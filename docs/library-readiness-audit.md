# Library-readiness audit

Audit date: 2026-08-04
Audited baseline: published v0.9.0 plus its tag-pinned downstream consumer and
the current v0.10.0-dev scheduler checkpoint

## Verdict

ProofNet-IR v0.9.0 is a usable, independently consumable Lean research library
and reference checker for its documented unit-free, cut-free MLL certificate
model. It is not a general Lean/mathlib proof assistant or a library for all
proof-net logics. The exact checker and automatic sequentializer are sound and
complete for the stated model; the dataset and focused-search baseline can be
reproduced. v0.5.0 proves that any accepted
certificate can be converted into a concrete first-order derivation whose
desequentialization is `ProofNetEquivalent` to the input. It also
lets a downstream consumer parse v0.2/v0.3 JSON directly into a checked Lean
object and migrate v0.2 to a reindex-invariant v0.3 key, but that closes only
part of the engineering and proof-identity gap.

## What is logically established

- involutive linear negation;
- proposition-level local link/resource semantics equivalent to the Boolean
  structural checker;
- exact enumeration of one-edge-per-par switchings;
- checker soundness for independent unbounded walk semantics;
- checker soundness and completeness for the independent fuel-indexed path
  semantics;
- after v0.2.0, loop erasure and finite vertex counting prove completeness for
  the standard unbounded walk semantics as well
  (`check_iff_declarativelyCorrect`);
- exhaustive differential agreement for all 33,868 simple graphs through six
  vertices and two separate 1,000-certificate corpora;
- exact reconstruction for the recursive identity family;
- after v0.2.0, successful first-order derivation inference denotes a genuine
  kernel-typed `Derivation` (`CutFreeDerivation.infer?_sound`).
- `CutFreeDerivation.elaborate?` returns only when the inferred sequent has a
  kernel-typed derivation, the certificate boundary labels are that same
  sequent, and the reference checker accepted the certificate.
- the post-release parser accepts the canonical serializer for all 250
  generated derivation-tree fixtures and returns the normalized certificate.
- after v0.2.0, bounded vertex reindexing is lossless and forms an explicit
  equivalence relation; structural validation, graph/tree semantics, switching
  correctness, and the final checker are invariant under it.
- v0.3 proves that every `ReindexEquivalent` certificate has the same
  `reindex-v1` serialized key; 250 generated certificates round-trip through
  the native checked parser and an independent audit exercises all 1,000
  committed records under deterministic vertex permutations.
- v0.3.1 proves structural well-formedness gives a complete traversal,
  normalization is an in-class representative, and normal-form equality is an
  iff/decision procedure for the exact order-preserving reindex relation.
- v0.4.0 defines a broader `ProofNetEquivalent` relation generated
  by bounded reindexing and link-list permutation. Lean proves that link
  permutation preserves all structural conditions, transports every par
  switching to a tree-equivalent graph, and preserves declarative correctness,
  `Correct`, and the Boolean checker.
- v0.4.0 implements checker-gated terminal-par and splitting-tensor
  inverse candidates, with 250 generated nets exposing an accepted recursive
  step; the supporting vertex-deletion graph layer now proves the complete
  theorem that deleting a leaf preserves `IsTree`. Terminal-par preservation is
  complete, and a genuine splitting tensor now produces two universally
  structurally well-formed components whose every switching is an induced
  input restriction and remains an `IsTree`. Checker/declarative preservation
  for this reduction is complete. Universal terminal-par-or-splitting-tensor
  existence, strict decrease of both reductions, and the axiom-only recursive
  base are now kernel checked. Boundary transport and well-founded logical
  recursion are also complete. Exact par/tensor occurrence reconstruction and
  inverse-rule congruence now close `sequentialization_of_check` and
  `generallySequentializable`: every accepted certificate has a concrete
  first-order tree whose executable desequentialization is
  `ProofNetEquivalent` to the input and has exactly its ordered conclusion
  formulas.
- the post-v0.4 `Certificate.sequentialize_complete` theorem closes the
  separate runtime path: finite terminal-par/splitting-tensor search, complete
  repeated-label boundary alignment, and fuel-bounded recursion return a
  proof-bearing result for every checker-accepted certificate.
- current v0.10 development has a separate bounded/tagged `NEXTAXIOM`
  checkpoint. Its reusable source-incidence index has kernel-proved exact
  submitted-link origin. This `SourceIndex.Sound` fact alone is only
  provenance: both endpoints of a malformed self-axiom enter the same bucket,
  while structural well-formedness now proves a singleton source lookup at
  every in-bounds occurrence. Every successful search retains the exact
  submitted axiom index/endpoints, final tags, and trace, and proves tag-array
  size preservation, monotonicity of old true tags, trace `Nodup`,
  input-false/output-true tagging of the trace and endpoints, input-unmarked
  endpoints, and `trace.length ≤ fuel`. Successive touched carriers are
  disjoint when the second call uses exactly `first.tags`; this is the precise
  scope of the global no-revisit discipline, and the theorem does not cover
  reset tags. The separate oriented-route theorem proves the trace follows
  exact submitted source-left steps to the endpoint actually reached and does
  not confuse that endpoint with the axiom's stored left endpoint.
  `SearchClearThrough` then gives local totality under rank-scoped
  untagged/unassigned freshness and fuel greater than the start complexity;
  full initial-carrier freshness yields the exact `complexity + 1` budget.
  This is not totality of the carrier-size wrapper or of later Figure-7
  scheduler calls. Its dynamic start refines an immediate eager Figure-5 step
  under `OrderedParents`, not the delayed Figures 7–8 `init`/`new` transition.
  Tests exercise expected tags/trace, zero fuel, out-of-bounds, tagged and
  marked starts, missing and non-unique sources, threaded-result-tags repeat
  rejection, stored-right orientation, every canonical initial start under
  its rank budget, a depth-two exact rank-versus-`rank + 1` fuel boundary, and
  dynamic token allocation.
- current v0.10 development also has an independent delayed scheduler-state
  checkpoint. `RawTokenAge` is a discovery-order age, not a union-find
  representative. `SigmaAgePartition` proves strictly increasing `σ`
  boundaries below the raw-age horizon, and executable lookup returns the
  greatest eligible boundary. `WaitingCell` distinguishes an out-of-bounds
  lookup, in-bounds undefined `⊥`, and initialized empty `∅`. Strict empty
  `init` reserves age zero, keeps `W(0)` undefined, preserves marks, and queues
  `[reached, partner]`. Guerrini's 1999 prose defines `W` at the inactive
  `σ` boundaries, and `unify` reads the old predecessor; the printed Figure-7
  `new` instead writes the fresh top. `newEnqueue?` retains that literal
  fresh-cell update only for source audit. The production
  `operationalNewEnqueue?` initializes the old active boundary and leaves the
  fresh top undefined. The kernel-checked `OperationalWaitingDomain` says that
  allocated initialized cells are exactly `sigma.dropLast`; `init` establishes
  it and operational `new` preserves it. This is the project's operational
  interpretation, not an author-confirmed erratum or uniqueness claim.
  `SequentialSchedulerBridge.lean` uses the operational update and reserves a
  locally well-formed submitted axiom as an unmarked live component with a
  fresh self-parent. `RealizesSigma` covers raw marks, horizon, and executable
  boundary lookup; the same route-bound result exposes production submitted
  orientation separately from delayed reached/partner order. Typed
  initial/later wrappers thread the complete tag array and preserve
  `ReservationInvariant`, including `OperationalWaitingDomain`.
  `SequentialFigure7History.lean` now separately characterizes exact
  empty/init/operational-new executions and proves tags iff recorded touch,
  whole-history submitted-slot non-reuse, and reservation-count alignment.
  The preservation record alone still does not exclude reset tags, and the
  history result covers neither the implemented local non-reserving rules nor
  the remaining unimplemented rules.

## Logical gaps blocking a mature-library claim

1. Formula inference and occurrence-aware construction have a proved exact
   success-domain/boundary equivalence, including duplicate-label exchanges.
   Structural composition and all-switchings tree composition now prove every
   successful construction declaratively correct and checker-accepted;
   `desequentializeChecked?` and `elaborate?` are proved total on `infer?`
   success. The remaining logical scope gaps are units, cuts, additives,
   exponentials, and integration with the initial persistent LeanProp bridge.
   The bridge now has separate persistent/linear contexts, explicit persistent
   structural rules, ordinary Lean connective/quantifier nodes, an axiom-free
   proof-term interpreter, and an exact linear-leaf count theorem. It remains
   separate from MLL certificate semantics and lacks release-level
   qualification. A deterministic 600-template positive schema corpus,
   universal atom-valuation soundness theorem, unindexed raw checker, positive
   erasure/recovery theorem, strict versioned JSON/checker-gated parser, and
   1,000 malformed cases with exact raw/wire diagnostic expectations are now
   present. A typed structural normalizer recursively removes immediate
   persistent contraction-over-weakening redexes and has proved reducedness,
   fixed-point, idempotence, size, linear-count, and pointwise interpretation
   laws. It is noncomputable and does not normalize raw wire schemas. Equality
   and quantifier terms remain outside the wire fragment.
2. The stronger `GenerallySequentializable` result and the public executable
   totality theorem are complete for the
   documented unit-free, cut-free MLL representation. Remaining logical scope
   gaps concern unsupported connectives/units/cuts and broader notions of
   canonical graph identity, not the accepted-net reverse theorem.
3. `Graph.Acyclic` is now exposed as absence of an exact stored-edge
   `EdgeSimpleCycle`, and `Graph.IsTree.acyclic` proves the sound direction
   against that occurrence-aware semantics. Exact directed edges, walks,
   simple cycles, and acyclicity now transport through bounded bijective
   vertex renamings, with `acyclic_reindex_iff` exposed publicly. The converse
   finite-multigraph forest-count theorem is now kernel checked without
   assuming the edge-count equation: a canonical shortest-parent spanning
   tree and exact extra-edge cycle construction establish
   `IsTree ↔ Bounded ∧ Connected ∧ Acyclic`. The exhaustive executable
   `isAcyclic` is now proved equivalent to this exact acyclicity semantics,
   and the derived `isTreeViaAcyclic` is proved Boolean-equal to the existing
   tree checker. This closes the reference-decision gap but not the
   non-enumerative performance gap.
   The colored criterion now additionally has an exact semantic acyclicity
   converse: structural well-formedness proves
   `CuspAcyclic ↔ every occurrence-order switching is Acyclic`, with retained
   cycles lifted by exact edge occurrence rather than endpoint value. A
   maximal-forest theorem now completes the connectedness half and reduces
   all switching connectedness to one deterministic reference graph. Thus
   `check = true` is equivalent to structural well-formedness,
   `CuspAcyclic`, and `ReferenceSwitchingConnected`. The executable
   `compactCheck` evaluates these three fields without enumerating switching
   graphs and is proved Boolean-equal to `check`; its exhaustive
   colored-cycle phase remains a specification oracle rather than the
   scalable implementation.
   The v0.9 API additionally provides
   `Certificate.verifyDerivation?`, which avoids both input-switching
   enumeration and vertex-permutation search when a caller supplies a
   derivation. Its soundness and relative completeness are kernel checked.
   The automatic `Certificate.reconstructDerivation?` layer now decides a
   bare certificate without calling the all-switchings checker. Lean proves
   universal success on reference-accepted inputs and exact Boolean equality
   with `Certificate.check`. A structure-guided fast path now defers
   verification until the complete tree and greedily aligns repeated boundary
   occurrences by formula-tree/axiom profiles; the proved exhaustive path
   remains its fallback. Runtime equality is CI-gated on the frozen 1,000-case
   250-positive/750-negative corpus. A separate 18-case adversarial suite
   covers skewed, balanced tensor, balanced par, alternating, repeated-internal
   labels, repeated boundary labels, and reversed link storage through 126
   formula occurrences and 22 conclusions. The
   remaining gap is a proved worst-case complexity/resource bound: fallback
   backtracking and repeated-label enumeration are not yet polynomially
   bounded.
   The v0.9 `Certificate.unificationFastCheck` layer now executes the
   Guerrini Figure-5 token rules while constructing a derivation and is proved
   sound through independent verification. `Certificate.unificationCheck`
   combines it with the complete checker-free reconstruction fallback and is
   proved exactly equal to `check`. The clean consumer compiles and executes
   both APIs. The pure fast path is not yet proved complete; the hybrid's
   fallback means this is not yet a linear-time production contract. The
   statistics-bearing API now gives callers proof-relevant scan receipts:
   at most `|links|` passes and `|links|²` link visits. The deliberately scoped
   theorem does not bound the complete verifier.
   An additional event-driven worklist precomputes premise consumers and
   retries only waiting par links after a tensor union. Its verified success
   is sound, its fallback wrapper is exactly equal to `check`, and every run
   is capped at `n(n+4)+1` link attempts. Current `main` proves that this fuel
   exhausts the canonical production queue and classifies every remaining
   unfired connective by an exact idle/waiting/deadlock witness. A
   least-formula-complexity theorem now eliminates idle premises from the
   incomplete case, leaving an exact submitted distinct-thread waiting par or
   same-thread tensor deadlock. A kernel-checked active-reference connectivity
   invariant plus declarative switching acyclicity now excludes the tensor
   branch on correct inputs. A converse retained-edge invariant and causal
   marking closure now prove that active-reference connectivity is exactly
   union-find thread equality on reachable markings. The sole remaining
   obstruction is now path-exposed: an exact reference simple path joins the
   waiting par premises while avoiding its conclusion, and distinct active
   components force an unmarked internal occurrence on that path. Current
   development further exposes the first exact traversed reference-edge
   occurrence directed from a marked source into an unmarked target, retains
   an entirely active prefix, and proves that its source carries the waiting
   par's left token. A reverse-path theorem selects the last inactive
   frontier, proves that its marked target carries the waiting par's right
   token, and gives an exact ordered decomposition with two distinct boundary
   occurrences. It then classifies both frontiers
   occurrence-exactly as a forward premise-to-conclusion edge of a concrete
   submitted par or tensor. Quiescent scheduler coverage now gives the exact
   residual cases: an omitted/unassigned par premise, a registered
   distinct-token par, or an opposite/unassigned tensor premise.
   A first-reentry suffix cut narrows the remaining geometry to a contiguous
   inactive block:
   every intervening traversed occurrence has two unmarked endpoints and both
   boundary orientations retain their exact scheduler classifications.
   Every terminating formula chase now also retains a composable sequence of
   exact source-connective/premise steps. Iteration on the finite formula
   carrier yields a concrete nonempty closed waiting-dependency segment with
   every structural chase preserved. Each descent step is now lifted to the
   exact full occurrence-graph backward edge; a nontrivial chase is a
   vertex-simple, internally cusp-free path, and state-indexed evidence keeps
   every visited formula occurrence unassigned. The occurrence-exact
   scheduler frontier cannot be immediately reversed by the first tail edge.
   The deterministic mask is now classified at the exact lifted index;
   structural typing and unique producer ownership then prove every
   nontrivial turn is a par cusp or tensor-colored free turn. Every dependency
   now carries an exact composable complete-graph segment from source waiting
   conclusion to target; concatenating the selected finite family yields a
   genuinely nonempty closed occurrence-aware `fullGraph` walk. Exact
   occurrence cancellation, residual-core analysis, and simultaneous
   switching flips reduce every correct fully reflexive dependency cycle to a
   terminal forward retained-left par cusp with a complete
   state-and-interval-cut trace. Every backward cut is now bound to the exact
   positioned obstruction that generated it. The terminal step likewise binds
   its indexed generator, arc, exact complementary interval, derived strict
   cut, closed walk, reverse-shell normalization, and nested trace. The
   complement is nonempty, closed,
   internally cusp-free, and strictly shorter. Proof-relevant cyclic
   normalization now strips only exact first/last reverse shells, retains the
   full positional context and length equation, and transports scheduler
   provenance to the residual core. If that core is nonempty and closes
   cusp-free, the same construction yields a strictly nested terminal cusp;
   well-founded descent therefore terminates at either an empty shell core or
   a scheduler-located nontrivial closing-par core. The terminal complement,
   reverse shells, normalized cores, and recursively exposed cusps carry exact
   scheduler tags through one composed descent from the original family. The
   terminal path derives its cut from the same indexed terminal witness instead
   of invoking the first generic `CyclicIntervalCut` positional lift. The
   terminal base retains its complement walk and cusp-freedom.
   In the empty-core branch, every exact visit has a distinct reverse partner
   from another scheduler step, every edge is reference-kept, the nonempty
   complement transports to the reference-switching tree, and no visit is a
   flipped-segment head. One concrete reverse pair is additionally ordered by
   scheduler step with an exact before/middle/after family decomposition, and
   each positive offset is inverted to its omitted-head/retained-suffix
   decomposition plus the exact suffix walk. Lean now also exhibits the
   zero-offset heads of both ordered endpoint segments as exact members of the
   initial tagged family and exact nonmembers of the retained complement. Each
   endpoint additionally carries its exact scheduler source, complete
   reference-kept suffix walk to the next scheduler conclusion, and the exact
   retained-left target occurrence avoided by the whole segment. The terminal
   outcome is now consumed by the global fully reflexive dependency-cycle
   extraction. Exact mask transport proves that the selected compacted suffix
   occurrences remain a reverse pair. The empty shell additionally splits
   into two nonempty compacted reference walks through one midpoint, and its
   full closing traversal is kernel-proved equal to the reverse of its full
   opening traversal. This head-skipping chord plus occurrence-exact shell
   identifies an unavoidable midpoint occurrence/reverse cusp, so the
   cusp-free empty branch is now kernel-excluded without assuming the false
   transitivity of generic cyclic-interval convexity. The tagged closing-par
   base now retains exact first/last scheduler tags, source segment/offset
   lookups, and reference retention of its forward last incidence. The same
   dependent package now binds those tags to the par link, normalization core,
   closed walk, and exact `first :: middle ++ [last]` tagged split; Lean proves
   its artificial seam is not an original same-segment or segment-boundary
   coordinate adjacency. Backward-search ancestry and the terminal-complement
   step now carry generator-exact indexed witnesses. The terminal base,
   data-indexed global ancestry, closing outcome, and normalized endpoint split
   are also assembled into one exact package: the first three share
   `(base, complementBase, taggedComplement, taggedNormalized)`, and the split
   shares that `taggedNormalized`. The full terminal `StepAt` frame remains
   existential inside the step wrapper rather than a global package index, but
   the structural replay opens that wrapper exactly once and reuses the same
   frame. It now enriches the older boundary cursor with an
   occurrence-position endpoint zipper whose gap is the complete complementary
   arc between the fixed tagged endpoints. These two gap notions are not
   equated.

   Every indexed flipped segment is nonempty. Hence an empty exact zipper gap
   in the initial tagged scheduler family would force the coordinate adjacency
   already excluded by the endpoint witness, and the exact gap is nonempty.
   The canonical endpoint replay of the fixed terminal step now always
   first-opens before ancestry: a nonempty reverse shell opens in the first
   frame; otherwise the generator's nonempty omitted arc opens in the second.
   It retains
   `closing.map erase = reverseTraversal (opening.map erase)`, the
   omitted-right zero-offset backward anchor, the forward retained-left last
   occurrence of the outer terminal arc, and the exact base gap
   `closing ++ taggedArc ++ opening`.

   Erasing the outer `taggedArc` produces a closed `EdgeWalk` at the complement
   base and satisfies `CuspFreeTraversal` internally; the exact cyclic closing
   pair from its outer last occurrence to the anchor is a cusp, and those
   directed occurrences are not reverses. The first-opening proof is built by
   an internal shell-nonempty/empty split, but its returned proposition does
   not expose a separately consumable frame/origin branch tying the opening to
   the anchor.

   Endpoint-gap sublist preservation carries the entire outer `taggedArc` in
   its original linear order through exact ancestry into the initial
   scheduler-family gap, retaining its same omitted-right head and
   retained-left last occurrence. A generic head/getLast-plus-sublist theorem
   now exhibits that gap as
   `g0 ++ anchor :: g1 ++ outerLast :: g2`; composing the decomposition with
   the zipper rotation yields
   `CyclicFourPointDisplayAt firstTag lastTag anchor outerLast`. The generic
   relation permits empty intervals and repeated values, so it is not the
   missing strict scheduler-rank theorem. The ordered sublist need not be
   contiguous, and the four-point display establishes no fixed linear rank,
   crossing, cyclic betweenness, or scheduler-order/proper-nesting contradiction.
   In the complete initial `tagSchedulerFamily`, its ambient exact-coordinate
   `Nodup` now implies
   `[firstTag, lastTag, anchor, outerLast].Nodup`. This is a theorem about the
   four `SchedulerOccurrence` tags only; erased edges, edge endpoints, and
   vertices may repeat. The endpoint replay preserves the same exact outer
   positioned choice, and exact ancestry membership lifts both that outer
   witness and the inner normalized closing witness to the full initial family.
   A specialized theorem returns those two witnesses together with the display
   and four-tag `Nodup`. Its order
   `firstTag → lastTag → anchor → outerLast` separates rather than crosses the
   endpoint pairs. No interval nonemptiness, contiguity, fixed or modular rank,
   or model-specific scheduler-order contradiction is proved; planarity is not
   assumed. Ordinary laminarity permits these separated pairs as siblings.
   A stable small accepted three-axiom/two-tensor regression also starts token
   ages 0, 1, and 2 and first merges ages 0 and 2 under the current reverse
   connective queue. The worklist succeeds in two attempts, zero waiting
   requeues, and two firings. The counters do not expose internal class
   membership; that noncontiguous merge follows from the fixed links and
   eager-start/reverse-queue definitions. Therefore contiguous age intervals
   and Figure-7 LIFO are not invariants of the current flat scheduler, and
   `tagSchedulerFamily.step` must be read as a dependency-segment index rather
   than firing age.
   Exact concrete-state confluence is refuted by a derivation-generated
   correct certificate, and structural-only confluence is refuted by a
   structurally well-formed certificate. Flat-worklist completeness may instead
   require preservation of the residual parsing witness or a theorem modulo
   the candidate marked-domain plus occurrence-thread-partition quotient. No
   committed reproducible audit or kernel theorem currently establishes
   confluence or completeness at that quotient.
   The separate bounded/tagged `NEXTAXIOM` and dynamic-start primitive is
   kernel checked, including per-call trace/tag invariants, oriented route
   correctness, initial/local rank-scoped totality, and touched-set
   disjointness for successive calls that strictly thread `first.tags`; reset
   tags are outside that theorem. The separate raw-age state checkpoint proves
   the initial `σ`/waiting representation, the literal printed `new` audit
   helper, and the separate production update that preserves
   `OperationalWaitingDomain`. Initial and later reservations, submitted/search
   orientation separation, the narrow `RealizesSigma` relation, and the local
   pop/mark/mate-search/new pipeline are kernel checked under the supplied
   invariant. Exact init/new execution history, tag provenance, global
   submitted-slot non-reuse, and reservation-count alignment are also kernel
   checked. Exact local `concl`, `nop`, `wait`, and successful `forward` rules
   now preserve the reservation invariant, with conclusion lookup requiring
   local `NodeWellFormed` ownership and distinguishing an empty bucket from
   ambiguous singleton-query failure. Independent Boolean-free direct
   relations, executable soundness, structurally valid completeness, and
   output uniqueness are kernel checked for the common prefix, `concl`, `nop`,
   `wait`, and `forward` under their documented hypotheses. `ForwardRule`
   states the exact non-strict raw-age paper guard and excludes every Figure-7
   executable/mutation wrapper; `ForwardExecutableReadyNodup` separately
   states the fail-closed list-shape refinement. The complete
   `SchedulerInvariant` derives that shape condition, giving a second direct
   executable iff. None of these local results establishes applicability,
   dispatcher reachability, or progress.
   The stronger current state-only `SchedulerInvariant` is now preserved by
   the synchronized prepared pop/raw-mark prefix and therefore by exact and
   executable `concl`/`nop`. This includes extensional active ready/frontier
   transport, combined ready/waiting queue uniqueness, waiting-span transport,
   causal produced-premise marking, pending-premise coverage for the newly
   marked selected occurrence, and unchanged live-component counter/domain
   facts. The separate proof-only `SequentialComponentProvenance` module now
   records exact submitted link indices, exact formula vertices and focus
   positions, locally duplicate-free component ownership, and cross-slot
   disjoint forest accounting. Marked owned vertices resolve to the exact live
   representative slot, unmarked owned vertices remain on the same frontier,
   and every concrete raw mark is conversely owned at its representative.
   The layer proves formula-consistency soundness, exact axiom-reservation
   provenance, and local par/tensor queue provenance extension; a
   repeated-label fixture rejects a component that the older formula-only
   predicate accepts. Separate closed fixtures reject a marked occurrence
   assigned to the wrong representative slot and an ownerless raw mark. The
   forest predicate is now integrated into `SchedulerInvariant`, established
   by empty/init, and preserved by the common prepared raw-mark prefix; exact
   and executable `concl`/`nop` inherit that result. Successful deterministic
   `NewStep` and successful executable `new?` now preserve the complete current
   occurrence-exact state-only invariant too, including exact fresh-axiom
   forest extension, global queued-occurrence uniqueness/unmarkedness, causal
   production, waiting-span, pending-premise, and counter fields. This is
   preservation conditional on a successful step, not proof of later `new?`
   success, totality, or reachability. Successful deterministic/executable
   `wait` now preserves the same complete state-only invariant. The proof locks
   the exact submitted par position in the source index, preserves combined
   queue `Nodup` and raw-unmarkedness, and adds one strict older/younger waiting
   span while leaving the component forest and firing counter unchanged.
   The local `wait` destination is exactly
   `sigmaBoundary? stack.sigma mateRawAge`, and its initialized-cell cons
   update has those state-only ownership guarantees only under the supplied
   `SchedulerInvariant`. Successful typed `ForwardStep` and executable
   `forward?` now require the paper guard
   `selectedRawAge ≤ mateRawAge`; a separate theorem regression proves the
   distinct-age boundary case `sigmaBoundary? [0] 1 = some 0`. It queues the
   exact submitted par and preserves the complete
   occurrence-exact `SchedulerInvariant`. The proof retains the exact submitted
   par position, component forest and live frontier, ready/waiting queue facts,
   waiting spans, pending-premise coverage, and exact fired-connective counter.
   The extra active-ready `Nodup` guard is only a fail-closed shape check. A
   typed `init → nop → forward → concl` regression exercises the path.
   A bounded empty-cell `UnifyEmpty` executable/direct-relation slice now
   retains the exact submitted tensor occurrence and raw-age guard
   `j ≤ μ(mate) < i`. Soundness assumes `ReservationInvariant`; completeness
   and iff additionally assume structural validity plus the separate ready-list
   `Nodup` premise. Every successful execution preserves
   `ReservationInvariant`, including exact `RealizesSigma` transport through
   the stack pop and parent union. Given the full state-only invariant, every
   successful typed and executable bounded step also preserves the complete
   occurrence-exact `SchedulerInvariant`, including the component forest,
   live-frontier/queue/waiting/pending fields, and fired counter. The
   strict-singleton `UnifyOne` slice now accepts exactly `W(j) = [c]`, obtains
   `c`'s exact submitted par producer slot from the singleton occurrence-source
   bucket, and atomically performs prepare, tensor union, one par activation,
   and scheduler drain. Its high-level-executable-independent direct relation has exact
   typed/executable correspondence and output uniqueness; successful steps
   preserve both `ReservationInvariant` and the complete occurrence-exact
   `SchedulerInvariant`, with an exact connective-counter increase of two.
   Empty and length-at-least-two payloads fail closed. Explicitly constructing
   the waiting par is the project's derivation/provenance representation
   refinement of the paper's set-to-ready move, not a claim that the paper
   specifies that construction. A separate local head-to-tail production-core
   fold has direct/typed/executable correspondence, output uniqueness, the
   documented core-field preservation, and exact `+ payload.length` counter
   accounting. `SequentialFigure7UnifyPayload.lean` now atomically composes
   one exact tensor, that stored-order fold, and the two-level drain. Its
   high-level-executable-independent direct relation, typed witness, and
   executable have exact
   correspondence and output uniqueness under their documented structural,
   `ReservationInvariant`, and final-ready `Nodup` premises. Successful steps
   preserve `ReservationInvariant`, and the exact state theorem accounts for
   `1 + payload.length`. The follow-on
   `SequentialFigure7UnifyPayloadInvariant.lean` proves complete
   occurrence-forest/`SchedulerInvariant` transport for every successful typed
   or executable step from a full input invariant. Its transient fixed-final-
   stack gap derives pre-activation freshness and exact producer/boundary facts
   from that input, establishes ownership head by head, and closes after the
   last activation. The separate input-only `UnifyPayloadEnabled` layer proves
   executable applicability and invariant-preserving output from that predicate
   plus the full invariant; the invariant alone does not imply enabledness, and
   physical tensor/fold intermediates are not assigned the invariant.
   `SequentialFigure7StableEnabled.lean` now provides the corresponding pure
   input predicates for `concl`, `nop`, `wait`, and `forward`. Their field
   inventory contains no result state or executor equation; the full invariant
   derives the prepare state, wait destination/payload, and forward
   token/component/pick/`Nodup` obligations. Each predicate yields executor
   success and a full-invariant output. An already supplied ready head and exact
   submitted par is classified as `nop`, `wait`, or `forward`, but this scoped
   theorem excludes conclusion, tensor/`new`, unification, completed buckets,
   priority, and global scheduler enabledness. The new occurrence-exact
   coverage theorems close only that structural gap for an already supplied
   ready head: the head falls into a conclusion, submitted-par-consumer, or
   submitted-tensor-consumer case, and the refined theorem returns one of four
   stable enabled alternatives or an exact unmarked/marked tensor alternative.
   This is inclusive exhaustive coverage, not pairwise disjointness or unique
   branch selection. The bare unmarked tensor alternative still does not imply
   `NewEnabled`; the local source-region record additionally names an exact
   route, endpoint queue separation, and strict fresh capacity. Canonical
   history now derives the latter two categories once the exact run is supplied.
   The marked alternative
   now implies `UnifyPayloadEnabled` only
   when the separate input-only sigma-predecessor/boundary witness is supplied;
   the occurrence-level case theorem alone does not derive that witness. A
   checker-rejected one-axiom/one-tensor fixture compile-locks the stronger
   boundary: full state-only `SchedulerInvariant`, singleton sigma, an exact
   ready tensor, and a marked mate can coexist while
   `UnifyPayloadEnabled` is false. This is not a correct-certificate or
   canonical-dispatcher reachability counterexample. The fixed initialization
   uses `native_decide`, so the private fixture is executable regression
   evidence outside the audited public theorem boundary.
   `SequentialFigure7Dispatcher.lean` now supplies one canonical executable
   entry point for `concl`/`nop`/`new`/`wait`/`forward`/`unifyPayload`, exact
   priority-aware dependent witnesses, output uniqueness, full successful-step
   invariant transport, and a certified proof-carrying history. The specialized
   empty/singleton unifiers are compatibility APIs, not duplicate branch tags.
   The history requires the invariant at every later edge; it does not prove
   exhaustive branch applicability, totality, or progress.
   `SequentialFigure7ProgressInvariant.lean` separately proves
   `FutureWaitingUndefined` for exact empty/initial states and preserves it
   through every successful rule, dispatch, certified history, and dispatcher
   reachability. It constrains only unused in-bounds waiting storage. A private
   native-computed forged-future-cell regression retains the full state
   invariant, an exact unmarked tensor guard, and `FreshSourceLeftRun` while
   `NewEnabled` fails; it is explicitly not a reachable-state theorem. This
   closes the storage-preservation sub-obligation. The source-region bridge
   identifies exactly two endpoint queue-absence obligations and strict fresh
   capacity beyond the exact run. The new fresh-capacity and endpoint-specific
   queue-history theorems derive all three from structural well-formedness,
   canonical history, the complete invariant, and that exact run. The later
   active-region layer now derives the run/route, and therefore `NewEnabled`,
   for every supplied correct canonical-history `NewGuard`. It does not prove
   that every nonterminal state presents such a guard. Tensor-branch
   exhaustiveness, dispatcher progress, and worklist completeness remain open.
   `SequentialFigure7ReadyHeadDispatchResidual.lean` now combines these local
   results for every supplied correct canonical-history `ReadyHeadInput`. It
   returns an inclusive `PriorityEnabled`-or-marked-tensor-gap disjunction; the
   reachable wrapper turns the positive side into an exact dispatcher result.
   The residual is already narrowed to a strictly older retained mate boundary
   that is not known to be the active top's immediate predecessor. This is not
   an exclusive classification, a proof that the gap is unreachable, or a
   theorem that every semantic nonterminal state supplies a ready head. The new
   predecessor invariant now quantifies over every ready or waiting future-work
   occurrence, holds for empty and initial-reservation states, and is preserved
   through Prepared, `concl`, `nop`, canonical `new`, and canonical successful
   `wait`, `forward`, and `unifyPayload`. The Wait theorem transports retained
   work through the
   prepared and destination updates and discharges the inserted conclusion. A
   source-visible conditional bridge packages the exact predecessor only after
   callers supply strict older-event separation and a child-event anchor; the
   bridge proves neither those premises nor branch applicability or progress.
   The Forward theorem supplies those bridge premises from private
   transition-specific geometry for an already-successful typed step and also
   requires declarative correctness, the complete scheduler invariant,
   canonical history, a `ForwardStep`, and the prior predecessor invariant. The
   Unify theorem exposes a carrier-free raw touch result for the inserted
   conclusion, transports retained evidence across the final sigma pop, rules
   out moved active work by strict output order, and sends created work through
   final component provenance plus the conditional child-anchor bridge. It
   consumes an already-successful typed Unify branch, declarative correctness,
   the complete scheduler invariant, canonical history, and the prior
   predecessor invariant; it does not derive any of them. The
   ready-head projection converts the residual's strictly older boundary into
   the exact immediate predecessor whenever the invariant is available.
   `SequentialFigure7OlderMarkedTensorPredecessorHistory.lean` now packages the
   closed prefix over complete canonical dispatcher histories and exposes it for
   every `ExecutedHistory` under declarative correctness. At a
   dispatcher-reachable state with an explicitly supplied `ReadyHeadInput`, the
   invariant eliminates the residual and yields one exact successful
   dispatcher result. This history wrapper does not construct that ready head;
   the following structural classifier identifies the exact shape when it is
   absent, and the following debt and continuation-exit layers give conditional
   completion reductions. The re-entry-target classifier now leaves selected-
   raw and concretely-marked no-tail alternatives as the first gate before
   dispatcher progress. Later-state totality, recursive-fallback removal,
   faithful token-age scheduling, whole-program linearity, and Figure-7
   pure-worklist completeness remain open maturity gates; no global raw seam or
   sequentialization result follows from this history package.
   `SequentialFigure7ActiveTopResidual.lean` now identifies the exact remaining
   state shape. Under a complete scheduler invariant and a started-state
   premise, no `ReadyHeadInput` exists exactly when the active live component
   has no raw-unmarked frontier occurrence. A correct dispatcher-reachable
   state therefore satisfies a disjunction between one exact dispatcher result
   and this `ActiveTopDrained` witness; exclusivity is not claimed. This closes
   the structural ready-head classification, but a drained active top alone is
   not identified with semantic completion.
   `SequentialFigure7ActiveTopMarkedNonconclusionDebt.lean` adds the exact
   conditional reduction. Its state predicate requires every marked
   nonconclusion on the active frontier to retain a raw-unmarked nonconclusion
   witness there. It holds for empty and initial-reservation states; New
   establishes it without an additional scheduler-invariant premise; Concl
   preserves a prior instance; and Forward/UnifyPayload establish it under the
   prior complete scheduler invariant when the created conclusion is not
   global. Declarative correctness, the complete scheduler invariant,
   `ActiveTopDrained`, and this debt imply
   `core.allMarked = true`.
   `SequentialFigure7ActiveTopDebtBranchResidual.lean` makes the four local
   obligations exact. Under prior debt, post-Nop and post-Wait debt are
   equivalent to the prepared selected-away witness. Under the prior complete
   invariant and a global created conclusion, Forward and UnifyPayload
   post-debt are equivalent to marked-nonconclusion presence implying a
   non-global vertex in the exact ready tail. Presence only detects vacuity.
   Canonical history supplies none of these debt witnesses, so progress,
   terminality, totality, and completeness remain open.
   `SequentialFigure7ActiveTopDebtQueueTail.lean` sharpens the Nop and Wait
   residuals further. Under the prior debt and input `SchedulerInvariant`, each
   post-step debt proposition is equivalent to the prepared `remainingTop`
   containing a non-global vertex. This is an exact normalization, not a proof
   that any correct, historical, or reachable state contains such a vertex.
   `SequentialFigure7ActiveTopDebtHistoryTail.lean` collects the exact current
   obligations in `CanonicalTagHistory.ActiveTopDebtTailLaw`. Concl, Nop, and
   Wait recurse; Nop and Wait additionally require their non-global
   `remainingTop` witness. New resets, while Forward and UnifyPayload reset recursion and
   retain only their exact current non-global-created or global-created-tail
   obligation. The law plus the matching canonical tag history implies endpoint
   debt. The law remains an explicit assumed carrier and is not derived from
   correctness, canonical history, or reachability. Consequently unconditional
   `allMarked`, progress, termination, totality, and completeness remain open.
   The later parent-escape reduction neither requires nor derives this law.
   `SequentialFigure7ActiveTopDebtParentEscape.lean` now gives that bounded
   reduction for an explicit ready head whose selected connective is a `par`.
   Declarative correctness plus `SchedulerInvariant` returns the active
   component occurrence/accounting receipt and either a non-global ready-tail
   witness or `ActiveCarrierParentEscape`. The escape records a concrete marked
   non-global frontier premise, distinct from the selected vertex, whose exact
   submitted connective parent conclusion is outside the active owned carrier.
   The theorem does not assert that the outcomes are exclusive. If the tail
   witness is denied, the
   failure-conditioned theorem forces the escape without claiming that escape
   is impossible. A supplied `CanonicalTagHistory` only authenticates the
   concrete mark as an earlier prepared-selection event; it is not a premise of
   the reduction. No `ActiveTopDebtTailLaw` is assumed or derived. No
   computational coexistence receipt is part of this public checkpoint. The
   downstream re-entry classifier identifies exact submitted-parent target
   status, and its stored-right no-tail specialization eliminates the selected
   target. Eliminating the concretely marked target is the next readiness gate.
   Progress, completion, termination, totality, and completeness remain open.
   `SequentialFigure7ActiveTopDebtParentEscapeTemporal.lean` sharpens that
   residual without closing it. Under the matching canonical history,
   correctness, scheduler invariant, exact active occurrence/accounting data,
   and no-tail escape, the source is classified as par or tensor. The par
   branch returns an authentic reservation anchor and a raw-sibling or strictly
   older parent continuation. In the tensor branch, the escaped mark resolves
   to the active boundary while its sibling and parent lie outside the carrier;
   the branch also returns the already-proved older marked-tensor
   predecessor invariant. No branch supplies the missing ready-tail vertex or
   proves its residual impossible. The tail law, global-created alternatives,
   progress, completion, termination, totality, and completeness remain open.
   `SequentialFigure7ActiveTopDebtParentTemporalOutcome.lean` adds a common
   endpoint carrier for those two branches. Canonical continuation credit
   resolves the tensor residual to the same raw-sibling, older-future, or
   older-marked cases as par; future and marked parents remain outside the
   active carrier, while raw siblings are selected or external. The marked
   case is not declared terminal. This improves the induction interface but
   does not establish a ready-tail witness, `ActiveTopDebtTailLaw`, residual
   elimination, or progress.
   `SequentialFigure7ActiveTopDebtParentExternalTemporalOutcome.lean` now
   applies that interface to actual no-tail Nop and Wait steps. The Nop
   unmarked-mate guard and Wait strict mate-age order eliminate the selected raw
   endpoint. The resulting external-only carrier retains raw work outside the
   active owned carrier, older external future work, or an older external
   marked parent. It does not prove that any endpoint re-enters the active
   frontier, so the tail witness, history law, progress, completion,
   termination, totality, and completeness gates remain open.
   `SequentialFigure7ActiveTopDebtParentExternalCommitmentOutcome.lean`
   strengthens the older future and older marked branches with an exact
   retained `sigma` split. The final adjacent edge into the active top carries
   its canonical commitment reference path. The raw external branch stays
   unchanged. `SequentialFigure7ActiveTopDebtParentExternalEndpointCrossing.lean`
   now connects the active owned carrier to each exact older
   continuation endpoint and retains one stored owned-to-outside crossing.
   `SequentialFigure7ActiveTopDebtParentExternalCommitmentReentry.lean` now
   composes the complete retained commitment interval. Ready future and older
   marked endpoints receive an endpoint-to-active path and an exact
   outside-to-inside re-entry edge; waiting keeps its exact cell and raw work
   stays unchanged. The re-entry edge is not yet classified as a distinct
   ready-tail payer or eliminated under the no-tail hypothesis.
   `SequentialFigure7ActiveTopDebtParentExternalReentryTarget.lean` now
   identifies the edge as the reverse of an exact submitted connective-parent
   edge. Its target is a non-global active-frontier premise, and complete ready
   accounting classifies it as the selected raw head, a raw ready-tail
   occurrence, or a prior concrete mark. Explicit no-tail removes the middle
   case. Canonical raw-mark history authenticates the marked alternative at the
   active representative. If the retained path avoids the current par
   conclusion, parent-link uniqueness removes the selected alternative and
   leaves a distinct marked target. The checkpoint does not derive that path
   avoidance or turn the marked history into a distinct payer. Those are the
   next gates, followed by the global-created tail obligations.
   `SequentialFigure7ContinuationCredit.lean` and its preservation module now
   close a weaker full-history invariant. The two carriers assign each marked
   nonconclusion one of three receipts: an unmarked mate, future conclusion
   work, or a marked conclusion. Fresh events receive credit in all six cases.
   The six branch transports and two dispatcher transports require structural
   well-formedness; Nop and New additionally consume the old owner's mark, and
   dispatch-level old-credit transport supplies that mark uniformly. Exact
   `CanonicalTagHistory` preserves the state predicate without a correctness
   premise. None of the three receipt forms guarantees a distinct raw witness
   on the active frontier, so the selected-away and global-created exact-tail
   gates above remain open.
   `SequentialFigure7ContinuationExit.lean` now normalizes any such supplied
   continuation receipt through a finite chain of concretely marked non-global
   conclusions. Formula complexity strictly increases at every chain step, and
   the endpoint is an unmarked raw mate, scheduled future-conclusion work, or a
   concretely marked global conclusion. Under the complete scheduler invariant
   and a drained active top, the open endpoints become respectively a
   structurally non-global unmarked mate or an unmarked conclusion at a
   strictly older boundary.
   The separate `LocalizedContinuationExit` carrier binds only those two open
   endpoint forms to one component frontier and has no marked-global case.
   With structural well-formedness and queued vertices unmarked,
   `ActiveTopContinuationExitLocalized` implies active-top debt; with
   declarative correctness, the complete scheduler invariant, and
   `ActiveTopDrained` it implies `core.allMarked = true`. Both conditional
   reductions remain valid.
   `SequentialFigure7EndpointLocalityObstruction.lean` now proves that every
   successful typed `WaitStep` from a scheduler-invariant input refutes the
   unrestricted locality law at its output. It therefore cannot be promoted as
   a full canonical-history invariant across successful Wait transitions. This
   proves neither that the output is drained nor that a reachable Wait exists,
   and it does not refute direct debt or a Wait-compatible drained, temporal, or
   cross-component weakening. The concrete `native_decide` trace remains
   research-only and outside the public theorem. The reset-aware history-tail
   carrier records a Wait-compatible route, but does not establish its own
   history-level premise; unconditional progress, completion, termination,
   and totality still do not follow.
   `SequentialFigure7PriorityEnabled.lean` now gives that dispatcher an exact
   branch-indexed applicability correspondence whose six positive fields and
   stored earlier-branch negations are input-only. Each executor has an
   existential-success iff result under the complete invariant. The `new`
   field stores `NewEnabled`; operational `NewExecutableEnabled` remains only
   as an exact compatibility API.
   `SequentialFigure7NewInputCore.lean` adds the pure necessary projection,
   while `SequentialFigure7NewInputNecessary.lean` retains its historical
   import facade: the shallow guard plus exact fresh route, including whole-trace
   production readiness, is reconstructed from success, but the record itself
   omits recursive per-step tag-update equations and the later operational
   enqueue guard. Structural route reconstruction now recovers the exact run
   and terminal-partner exclusion. The projection therefore supplies no
   unconditional converse and is deliberately not named `NewEnabled`.
   Canonical queue/tag history supplies the missing region condition only in
   the stronger history-indexed setting, where Lean proves
   `NewEnabled ↔ NewInputNecessary` under the complete invariant.
   `SequentialFreshSourceLeftRun.lean` now supplies a separate exact
   proof-relevant source-left execution relation. It mirrors every executor
   branch and is equivalent in both directions to a named
   `nextAxiomWithFuel?` success, while retaining exact source buckets,
   submitted slots, recursive tag updates, fixed-state readiness, and terminal
   orientation. `SequentialFigure7NewEnabledCore.lean` combines that run with the
   shallow guard and exact enqueue guard. The resulting `NewEnabled` contains
   no executor equation/result, output, history, or reachability field and is
   equivalent to existential `new?` success under `SchedulerInvariant`, with
   an invariant-preserving output theorem. A queued-partner fixture confirms
   that the enqueue guard is essential. The lower-layer dependency split now
   lets the priority field use `NewEnabled` directly without changing the
   dispatcher. The historical `SequentialFigure7NewEnabled.lean` facade still
   re-exports the old direct-import priority surface, protected together with
   the narrow priority import by two default-build sentinels. This is a
   local applicability/classification theorem, not later-state totality or
   progress. `SequentialFigure7NewRegion.lean` further proves that every
   structurally well-formed route reconstructs the exact formula-bounded run.
   `NewSourceRegionInput` adds only two post-pop endpoint queue-absence facts
   and strict fresh waiting capacity; with `SchedulerInvariant` and
   `FutureWaitingUndefined`, it derives the enqueue guard and `NewEnabled`.
   `SequentialFigure7FreshCapacity.lean` derives capacity from a current-tag
   run and canonical reservation history. `SequentialFigure7QueueHistory.lean`
   tracks only exact axiom endpoints—never arbitrary queued conclusions—and
   derives both endpoint absences from canonical tag history. Certified
   dispatcher reachability therefore packages
   `NewEnabled ↔ NewInputNecessary` under structural well-formedness, while the
   exact route remains assumed.
   `SequentialFreshSourceBlocker.lean` now removes one ambiguity from that
   remaining route obligation. Under `StructurallyWellFormed` and an in-bounds
   start, the source-left search has either a formula-budget exact run or an
   inhabited blocker on a recursively visited stored-left occurrence or the
   terminal axiom partner. The blocker vocabulary is complete and deliberately
   narrow: only tag lookup different from `some false` or raw-mark lookup
   different from `some none`. Source shape, source singletonhood, and adequate
   fuel are discharged structurally. At this layer no theorem excludes blockers
   from correct canonical histories, and endpoint queue absence plus fresh
   capacity remain downstream of the positive run. The later active-region
   touch and raw-anchor theorems discharge both blocker classes for a supplied
   correct canonical-history active guard. This structural dichotomy alone
   still adds no reachability, totality, progress, fallback-removal, or
   complexity guarantee.
   `SequentialComponentSourceLeftGeometry.lean` adds the complementary
   structural carrier theorem. Starting from one occurrence owned by an exact
   `OccurrenceDerivation`, it keeps every recursively visited stored-left
   occurrence and the terminal axiom partner inside that same owned list. It
   does not identify a scheduler component, impose chronological separation,
   or establish reachability, enabledness, or progress.
   `SequentialFigure7BlockerHistory.lean` now makes the history side of that
   boundary exact. Given authentic canonical tag history, the complete
   invariant, and `NewGuard`, the base classifier gives a prior exact touch, the
   selected ready-head update, or an old raw-marked occurrence with an
   occurrence-exact live-component owner. Those three
   `CanonicalSourceLeftObstruction` alternatives may overlap, including in
   authentic correct canonical states; correctness does not make the
   prior-touch and old-owner classes globally disjoint. The terminal geometry
   below eliminates the selected-head alternative throughout the complete
   region under declarative correctness. A universal premise excluding the two
   remaining blocker forms from the particular current source-left carrier
   yields the exact run, `NewInputNecessary`, and `NewEnabled`. The new
   active-region touch-separation and enabledness layers now prove that local
   premise from declarative correctness, the complete invariant, canonical
   history, and the supplied active guard. Shallow-guard sufficiency is
   therefore closed at that history-indexed boundary. The result does not
   construct a guard or history and adds no dispatcher exhaustiveness,
   totality, progress, pure-worklist completeness, fallback-removal, or
   complexity guarantee. It records no new literature reading.
   The first obstruction-elimination slice is now proved. Exact source-left
   complexity descent and final-step decomposition show that a recursively
   visited route from the tensor mate cannot return to the selected ready head;
   the visited blocker classifier therefore contains only prior-touch or old
   exact-owner alternatives. The theorem is structural and non-circular, but
   it does not by itself apply to the terminal axiom partner. The new terminal
   geometry layer now constructs the exact all-left reference path and proves
   that `terminalPartner = head` would close an occurrence-aware cycle with
   the selected tensor's fixed edges. Reference-switching acyclicity, and hence
   declarative correctness, eliminates that final selected-head branch in both
   tensor orientations. A structurally well-formed switching-incorrect triangle
   remains the negative boundary showing the extra assumption is necessary.
   Prior-touch and old-owner blockers on the candidate current route remain the
   library-readiness gate; terminal-head separation no longer is one. They are
   not two globally disjoint state regions: one real correct canonical fixture
   has a vertex satisfying both, while an initialization fixture has touched
   vertices that remain unmarked and unowned by a marked-owner witness.
   `SequentialFigure7RegionBoundaries.lean` proves the exact conditional
   boundary instead: the carrier of an already supplied run is disjoint from
   prior touches, and the carrier of an already supplied marked-core run is
   disjoint from old exact marked owners. Because those statements take the run
   as input, they do not close the forward run-construction gate.
   `SequentialFigure7TouchOrigin.lean` now resolves the provenance shape of
   the first gate: every prior touch comes from one exact recorded init/new
   search and exposes its submitted axiom slot, oriented route, and complete
   historical source-left region. `SequentialFigure7ReservationLedger.lean`
   now assigns those authentic events their exact chronological raw-age index:
   the ledger projects to `List.range final.stack.nextAge`, exact age lookup succeeds,
   chronological link slots reverse the legacy newest-first list, and every
   touch reaches an event that itself touched the vertex. It also proves the
   selected old active age is strictly below a `new` event's fresh age. The
   new `SequentialFigure7CommitmentSpine.lean` layer proves that every adjacent
   pair retained in final `sigma` is backed by the exact `new` event at the
   child raw-age ledger slot. Stable branches preserve this ancestry, New
   appends one edge, and UnifyPayload removes only the active top edge. This
   does not construct a vertex-level reference path, prove target avoidance or
   queue origin, or discharge any raw created-candidate seam. The
   reservation/final-component transport is now complete in
   `SequentialFigure7ReservationRealization.lean`: under explicit certificate
   structural well-formedness, every event's exact axiom link survives all six
   dispatcher branches at its raw age's current
   representative, the event-owned list aligns with the final invariant forest,
   and both exact endpoints are accounted there. A checker-accepted real union
   merges raw ages zero and one into one final component while retaining both
   distinct event links. The remaining gate is now only the finer
   route/intersection geometry needed to construct the current run. Raw age is
   not a representative, reserved axiom endpoints are not the whole historical
   touch region, and historical event membership is not blanket current
   ownership.
   `SequentialFigure7RawMarkReservationAnchor.lean` now closes the local
   raw-mark-to-reservation anchor. From a concrete mark, canonical history and
   the complete state invariant recover the same-age ledger event, align the
   marked occurrence and both submitted-axiom endpoints in one final component
   and exact owned carrier, and construct owned-contained reference paths to
   both endpoints. This needs neither declarative correctness nor switching
   acyclicity. It does not compose paths between `sigma` components, prove
   target avoidance or queue origin, discharge a raw created-candidate seam, or
   establish progress.
   `SequentialFigure7CommitmentEdgeReferencePath.lean` now performs one exact
   cross-component composition for every adjacent parent-child pair retained in
   final `sigma`. It reconstructs the historical `new` step and composes the
   parent owned anchor, selected-head tensor/NEXTAXIOM segment, and child owned
   anchor into a canonical left-endpoint-to-left-endpoint simple path while
   retaining final accounting on both sides. This needs neither declarative
   correctness nor switching acyclicity, but it does not establish arbitrary
   target avoidance, whole-spine composition, queue origin, any raw seam,
   enabledness, progress, completeness, fallback removal, or complexity.
   `SequentialFigure7CommitmentEdgeTargetAvoidance.lean` now gives the exact
   conditional one-edge refinement. If the authentic child ledger event does
   not touch a supplied future candidate's tensor conclusion, Lean constructs
   the same canonical endpoint path while omitting that conclusion. The law is
   an explicit input rather than a history consequence; its global availability,
   arbitrary multi-edge composition, queue origin, the raw seams, enabledness,
   progress, completeness, fallback removal, and complexity remain open.
   `SequentialFigure7CommitmentIntervalTargetAvoidance.lean` now closes the
   composition operation for a supplied positive-length retained-`sigma`
   interval. Its callback must provide every adjacent avoiding witness. Exact
   middle ledger events are matched before verified loop erasure joins the
   paths. This does not derive or globalize the callback or child-event laws,
   cover a zero-edge singleton, recover queue origin, discharge a raw seam, or
   imply progress or complexity.
   `SequentialFigure7TouchCompleteness.lean` now proves the exact reverse
   structural direction for every authentic reservation event. Under
   `StructurallyWellFormed`, a vertex in the event's complete source-left region
   belongs to its reconstructed exact trace or is its terminal partner, hence
   is one of the event's stored touches. Combined with the existing forward
   theorem, event touch is equivalent to event-region membership. This requires
   the successful equation retained by `ReservationEvent`; it does not apply
   unchanged to an erased `ReservationSearchEvent`, establish current
   ownership or representative order, discharge a created-region premise, or
   prove progress.
   `SequentialFigure7OlderEventTouchSeparation.lean` now converts the complete
   cross-representative invariant to an exact event-touch form. Structural
   region disjointness always excludes event touches; the authentic-event
   reverse-completeness theorem recovers region disjointness under
   `StructurallyWellFormed`. The history-level iff preserves the old ledger,
   future-candidate, and current-representative quantifiers exactly. It is a
   normalization lemma, not unconditional history preservation or a discharge
   of the four created-candidate geometry premises.
   `PriorityEnabled` records the selected
   witness and all earlier negatives, is equivalent to the matching
   `DispatchStep`, characterizes exact selected-kind success and dispatcher
   failure, and has a unique selected kind. A completed reachable `[[]]`
   regression proves that the full invariant need not enable any branch, so
   these theorems do not establish intended-state exhaustiveness,
   nonterminality, global progress, or worklist completeness.
   `SequentialFigure7CrossRepresentativeWaitPreservation.lean` now closes the
   exact state-transport portion of the Wait branch. Every output future-work
   occurrence is retained middle-state work or the exact inserted conclusion;
   only the latter needs new geometry. The exported preservation theorem is
   deliberately conditional on `WaitCreatedRegionSeparated`, a non-circular
   prior-ledger/source-region obligation. The current scheduler invariant does
   not yet imply that premise, so unconditional Wait preservation remains an
   open maturity gate.
   `SequentialFigure7CrossRepresentativeNewPreservation.lean` now closes the
   exact state-transport and fresh-event portions of the New branch. Every
   output occurrence is retained marked-middle work or one of the exact
   reached/partner endpoints at the fresh boundary. The fresh reservation
   event is not strictly older than any output candidate. The exported history
   theorem remains conditional on `NewCreatedRegionSeparated` for prior events
   against actual endpoint candidates; the current invariant does not derive
   that geometry, so unconditional New preservation remains open.
   `SequentialFigure7OlderEventFutureWorkTouchNewPreservation.lean` separately
   closes New preservation for the queued-head invariant. From an
   already-successful typed step, a supplied prior canonical history, and its
   `OlderEventFutureWorkTouchSeparated`, retained candidates transport, old
   events cannot touch created reached/partner endpoints by canonical touch
   disjointness, and the fresh event cannot be strictly older. No created-region
   premise is required. This does not establish global invariant availability,
   the same-boundary case, another candidate-creating rule, raw seams,
   enabledness, or progress.
   `SequentialFigure7OlderEventFutureWorkTouchWaitPreservation.lean`
   conditionally closes the corresponding Wait branch. Retained candidates
   transport through the exact destination and prepared-prefix equations. For
   an actual inserted future-New candidate, the candidate-indexed
   `WaitCreatedHeadTouchSeparated` premise is precisely the remaining
   old-event/conclusion obligation, and Wait appends no current ledger event.
   Relative to the supplied prior invariant this is the exact transition-local
   residual, but neither the scheduler invariant nor canonical history or
   reachability derives it. Unconditional/global Wait, Forward/UnifyPayload,
   same-boundary, raw/source-region seams, enabledness, and progress remain
   open.
   `SequentialFigure7OlderEventFutureWorkTouchWaitDischarge.lean` now derives
   that candidate-indexed residual under structural well-formedness. A touch
   of the inserted par conclusion continues through the exact submitted par's
   stored-left premise, which is either the selected occurrence or its
   already-marked mate. The middle forest owns that premise in a live slot
   strictly newer than the event slot, so exact component disjointness closes
   both orientations. The direct corollary still consumes a supplied prior
   queued-head invariant and an already-successful typed Wait step. It does not
   close the source-region or raw seam, the final equal-boundary callback,
   global invariant availability, enabledness, or progress.
   `SequentialFigure7CrossRepresentativeForwardPreservation.lean` now closes
   the exact state-transport portion of the Forward branch. Old ready and
   waiting occurrences retain their exact prepared-middle boundary, while the
   only newly inserted work is the submitted par conclusion at the active
   boundary. The exported history theorem is deliberately conditional on
   `ForwardCreatedRegionSeparated`, because that conclusion had no prior
   `FutureWorkAt` witness. The current scheduler invariant does not imply this
   new-candidate geometry, so unconditional source-region Forward preservation
   remains an open maturity gate.
   `SequentialFigure7OlderEventFutureWorkTouchForwardPreservation.lean`
   conditionally closes the parallel queued-head Forward branch. Retained
   candidates transport through Prepared and the exact Forward representative
   equality. For an actual inserted candidate, the candidate-indexed
   `ForwardCreatedHeadTouchSeparated` premise is precisely the remaining
   old-event/conclusion obligation, and Forward appends no current ledger
   event. Relative to the supplied prior invariant this is the exact
   transition-local residual, but scheduler invariants, canonical history, and
   reachability do not derive it. That base theorem alone establishes no
   unconditional/global Forward, UnifyPayload, same-boundary,
   raw/source-region seam, enabledness, or progress result.
   `SequentialFigure7OlderEventFutureWorkTouchForwardDischarge.lean` now
   derives the candidate-indexed created-head residual under structural
   well-formedness. Ledger endpoint accounting puts the old event endpoint in
   its representative's owned carrier, while a hypothetical touch of the
   inserted Forward conclusion and source-left carrier closure put that same
   endpoint in the active par carrier. Strict representative order and live
   component disjointness contradict the overlap. The direct corollary still
   requires the supplied prior queued-head invariant and an already-successful
   typed Forward step. It does not close the source-region or raw seam, the
   separate final equal-boundary callback, global invariant availability,
   enabledness, or progress.
   `SequentialFigure7CrossRepresentativeUnifyPayloadPreservation.lean` now
   closes the state-transport and representative-map portions of arbitrary-
   payload Unify. Output work is a same-boundary survivor, an active-ready item
   moved to the previous boundary, or the inserted tensor conclusion. The
   active class alone is redirected to the previous root, and strict output
   ordering excludes prior events in that retired class. The exported history
   theorem remains conditional on `UnifyPayloadCreatedRegionSeparated` for the
   inserted conclusion. The current invariant does not derive this geometry,
   so unconditional Unify preservation remains an open maturity gate.
   `SequentialFigure7OlderEventFutureWorkTouchUnifyPayloadPreservation.lean`
   conditionally closes the parallel queued-head UnifyPayload branch.
   Survivors reuse the prior invariant, while moved work is recovered at the
   prepared active boundary. Strict output order excludes an older event from
   the retired active representative class. For an actual inserted candidate,
   the candidate-indexed `UnifyPayloadCreatedHeadTouchSeparated` premise is
   precisely the remaining old-event/conclusion obligation, and UnifyPayload
   appends no current ledger event. Relative to the supplied prior invariant
   this is the exact transition-local residual, but scheduler invariants,
   canonical history, and reachability do not derive it. Unconditional/global
   UnifyPayload, same-boundary, raw/source-region seams, enabledness, and
   progress remain open.
   `SequentialFigure7OlderEventFutureWorkTouchUnifyPayloadDischarge.lean`
   now derives that candidate-indexed residual under structural
   well-formedness. The tensor output occurrence carrier joins the previous and
   active live slots. A hypothetical touch places the old event's stored-left
   axiom endpoint in that output carrier, while reservation realization places
   it in the event representative's carrier. Strict order separates the event
   from both tensor-input roots, so live-slot disjointness contradicts the
   overlap in either orientation. The direct corollary still requires the
   supplied prior queued-head invariant and an already-successful typed
   UnifyPayload step. It does not close the source-region or raw seam, the final
   equal-boundary callback, global invariant availability, enabledness, or
   progress.
   `SequentialFigure7OlderEventFutureWorkTouchAvailability.lean` now closes
   that queued-head global-availability gap. A direct induction over every
   supplied `CanonicalTagHistory` uses empty, structurally well-formed init,
   and the six successful-rule preservation theorems to derive
   `OlderEventFutureWorkTouchSeparated`. It does not construct a history,
   broaden reachability, provide the distinct mate-region or raw-mark
   invariants, supply unconditional stored-left equal-boundary avoidance, or
   prove enabledness or progress.
   `SequentialFigure7SameRepresentativeEventTouch.lean` now rules out one
   remaining obstruction without assuming a fresh run or success of an
   additional current `new?` call: an exact historical reservation-event touch
   cannot lie in the selected mate's complete source-left region when the
   event and active ready head have the same current representative. The proof
   is kernel checked from reservation realization, component provenance, and
   declarative
   reference-switching acyclicity. It does not cover strictly older events,
   old marked owners, the four created-region premises, exhaustive
   enabledness, or progress.
   `SequentialFigure7ActiveRegionTouchOrder.lean` now classifies the remaining
   historical-touch order for the active `NewGuard` mate region. Every overlap
   is strictly older than the active head in both current-representative and
   immutable raw-age order. Supplying `OlderEventTouchSeparated` excludes all
   ledger-event touches from that region and proves each region tag is
   `some false`; the older structural invariant has a compatibility theorem.
   This is conditional tag freshness, not route/run construction, raw or
   endpoint readiness, queue/capacity evidence, global invariant availability,
   `NewEnabled`, or progress.
   `SequentialFigure7ActiveConclusionTouch.lean` now proves the exact
   structural split for a historical event touching any future candidate
   tensor conclusion: the event also touches the mate or queued head. For the
   active candidate, conditional mate-region tag freshness removes the mate
   branch, even for a same-boundary event, leaving an active-head touch. This
   is not a conclusion-untouched theorem and does not eliminate that head
   touch, exclude raw marks, build a target-avoiding path, close a created
   seam, or prove enabledness or progress.
   `SequentialFigure7OlderEventFutureWorkTouchSeparation.lean` now isolates
   that queued-head residue for the strictly older branch. The supplied
   history invariant, together with `OlderEventTouchSeparated` and structural
   well-formedness, makes a strictly older event's candidate tensor conclusion
   untouched. It holds for empty and, under structural well-formedness, init;
   it transports through Prepared/concl/nop. It is not derived from
   correctness, the scheduler invariant, canonical history, or queue
   provenance. This base layer alone does not cover a candidate-creating rule;
   New is handled by a downstream preservation theorem, while Wait, Forward,
   and UnifyPayload derive their residuals structurally. A downstream induction
   now makes the queued-head invariant available for every structurally
   well-formed canonical history. Mate-region availability, unconditional
   equal-boundary avoidance, raw seams, enabledness, and progress remain open.
   `SequentialFigure7StrictCommitmentTargetAvoidance.lean` now closes the
   strictly older target-path adapter. Under the complete scheduler invariant
   and both supplied separation invariants, an adjacent retained edge whose
   child is strictly older than the future candidate obtains the exact
   child-event untouched callback automatically. Strict sigma ordering extends
   this to any positive retained interval from strict oldness of its final
   boundary. It does not cover an equal final boundary, prove either invariant
   globally, recover queue origin, close a raw seam, or imply progress.
   `SequentialFigure7StrictOlderSigmaSplit.lean` now locates that strict
   interval for any authentic ledger event and future-New candidate satisfying
   the representative inequality. It returns the candidate's immediate
   predecessor plus a possibly empty prefix; the consumer composes every
   positive prefix and treats zero explicitly. It does not discharge the final
   predecessor-to-candidate edge or establish separation availability, queue
   origin, a created-head/raw seam, progress, totality, or completeness.
   `SequentialFigure7EqualBoundaryCommitmentTargetAvoidance.lean` now
   classifies that final edge. Stored-right orientation yields an exact
   target-avoiding path. In general the inclusive result returns that path or
   an authentic same-age stored-left child event whose trace contains the
   exact conclusion-to-head step. The latter is a witness that the generic
   child-untouched callback failed, not a proof that no avoiding path exists;
   both alternatives may hold. Mate-region/raw-mark availability, queue origin,
   progress, completeness, scheduling, and complexity remain outside it.
   The same owners now cover a supplied ready-head par conclusion. Explicit
   child-event untouchedness yields an adjacent avoiding path; at the active
   boundary, an inclusive dichotomy instead records an authentic same-age trace
   step from the par conclusion to selected or mate. Neither untouchedness nor
   elimination of those two trace branches is claimed.
   `SequentialFigure7CommitmentIntervalParConclusionDichotomy.lean` extends
   this to every complete positive retained interval. It returns a composed
   avoiding endpoint path or one exact local edge with no avoiding path plus
   an authentic child-age selected/mate trace. The child is strictly before or
   equal to the final boundary, and the outer alternatives remain inclusive.
   The failed edge, both trace branches, a distinct payer, the history-tail
   law, and progress remain open.
   `SequentialFigure7CommitmentIntervalParTraceLocalization.lean` further
   compares the failed branch with the active occurrence carrier. A strictly
   older trace cannot end at the selected head or an active-owned mate, so it
   must be stored-right and end at a mate outside the active owned carrier.
   Equal-final failures retain both selected/mate trace orientations, and the
   outer alternatives remain inclusive. The external mate, equal-final cases,
   distinct payer, history-tail law, and progress remain open.
   `SequentialFigure7CommitmentIntervalParGuardOutcome.lean` gives the actual
   Nop and Wait specializations. Its common four-case carrier keeps avoidance,
   both equal-final trace orientations, and the strictly older stored-right
   mate. Nop makes the older mate external and raw-unmarked; Wait makes it
   external, concretely marked at its exact age, and strictly older at the
   representative. No branch returns that endpoint to a distinct payer, and
   the equal-final, history-tail, and progress gates remain open.
   `SequentialFigure7CommitmentIntervalParGuardReentry.lean` now connects the
   older external mate back into the active carrier under supplied
   reference-switching connectedness. Its exact inbound submitted-parent edge
   targets the selected raw head, a non-global ready-tail raw occurrence, or a
   prior concrete mark. This exposes an immediate payer branch but does not
   eliminate the selected/marked targets or either equal-final trace, derive
   the history-tail law, or prove progress.
   `SequentialFigure7CommitmentIntervalParGuardReentryFailure.lean` now applies
   exact ready-tail failure to the strictly older stored-right branch. It rules
   out the selected target and returns a distinct authenticated concrete mark
   represented at the active boundary. The marked target, avoiding branch, and
   both equal-final traces remain; no tail law or progress theorem follows.
   `SequentialFigure7CommitmentIntervalParGuardReentryMateSeparation.lean`
   then uses simple-path freshness and exact connective-parent uniqueness to
   separate the marked inbound target from the current mate. Every exact
   connective view rooted at that target has a mate different from the current
   selected head. This removes the selected raw-sibling alternative for the
   exact target, but it does not eliminate the target, choose par versus tensor
   source shape, return a ready-tail payer, derive the history-tail law, or
   close the avoiding/equal-final cases. The verified combined audit covers
   986 theorems: 694 standard-three, 25 axiom-free, 128 `propext`-only, and
   139 `propext`/`Quot.sound` boundaries.
   `SequentialFigure7CommitmentIntervalParGuardReentryMarkedTargetTemporal.lean`
   then binds the unique consumer at that same target to the exact inbound
   parent edge. Its target-indexed continuation is an unmarked raw mate outside
   the active carrier, queued parent work at a strictly older boundary, or a
   parent conclusion marked at a strictly older representative. This does not
   eliminate the target or a temporal branch, derive a payer or tail law, or
   close the avoiding/equal-final cases. The verified combined audit covers
   989 theorems: 697 standard-three, 25 axiom-free, 128 `propext`-only, and
   139 `propext`/`Quot.sound` boundaries.
   `SequentialFigure7CommitmentIntervalParGuardReentryMarkedTargetContinuationExit.lean`
   then follows a marked non-global parent through a finite continuation chain.
   It ends raw outside the active carrier, at an exact raw return to the current
   selected/mate pair, at older queued work, or at an older marked global
   conclusion. The return retains strict target-to-mate formula-complexity
   growth but is not eliminated. No terminal case supplies a payer or tail law.
   The verified combined audit covers 992 theorems: 700 standard-three, 25
   axiom-free, 128 `propext`-only, and 139 `propext`/`Quot.sound` boundaries.
   `SequentialFigure7MarkedTargetRawReturnCyclicReduction.lean`
   then gives the exact raw return a full-graph cyclic normal form. The
   retained prefix and forward continuation tail are individually
   nonbacktracking. Complete cancellation is empty or occurs at one of their
   two oriented endpoint junctions. In the latter case, both segments have
   unique occurrence indices, every prefix occurrence is backward and has its
   exact reverse in the tail, and every reached prefix vertex is concretely
   marked and non-global. Simple-path source uniqueness orders the tail as the
   exact reverse traversal of the prefix. A nonempty remainder has exact kept and omitted
   par-premise occurrences in the prefix and tail respectively, and the omitted-right
   source is a concrete marked nonconclusion. Neither alternative is
   eliminated, and the other
   continuation exits and equal-final branches are unchanged. The verified
   combined audit still covers 996 theorems: 704
   standard-three, 25 axiom-free, 128 `propext`-only, and 139
   `propext`/`Quot.sound` boundaries.
   `SequentialFigure7MarkedTargetNopRawReturnElimination.lean` then excludes the
   exact raw return in the typed Nop branch. Every nontrivial
   marked-conclusion chain ends at a concrete mark, but the Nop step keeps its
   current mate raw-unmarked. The refined Nop target still admits raw work
   outside the active carrier, older future work, and an older marked global
   conclusion. Wait and the generic cyclic residuals are unchanged. The
   verified combined audit now covers 999 theorems: 706 standard-three, 25
   axiom-free, 129 `propext`-only, and 139 `propext`/`Quot.sound` boundaries.
   `SequentialFigure7MarkedTargetRawReturnFirstDescent.lean` then refines the
   exact-return branch retained by Wait. Its first submitted parent conclusion
   lies outside the active occurrence carrier, so a nontrivial return chain
   immediately reaches a strictly older representative. Canonical tag history
   authenticates that marked conclusion. The theorem exposes rather than
   eliminates this residual and derives no tail law or progress. The verified
   combined audit now covers 1002 theorems: 709 standard-three, 25 axiom-free,
   129 `propext`-only, and 139 `propext`/`Quot.sound` boundaries.
   `SequentialFigure7RawMarkCausalOrder.lean` and
   `SequentialFigure7MarkedTargetRawReturnCausalDescent.lean` then make the
   prepared-selection event order explicit. Both submitted premises precede
   an authentically marked connective conclusion, and the first-descent
   reduction records that the re-entry origin and sibling mate precede its
   older marked parent. The sibling retains a finite continuation exit. The
   generic target adapter and typed Wait theorem expose the same refinement.
   `SequentialFigure7MarkedTargetRawReturnTerminalCausalOrder.lean` proves the
   strict relation transitive and asymmetric. It orders every distinct
   marked-chain origin before an authenticated terminal and attaches the outer
   Wait mate as that terminal. In the retained causal-descent alternative,
   both the re-entry origin and first sibling precede it. The reduction does
   not eliminate either residual,
   establish a total event order, or derive a tail law or progress. The
   verified combined audit now covers 1016 theorems: 723 standard-three, 25
   axiom-free, 129 `propext`-only, and 139 `propext`/`Quot.sound` boundaries.
   `SequentialFigure7MarkedTargetRawReturnSiblingExitCausalOrder.lean` makes
   authentic event order total on distinct vertices and classifies the first
   sibling continuation against the authenticated non-global outer terminal.
   Raw and future endpoints are unchanged; a marked-global endpoint is
   strictly earlier or strictly later. The generic terminal target and typed
   Wait theorem retain the first descent and add this classification. No
   endpoint is eliminated and no tail law or progress theorem follows. The
   verified combined audit now covers 1022 theorems: 729
   standard-three, 25 axiom-free, 129 `propext`-only, and 139
   `propext`/`Quot.sound` boundaries.
   `SequentialFigure7MarkedTargetRawReturnSiblingExitCausalJunction.lean`
   then applies the exact cyclic-junction normal form to the complete chain
   already retained by the first descent. The generic adapter and typed Wait
   theorem keep the same switching path and target connective while pairing
   that junction witness with the sibling causal classification. No branch is
   eliminated and no payer, history-tail law, completion, or progress follows.
   The verified combined audit now covers 1025 theorems: 732 standard-three,
   25 axiom-free, 129 `propext`-only, and 139 `propext`/`Quot.sound`
   boundaries.
   `SequentialFigure7MarkedTargetRawReturnCyclicEndpointCausalOrder.lean`
   then turns the complete-cancellation site disjunction into simultaneous
   reverse junctions at both exact walk endpoints and classifies the cyclic
   source as equal to or strictly before the authenticated outer terminal. The
   target adapter and typed Wait theorem preserve every other alternative. No
   junction, par-pair residual, sibling exit, marked-global order, or descent is
   eliminated, and no payer, tail law, completion, or progress follows. The
   verified combined audit now covers 1029 theorems: 735 standard-three, 25
   axiom-free, 129 `propext`-only, and 140 `propext`/`Quot.sound` boundaries.
   `SequentialFigure7MarkedTargetRawReturnCompleteCancellationCausalEndpoints.lean`
   then rules out equality between the cyclic source and base in every
   nonempty complete-cancellation branch. Prefix edge-index uniqueness turns
   internal reduction into cyclic reduction; retention would otherwise place
   a forbidden nonempty closed cyclically nonbacktracking walk in the correct
   reference-switching tree. Both endpoint junctions remain, while the source
   is strictly before the authenticated outer terminal. No other residual is
   eliminated. The verified combined audit now covers 1031 theorems: 737
   standard-three, 25 axiom-free, 129 `propext`-only, and 140
   `propext`/`Quot.sound` boundaries.
   `SequentialFigure7MarkedTargetRawReturnSiblingExitForwardCausalOrder.lean`
   then re-roots the first descent's sibling continuation after its shared
   marked non-global conclusion. Finite marked-conclusion chains from the same
   origin have comparable terminals, which forces every marked-global sibling
   endpoint strictly after the authenticated outer mate and eliminates the
   earlier order. Raw and future exits, complete cancellation, both endpoint
   junctions, the par residual, the descent, and tail failure remain. No payer,
   history-tail law, completion, or progress follows. The verified combined
   audit now covers 1035 theorems: 741 standard-three, 25 axiom-free, 129
   `propext`-only, and 140 `propext`/`Quot.sound` boundaries.
   `SequentialFigure7MarkedTargetRawReturnSiblingExitOpen.lean` then uses the
   selected ready head's exact raw-unmarked lookup and canonical
   `rawMarkedPremisesBefore` receipt to eliminate the remaining marked-global
   sibling endpoint. Its open-exit carrier retains raw-mate and future-work
   endpoints only. The target's separate raw, future, and older marked-global
   branches and every cyclic, junction, par, descent, and tail-failure
   residual remain. No payer, history-tail law, completion, or progress
   follows. The verified combined audit now covers 1039 theorems: 744
   standard-three, 25 axiom-free, 130 `propext`-only, and 140
   `propext`/`Quot.sound` boundaries.
   `SequentialFigure7MarkedTargetRawReturnSiblingExitTemporal.lean` additionally
   classifies the two open sibling exits under exact active occurrence and
   ready-tail failure. Raw work is outside or returns exactly to the current
   selected/mate pair; outside future work is strictly older. The public
   carrier retains the outside terminal in every case, and its runnable
   consumer destructs every constructor and calls the generic, target, and
   typed Wait theorems. The separate target branches and exact raw return remain
   open. The verified combined audit now covers 1042
   theorems: 747 standard-three, 25 axiom-free, 130 `propext`-only, and 140
   `propext`/`Quot.sound` boundaries.
   `SequentialFigure7FutureWorkExactLocation.lean` exposes the exact ready or
   waiting scheduler location behind every `FutureWorkAt`. The ready case
   carries its sigma slot, bucket, live component frontier, and unmarked
   conclusion; the waiting case carries its exact cell, submitted par
   producer, oriented marked premises, and strict boundary order. Both
   premises of any connective conclusion stored as future work are concrete-
   marked. `SequentialFigure7MarkedTargetRawReturnSiblingExitScheduled.lean`
   transports those facts into the older future sibling endpoint and typed
   Wait theorem without changing raw-outside or exact-return cases. The
   verified combined audit now covers 1047 theorems: 752
   standard-three, 25 axiom-free, 130 `propext`-only, and 140
   `propext`/`Quot.sound` boundaries. No endpoint is eliminated and no payer,
   tail law, completion, or progress result follows.
   `SequentialFigure7MarkedTargetRawReturnSiblingExitCausalOwnership.lean`
   authenticates and orders both endpoint-premise marks. The outside terminal
   resolves strictly below the active boundary; the mate resolves either
   strictly below outside the carrier or exactly at the active carrier. An
   active-owned waiting mate forces the exact older-terminal/younger-mate
   orientation and active younger boundary. Ready work remains ready. Its
   runnable consumer destructs every public carrier and calls the generic,
   target, and typed Wait theorems. The verified combined audit now covers
   1052 theorems: 757 standard-three, 25 axiom-free, 130 `propext`-only, and
   140 `propext`/`Quot.sound` boundaries. No endpoint, payer, tail law,
   completion, or progress theorem follows.
   `SequentialFigure7MarkedTargetRawReturnSiblingExitReadyMateElimination.lean`
   now rules out ready work when the older future endpoint's mate is owned by
   the active occurrence carrier. Exact live-component occurrence ownership at
   the older ready boundary conflicts with active ownership of the same mate.
   The active-owned branch therefore retains only the exact waiting return;
   older-outside mates may remain ready or waiting. Its runnable consumer
   destructs the refined scheduler, sibling, target, and typed Wait outcomes.
   Five registered public theorems use the standard-three boundary. The
   verified combined audit now covers 1057 theorems: 762 standard-three, 25
   axiom-free, 130 `propext`-only, and 140 `propext`/`Quot.sound` boundaries.
   The future endpoint, exact raw return, payer, history-tail law, completion,
   and progress remain open.
   `SequentialFigure7MarkedTargetRawReturnSiblingExitWaitingMateParentRecursion.lean`
   now rebuilds the surviving active-owned waiting mate as a marked,
   non-global active-frontier parent escape whose submitted conclusion leaves
   the active carrier. Under ready-tail failure, it normalizes that escape to
   the existing parent temporal outcome and transports the recursive status
   through the sibling target and typed Wait trace. Its runnable consumer
   reconstructs every public carrier and invokes all six registered public
   theorems. The verified combined audit now covers 1063 theorems: 768
   standard-three, 25 axiom-free, 130 `propext`-only, and 140
   `propext`/`Quot.sound` boundaries. Active waiting is reduced recursively,
   not eliminated, and no well-founded repeated normalization is proved;
   older-outside endpoints, exact return, a payer, the history-tail law,
   completion, and progress remain open.
   `SequentialFigure7MarkedTargetWaitingMateExternalTemporal.lean` now rules
   out a raw continuation from the exact active-owned waiting mate to its
   already concrete-marked older terminal in the public result type. The
   two-constructor `ActiveMateWaitingParentExternalTemporalOutcome` is fixed to
   `consumer.conclusion` and contains only `olderFuture` and `olderMarked`.
   The `propext`-only `.activeCarrierOutcome` explicitly forgets it into the
   broader parent temporal carrier. From
   `CanonicalTagHistory`, `SchedulerInvariant`, active component lookup and
   occurrence, the outside-conclusion premise, and the waiting witness, the
   direct theorem and active scheduler status return or store that narrowed
   carrier. It requires neither
   `DeclarativelyCorrect`, `noTail`, nor an explicit `mateActive` premise. The
   runnable consumer reconstructs or destructs all ten public declarations and
   invokes all six registered public theorems. The verified combined audit now
   covers 1069 theorems: 773 standard-three, 25 axiom-free,
   131 `propext`-only, and 140 `propext`/`Quot.sound` boundaries. Older-outside
   mates may still be ready or waiting; broader exact selected/mate raw
   returns, external temporal endpoints, the history-tail law, completion,
   progress, and totality remain open.
   `SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentry.lean`
   now refines both constructors of that exact external temporal carrier. At
   either strictly older future or marked endpoint, canonical history supplies
   the exact `StrictOlderCommitmentSplit`, reference-switching connectedness
   supplies an owned-to-external `ActiveCarrierExternalEndpointCrossing`, and
   `.reentry` reverses its edge-simple path and boundary edge. Exact ready-tail
   failure then yields `ActiveCarrierExternalReentryFailureHistoricalStatus`.
   The resulting two-constructor carrier stays fixed to
   `consumer.conclusion` and retains temporal, commitment, crossing, re-entry,
   and failure evidence. Crossing and re-entry are stored separately, so the
   carrier does not identify arbitrary existential witnesses. Its runnable
   consumer reconstructs all three public declarations and invokes both
   registered public theorems. The generated API now has 91 sections and 1785
   declarations; the accumulated rolling surface has 154 declarations. The
   source tree has 168 modules, the facade imports 164 submodules (165 modules
   including the facade), and the repository has 300 Lean files. The verified
   combined theorem audit now covers 1071 theorems: 774 standard-three, 25
   axiom-free, 131 `propext`-only, and 141 `propext`/`Quot.sound` boundaries.
   The inbound target remains the selected raw-unmarked head or a distinct
   canonical-history-authenticated mark at the active representative. Avoiding
   re-entry, target elimination, a payer, the history-tail law, completion,
   progress, termination, and totality remain open.
   `SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryMarked.lean`
   now eliminates the selected raw-unmarked branch of the nested failure status
   when the enclosing selected connective is a structurally well-formed
   stored-right `par`. The generic
   `ActiveCarrierExternalReentryFailureHistoricalStatus.markedHistoricalTarget_of_storedRight`
   theorem uses structural inbound-parent-edge separation and requires no
   path-avoidance premise. The two exact future/marked waiting endpoints retain
   all temporal, commitment, crossing, and re-entry fields while replacing only
   their failure status with
   `ActiveCarrierExternalReentryMarkedHistoricalTarget`. Constructor-preserving
   maps carry that refinement through the active future-work mate status,
   continuation sibling target, and typed Wait older-mate trace. Older-outside,
   raw-outside, selected-return, future/marked sibling exits, avoiding/equal
   trace branches, and causal-descent/cyclic-junction receipts remain unchanged.
   The runnable consumer exercises all 10 public declarations, including six
   registered public theorems. The generated API now has 92 sections and 1795
   declarations; the accumulated rolling surface has 164 declarations. The
   source tree has 169 modules, the facade imports 165 submodules (166 modules
   including the facade), and the repository has 302 Lean files. The verified
   combined theorem audit now covers 1077 theorems: 780 standard-three, 25
   axiom-free, 131 `propext`-only, and 141 `propext`/`Quot.sound` boundaries.
   The surviving authenticated mark is not eliminated or converted into a
   payer. No avoiding witness or path alignment, history-tail law, progress,
   completion, termination, or totality result follows.
   `SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryTemporal.lean`
   now starts the next normalization at the exact waiting endpoint, which may
   be `consumer.conclusion` rather than the enclosing current mate. The marked
   target belongs to the active frontier and owned carrier, so the enclosing
   mate's outside-carrier receipt separates them. Structural parent uniqueness
   binds the inbound edge to the target's submitted consumer and aligns its
   source with that consumer's conclusion. Under the retained exact
   ready-tail-failure premise, the parent status is an unmarked raw mate outside
   the carrier, future work at a strictly older boundary, or a marked
   conclusion at a strictly older representative. The
   result is carried through both exact waiting endpoints, the active
   future-work mate, continuation sibling target, and typed Wait older-mate
   trace while preserving unrelated exits and causal/cyclic receipts. Its
   runnable consumer reconstructs all 11 public declarations and invokes all
   six public theorems. The target remains an authenticated mark represented
   at the active boundary; no payer, witness alignment, history-tail law,
   progress, completion, termination, or totality result follows.
   `SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryContinuationExit.lean`
   now retains exact ready-tail failure, preserves `path.start = endpoint` for
   that target's arbitrary endpoint, and normalizes its finite
   `MarkedConclusionChain`. It ends with a raw-unmarked terminal consumer mate
   outside the active carrier; an exact selected/current-mate return with
   current-conclusion alignment and strict target-to-terminal complexity
   growth; future work outside at a strictly older boundary; or a marked-global
   conclusion outside at a strictly older representative. The public surface
   is one proposition carrier plus one standard-three theorem, both exercised
   by the runnable consumer. No exit is eliminated. The result derives no
   payer, avoiding witness or aligned re-entry path, history-tail law,
   progress, completion, termination, or totality.
   `SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryContinuationWaiting.lean`
   combines carrier-forest marked ownership with live-carrier disjointness. A
   nontrivial chain first marks the known-outside parent conclusion. An active
   owner contradicts that outside premise; a distinct live owner receives the
   active origin by connective ownership closure and contradicts carrier
   disjointness. Every retained chain is therefore reflexive. This eliminates
   the exact selected/current-mate return and marked-global endpoint. Exact scheduler
   localization further excludes older ready future work because its live
   carrier would also own the active-frontier origin. Exactly two parent forms
   remain: a raw-unmarked target-consumer mate outside active ownership, or the
   target-consumer conclusion as strictly older `FutureWorkAt` in an exact
   initialized waiting cell. The waiting receipt preserves its payload,
   submitted par/source data, oriented marked premises, and boundary equations.
   The public surface is one exact-waiting-location definition, one two-case
   target definition, and one standard-three theorem. The result adds no
   source, oracle, or runtime evidence and does not eliminate the target,
   recover a payer, align witnesses or paths, derive a history-tail law, or
   prove progress, completion, termination, or totality.
   `SequentialFigure7WaitingReentryContinuationProducerOrientation.lean`
   now exposes the assumption-minimal orientation of the remaining older
   waiting producer. Its one public theorem preserves the exact initialized
   waiting payload, par/source data, marks, and boundary order, then identifies
   the active-representative target as the younger premise and the consumer
   mate as the older premise. It additionally proves
   `targetAge = youngerAge`, `youngerBoundary = active`, and the older/younger
   representative equations at the older/active boundaries. The runnable
   consumer invokes the theorem and audits its standard-three trust boundary.
   Only `SchedulerInvariant`, the exact location, target mark,
   active-representative equality, and strict older-boundary inequality are
   assumed; no carrier, component lookup, occurrence witness, history,
   `noTail`, or declarative correctness enters the interface. The theorem does
   not eliminate a survivor, recover a payer, align paths or witnesses, derive
   a tail law, or prove progress. In particular, the raw survivor is unchanged.
   `SequentialFigure7CommitmentBlockerAdvance.lean` now combines the global
   queued-head law, strict split, and equal-boundary result. Under declarative
   correctness and the complete scheduler invariant, for a supplied canonical
   history, active `NewGuard`, and authentic ledger event whose current
   representative is strictly below the active head, the theorem yields an
   exact avoiding path, a mate-touching event with a strictly higher current
   representative still below the head, or the exact equal stored-left callback
   failure. At that checkpoint, the reduction was inclusive: the advance was
   not raw-age/ledger chronology, was not maximalized or eliminated, and the
   callback failure did not deny path existence. It derives no mate-region invariant, closes no
   created-candidate raw seam, and proves no `NewEnabled` or progress result.
   `SequentialFigure7CommitmentBlockerMaximality.lean` then eliminates that
   current-representative advance under the same explicit public inputs. It
   maximizes over the finite authentic mate-touch blockers above the original
   event; a maximal blocker cannot admit an avoiding commitment path without
   creating the tensor bypass forbidden by reference-switching acyclicity, and
   a further advance contradicts maximality. The inclusive result is an exact
   avoiding path or the exact equal stored-left callback failure. The callback
   branch does not deny path existence, and the theorem does not derive queue
   origin, the remaining mate-region/global raw-mark invariants, a created-
   candidate raw seam, `NewEnabled`, progress, totality, or completeness.
   `SequentialFigure7ActiveRegionTouchSeparation.lean` then supplies the local
   bridge needed to consume both inclusive branches. Its public
   `ActiveMateEventAnchor` carries a conclusion-avoiding exact path from the
   active mate to one event's stored-left endpoint. A strictly older anchored
   event contradicts the exact reference tree in either maximality branch: the
   commitment path gives the active tensor bypass, while the stored-left
   callback trace gives an alternate walk omitting the active tensor edge.
   Every authentic ledger event is consequently touch-separated from the
   complete active mate region. This is a per-guard theorem, not a global
   preserved history invariant or a claim that callback failure is impossible
   without an anchor.
   `SequentialFigure7ActiveRegionAvailability.lean` now composes that
   conditional tag freshness with the complete structural run-or-blocker
   theorem. The result is an exact dichotomy between a complete
   `NewSourceRegionInput` and an old `ExactMarkedOccurrenceOwner` in the active
   mate region, followed by the corresponding `NewEnabled`/owner dichotomy.
   A pointwise no-owner premise yields `NewEnabled`. This closes the run,
   readiness, endpoint queue-absence, fresh-capacity, and future-cell
   obligations in the successful branch, but it does not derive the owner-clear
   premise, global older-event separation, created-region preservation,
   exhaustive enabledness, or progress.
   `SequentialFigure7OlderRawMarkedRegionSeparation.lean` now expresses the
   exact old-owner obstruction as a state-only raw-mark separation invariant.
   It holds for empty and initialized states and is preserved through
   Prepared/concl/nop. Given that invariant, declarative correctness and the
   complete scheduler invariant exclude every concrete raw mark and every
   exact marked owner from the active mate region, so the existing
   availability theorem yields `NewEnabled`. This is not global availability:
   rule-specific created-candidate raw geometry and progress remain open.
   `SequentialFigure7ActiveRegionEnabledness.lean` removes the need to supply
   that global raw-mark invariant for the current active guard. A hypothetical
   raw mark is mapped to its same-age authentic reservation event and final
   owned component; exact active-region and owned paths construct the public
   anchor, and strict representative order contradicts the preceding theorem.
   Thus the complete active region has no raw mark, no exact owner, and no
   historical tag blocker. Structural search yields `NewSourceRegionInput` and
   input-only `NewEnabled` for every supplied correct canonical-history active
   guard. This closes the local active-guard applicability gate, not guard
   existence, branch exhaustiveness, global raw-invariant preservation,
   dispatcher progress, later-state totality, worklist completeness, fallback
   removal, token-age scheduling, or whole-program linearity.
   The predecessor projection now discharges that ready-head residual for
   states carrying the new invariant. After the successful-rule prefix closes
   through UnifyPayload, the full canonical-history induction makes the
   invariant available for every correct executed dispatcher history. A
   reachable state with an explicitly supplied ready head therefore has one
   exact successful dispatcher result. The active-top residual now gives a
   started correct reachable state the disjunction of exact dispatch and a live
   top component with no raw-unmarked frontier occurrence. The new
   marked-nonconclusion debt theorem turns that drained branch into
   `core.allMarked = true` when its additional state predicate is available.
   Full-history continuation credit is now available without a correctness
   premise and normalizes through a finite strict-complexity chain to one of
   three endpoints. The separate raw/future-only endpoint-locality law is
   sufficient to recover active-top debt and the conditional all-marked result,
   but every successful typed Wait from a scheduler-invariant input refutes the
   unrestricted law at its output. Canonical history therefore cannot preserve
   that exact law across Wait unchanged. This says neither that the output is
   drained nor that a reachable Wait exists, and leaves direct debt and
   Wait-compatible drained, temporal, or cross-component weakenings open.
   The library therefore still lacks unconditional branch applicability,
   progress, completion, terminality, later-state totality, global raw seams,
   fallback removal, scheduling fidelity, sequentialization, pure-worklist
   completeness, and whole-program linearity.
   `SequentialFigure7OlderRawMarkedRegionNewPreservation.lean` now proves the
   New preservation step under the exact residual
   `NewRetainedRawMarksSeparated` condition. The selected mark versus created
   candidate case is discharged from reference-switching acyclicity; retained
   candidates transport through Prepared, leaving only input-retained marks
   versus created regions in the premise. The fresh candidate cannot be
   represented by middle-state `FutureWorkAt`, so this is a genuine
   transition-local seam. Canonical history/reachability does not yet supply
   the seam, and this is not global availability or progress.
   `SequentialFigure7OlderRawMarkedRegionWaitPreservation.lean` now proves the
   corresponding Wait preservation step under
   `WaitRetainedRawMarksSeparated`. The selected mark cannot be strictly older
   than the destination candidate; retained candidates transport through
   Prepared. Only input-retained marks versus actual Wait-created regions remain
   in the premise. This transition-local seam is distinct from
   `WaitCreatedRegionSeparated`, requires no declarative correctness or history,
   and is not yet supplied by canonical reachability. This theorem alone does
   not establish global availability or progress.
   `SequentialFigure7OlderRawMarkedRegionForwardPreservation.lean` now proves
   the corresponding Forward preservation step under
   `ForwardRetainedRawMarksSeparated`. The selected mark and every inserted
   candidate have the same active raw age, so their strict-order case is
   impossible; retained candidates transport through Prepared. Only
   input-retained marks versus actual Forward-created regions remain in the
   premise.
   This transition-local seam is distinct from
   `ForwardCreatedRegionSeparated`, requires no declarative correctness or
   history, and is not yet supplied by canonical reachability. This theorem
   alone does not establish global availability or progress.
   `SequentialFigure7OlderRawMarkedRegionUnifyPayloadPreservation.lean` now
   proves the corresponding arbitrary-payload Unify preservation step under
   `UnifyPayloadCreatedRawMarksSeparated`. Strict older-than ordering excludes
   the retired active representative class; survivors and moved candidates
   transport through the prepared invariant. Only prepared-state raw marks
   versus actual inserted tensor candidate regions remain in the premise. The
   survivor, moved, and created alternatives cover the output but need not be
   exclusive. This raw seam differs from
   `UnifyPayloadCreatedRegionSeparated`, requires no correctness or history,
   and is not yet supplied by canonical reachability. It proves neither
   unconditional Unify, global availability, nor progress.
   `ProofNetIRNewProgressAudit.lean` now adds a finite, executable audit of the
   complete ready-head boundary over states reached by successful initialization
   and the canonical dispatcher. At every post-initialization state it
   classifies concrete marking completeness, reconstructs exact typed
   `ReadyHeadInput`, and invokes `dispatch?`; an incomplete state without a head
   or an incomplete dispatch-none stop produces a full replayable witness. The
   default CI corpus classified all 22,590 incomplete states as ready-head and
   successful-dispatch states and all 594 dispatch-none stops as fully marked.
   The opt-in depth-5 extension classified 95,190 incomplete states and 1,254
   fully marked stops in the same way. Both modes recorded zero missing-head,
   incomplete-dispatch-none, cycle, and fuel-truncation findings. The same runs
   retain the guarded-New subaudit and independently inspected 6,198 and 26,658
   selected marked-tensor ready-head states; all had an exact immediate sigma
   predecessor, with zero missing-predecessor gaps. Deep acceptance uses
   `unificationCheck` and the kernel theorem `unificationCheck_eq_check`, while
   the 18 cases at depths 0 through 2 also run the direct all-switchings
   checker. This finite receipt does not prove that canonical histories preserve
   marked-nonconclusion debt, nor that `ActiveTopDrained` alone implies semantic
   completion, and it does not establish intended-state exhaustiveness,
   progress, totality, or completeness.
   Its separate `--cross-representative-search` receipt covers 96 labelled
   depth-5 cases and 1,182,816 reachable states: 1,172,208 incomplete states all
   had exact ready heads and successful dispatches, while all 10,608
   dispatch-none stops were fully marked. New contributes 328,848
   successful steps, 222,246 actual endpoint candidates (59,706 reached and
   162,540 partner), and 3,333,924 strict prior-event pairs. Wait contributes
   5,682 steps, 636 candidates, and 1,068 pairs; Forward contributes 158,766
   steps, 33,582 candidates, and 117,324 pairs. Unify contributes 328,848
   steps, 528,204 retired-event remaps, 163,806 moved candidates, 58,056
   inserted-conclusion candidates, and 243,570 strict pairs. Independent
   nonzero gates cover every rule, both New endpoint kinds, and the Unify
   representative-changing and moved-work paths. The complete New, Forward,
   and Unify transitions and exact Wait prepend are decoded fail closed, with
   zero intersections or decoder, region, representative, ledger, cycle, and fuel
   failures. `--wait-search` is a compatibility alias for the same audit. This
   is finite falsification evidence only, not a proof of any conditional
   premise.
   `SequentialFigure7TagHistory.lean` now derives a branch-aligned augmentation
   from that exact history and from certified dispatcher reachability. It proves
   exact current-tag provenance, stable tags for all five non-`new` branches,
   strict fresh growth for `new`, touched-set separation, touched-history
   independence at a common concrete state, and history-wide submitted-slot
   `Nodup`. The state-only invariant still admits same-sized forged tag arrays;
    this checkpoint requires proof-carrying history evidence and does not
    separately prove the concrete all-true replacement unreachable.
    `SequentialFigure7RawMarkHistory.lean` reuses the same branch evidence to
    recover every successful branch's prepared selection. It proves exact
    one-step old-or-current-event mark transport, final mark iff canonical raw
    event, and executed-history/reachability event recovery. Raw-mark events
    are not `NEXTAXIOM` touches: stable rules can mark connective conclusions.
    This is provenance only; this layer alone does not provide queue-origin or
    vertex-level commitment paths, a proof of any created-candidate seam, or
    progress. The separate commitment-spine, adjacent-path, and conditional
   target-avoidance theorems supply retained ancestry and the one-edge geometry
   under an explicit child-event untouched law. Explicit adjacent callbacks
   now compose across any supplied nonempty retained-`sigma` interval. When
   both strict separation invariants and the scheduler invariant are supplied,
   the law and callback are automatic for edges, or positive intervals ending
   at boundaries, strictly older than the candidate. The queued-head invariant
   has empty/init, stable, successful New, and structurally discharged
   Wait/Forward/UnifyPayload preservation plus global canonical-history
   availability under structural well-formedness. Events whose current
   representatives are strictly below the candidate now split at its immediate
   predecessor. The stored-right final edge is now closed, finite maximality
   eliminates the strict current-representative advance, and the stored-left
   callback-failure touch witness is exact; unconditional stored-left
   avoidance, queue origin, raw-seam discharge, exhaustive
   guard classification, unconditional full-rule reachability, closing-par
   scheduler-order exclusion, correct-state
   progress, pure worklist completeness, recursive fallback removal, faithful
   `NEXTAXIOM`/token-age sequencing, and a whole-program linear cost theorem
   remain open.
   The narrower production-core `queuePar?`/`queueTensor?` and delayed-stack
   `prependReadyTop?`/`mergeTopReadyWaiting?` primitives are now kernel
   checked with exact success witnesses. They leave queued conclusions
   raw-unmarked and preserve the local abstraction, component, parent, carrier,
   counter, shape, and waiting-domain invariants under explicit hypotheses.
   They are not full rules by themselves. The bounded `UnifyEmpty` wrapper now
   binds the two representatives to scheduler `j/i`, orients
   `parent[i] := j`, and drains only `W(j) = []`; it increments only the tensor
   constructor. `UnifyOne` constructs exactly the singleton drained par. The
   local arbitrary executor now constructs every stored payload par head to
   tail between the tensor and the drain and proves the required
   `1 + |W(j)|` counter change. Complete exact occurrence provenance and
   scheduler-invariant preservation are now proved for every successful
   arbitrary payload. The full invariant discharges all hidden guards once the
   explicit pure-input enabled predicate is supplied for the relevant stable or
   payload rule. Deriving the correct predicate exhaustively for every chosen
   reachable branch remains open. Old
   empty/singleton success maps one way
   to the same new output; no function equality or reverse equivalence is
   asserted.
   The stack's deterministic
   `conclusion :: (payload ++ previousReady ++ activeReady)` order refines
   paper-level sets and does not establish global ownership or linearity.
   For callers that require fail-closed resource handling,
   `reconstructDerivationWithinLimits` checks explicit formula, link, and
   conclusion ceilings and runs only the structure-guided tier. It returns
   structured limit, malformed-input, no-candidate, or verification-failure
   diagnostics. Lean proves that every success is sound, reference-accepted,
   and included in the unbounded decision's accepted set; heuristic failure is
   not exposed as logical rejection.
4. A semantic relation modulo reordered links now has a complete executable
   decision procedure on structurally well-formed certificates. It now also
   has a complete executable finite canonical family: Lean proves extensional
   family membership equality iff `ProofNetEquivalent`. An experimental JSON
   fingerprint is total and forward invariant. A separate explicitly
   versioned, length-framed structural code is proved injective, and equality
   of its canonical minimum is proved equivalent to `ProofNetEquivalent` on
   structurally well-formed or checker-accepted inputs. A distinct bounded JSON
   parser, schema, migration function, and safe parsed-key matcher now expose
   the payload as `proofnet-canonical-key-0.1`. That retained implementation
   still materializes the factorial family and remains limited to seven links.
   v0.8 adds an independent occurrence-forest
   canonicalizer. Lean proves exact vertex coverage, exact link emission,
   in-class representation, and intrinsic-key equality iff
   `ProofNetEquivalent`; no link permutation is enumerated. The separate
   `proofnet-canonical-key-0.2` wire removes the link-count ceiling while
   retaining token/character limits, differential tests against the factorial
   oracle, malformed-input fuzzing, and a measured qualification through 145
   links. The current direct implementation is polynomial
   (`O(VL + V^2)`) but serialized formula volume and broader adversarial
   qualification remain engineering work.
   Conclusion-order canonicalization and arbitrary graph isomorphism remain
   outside the current claim. The v0.3.1 wire theorem remains intentionally
   about the narrower, order-preserving `ReindexEquivalent` relation.
   For accepted certificates, `CheckedCertificate.sameProofNet?` is now the
   supported production pairwise identity boundary and has an exact iff
   theorem. Ordered conclusions constrain candidate generation, reducing the
   64-pair repeated-label stress case from `(64!)^2` theoretical unconstrained
   orders to one generated candidate. Numeric-free one-hop incident-link views
   now also prune internal repeated-label alignments, with a proof that every
   direct equivalence witness survives the filter. This does not provide a
   stronger conclusion-reordering identity or a polynomial worst-case bound
   for pairwise search, checking, or sequentialization.

## Engineering gaps blocking a mature-library claim

- v0.2/v0.3 serialization now has a native Lean parser, path-aware parse
  errors, normalization validation, migration, and a checker-gated
  untrusted-input API;
- many older APIs return `Option`, losing the location and reason for failure;
  executable sequentialization now returns a staged `SequentializationError`;
- separate path-dependency and clean pinned-v0.5.0 Lake consumers now pass;
  the path dependency executes the v0.5 sequentializer and consumes its
  equivalence theorem, while the pinned consumer protects the v0.5.0 API. A
  third clean consumer installs the exact public v0.6 candidate Git commit
  and typechecks the retained-boundary, packed-witness, soundness, and
  persistent-normalization APIs. A fourth clean consumer pins the exact public
  `v0.7.0` tag and checks bounded canonical-key exactness, safe
  matching, fail-closed over-limit behavior, and executable
  sequentialization;
- the finite direct-equivalence search is now proved complete on structurally
  well-formed left certificates, including repeated labels and link reordering;
- CI parses `#print axioms` for the maintained public declaration set and
  locks exact standard-three, axiom-free, `propext`-only, and
  `propext`/`Quot.sound` boundaries; rolling totals and the exact checkpoint
  receipt live in [current status](current-status.md);
- the two public graph-acyclicity transport theorems and the two exact
  first-frontier/prefix-path theorems are separately locked to exactly
  `propext` and `Quot.sound`, without `Classical.choice`;
- the v0.9 package builds with `warningAsError`; the current full
  build emits zero Lean warnings, so future linter regressions fail locally and
  in CI rather than leaking into downstream builds;
- the separate LeanProp trust boundary locks four theorems as axiom-free,
  fifteen dependent metatheorems to exactly `propext`, and four theorems to
  exactly
  `[propext, Quot.sound]`;
- an initial compatibility policy and v0.2-to-v0.3 migration suite now exist;
  long-term API documentation and deprecation automation are still incomplete;
- a curated public declaration manifest now generates types and docstrings
  from the kernel-loaded environment, fails on missing/unsafe declarations,
  and is drift-checked in CI; an external Lake consumer tutorial covers
  checking, parsing, both proof directions, and precise scope boundaries;
- a deterministic 5,000-case native parser fuzz gate covers truncation,
  deletion, replacement, insertion, malformed fields, and excessive formula
  nesting; broader coverage-guided fuzzing remains future hardening;
- bounded reconstruction now has structured public diagnostics and is compiled
  by the clean path-dependent consumer; the qualified default envelope is
  CI-stressed, while a process-level cancellation/deadline API remains future
  integration work;
- the LeanProp wire boundary has an independent deterministic 5,000-case
  mutation gate plus JSON Schema fixtures and a SHA-256 manifest over 1,600
  Lean-emitted labeled records; every accepted wire value now retains an
  indexed derivation and exposes universal `sound`. A clean consumer pins the
  exact public `v0.6.0` tag and typechecks that API, including the structural
  normalizer;
- a 291-case depth-2/3/4 native CI workload now has a 45-second catastrophic
  regression budget; it explicitly does not establish favorable asymptotics,
  and the measured depth-4 cost remains a library-readiness limitation;
- the focused baseline is a Python experiment component, not a Lean library
  module;
- a deterministic 1,000-task matched algorithmic experiment now compares
  focused search, direct atom-matching net generation, and one-edit repair;
  all 930 distinct accepted outputs pass the Lean checker and runtime
  sequentializer, while all 930 distinct mutations are rejected. The supplied
  formula skeleton, positive derivation-first corpus, mostly unique atom
  labels, and distance-one mutations prevent this from establishing the
  research hypothesis;
- a 180-task held-out model experiment is preregistered with balanced
  depth/label/polarity strata, exact implementation/prompt/corpus hashes,
  negative atom-balance witnesses, and reference repair distances two/three;
  no task-specific model response or formal aggregate existed at registration.
  All 360 calls are now frozen, but the original runner failed to finish
  algorithmic scoring in 120 minutes because its wall-clock budget lacked a
  hard interrupt. A public amendment preserves every frozen input/response
  while adding process isolation and hard deadlines. Final scoring is now
  complete: model direct solved 117/180 overall but only 27/90 positives,
  model repair solved 2/180, proof-net generation solved 160/180 with 20
  depth-4 negative hard timeouts, focused search solved 85/180, and the
  constructed distance-ordered repair baseline solved 180/180. This does not
  establish a general model or proof-net advantage.

## Current usability boundary

It can currently be used for:

- constructing MLL certificates in Lean;
- checking structural and Danos-Regnier switching correctness;
- using the general sequentialization existence theorem inside Lean proofs;
- running the proof-bearing executable sequentializer on accepted certificates,
  with kernel-checked universal success for the documented certificate model;
- generating/desequentializing the first-order derivation syntax and retaining
  only checker-accepted results;
- regenerating the labeled v0.2 corpus;
- producing stable v0.3 cache/dataset keys across bounded vertex renamings;
- deciding exact `ProofNetEquivalent` pairwise identity between
  checker-accepted certificates through a checked API;
- computing an experimental typed canonical code whose equality is kernel
  proved equivalent to `ProofNetEquivalent`, while retaining
  `sameProofNet?` as the performance-qualified pairwise identity API;
- parsing and migrating the bounded `proofnet-canonical-key-0.1` wire, with
  exact equality under its seven-link generation ceiling, 1,000 generated wire
  properties, 5,000 malformed-key fuzz cases, and a measured 1/4/7-link
  benchmark;
- computing, parsing, migrating, and safely matching the
  non-factorial `proofnet-canonical-key-0.2` key, with an exact iff theorem,
  a 1,000-case differential oracle audit, 1,000 additional mixed
  derivation-generated accepted nets, 5,000 malformed cases, and a measured
  qualification through 145 links;
- running the focused-search comparison baseline;
- experimenting with the proof-bearing bounded/tagged `NEXTAXIOM`, dynamic
  Figure-5 start, and independent delayed raw-age state primitives, including
  their proved structural source-singleton, per-call tag/trace, strictly
  threaded touched-set, `σ` partition, operational inactive-boundary waiting
  domain, typed initial/later reservations, and local pop/mark/new pipeline,
  while treating search failure as inconclusive; local exact
  `concl`/`nop`/`wait`/`forward`/`UnifyEmpty`/`UnifyOne` are now present; the
  current state-only invariant
  is preserved through the common prepared prefix plus `concl`/`nop` and every
  successful deterministic/executable `new`, `wait`, `forward`, bounded
  `UnifyEmpty`, and strict-singleton `UnifyOne`; the exact
  occurrence-provenance forest is integrated for
  empty/init and each of those successful steps. Wait additionally preserves
  exact positional waiting spans
  and combined queue ownership without constructing the delayed par.
  Forward also has an independent Boolean-free direct rule and exact
  executable correspondence. Bounded `UnifyEmpty` and strict-singleton
  `UnifyOne` have direct rules and exact correspondence, and successful
  typed/executable bounded steps preserve the
  complete occurrence-exact `SchedulerInvariant`. The local arbitrary-payload
  fold and atomic `UnifyPayload` composition are present with exact
  correspondence and `1 + payload.length` accounting; the latter now preserves
  `ComponentForestProvenance` and the full `SchedulerInvariant` on every
  successful step from a full input invariant. Conditional applicability under
  `UnifyPayloadEnabled` is also proved. Pure input-only `ConclEnabled`,
  `NopEnabled`, `WaitEnabled`, and `ForwardEnabled` now similarly imply
  executor success plus full-invariant preservation; their submitted-par
  trichotomy is deliberately local and not a scheduler partition. Exhaustive
  reachable-branch enabledness, later-state totality, and intermediate-state
  invariance remain absent. A canonical
  priority dispatcher and proof-carrying certified history now integrate every
  implemented successful rule family. Its canonical tag augmentation lifts
  exact init/`new` touch provenance, global submitted-slot non-reuse, and exact
  reservation-event counting through stable branches: recorded slots have
  length equal to final `nextAge`. A public whole-history oriented route and
  unconditional reachability are not yet lifted. The
  local `wait` cons has a state-only ownership theorem only from a supplied
  `SchedulerInvariant`.
  Exact init/new reachability, tag history, the retained `sigma` commitment
  spine, local raw-mark-to-reservation endpoint anchors, and certified full-rule
  successful traces are present. One adjacent cross-component path and its
  explicit-premise target-avoidance refinement are present, and supplied
  adjacent callbacks compose across every positive-length retained interval.
  The strict conclusion law is available from both explicit separation
  invariants, and strictly older edge/interval callbacks now follow when the
  scheduler invariant is also supplied. Any ledger event whose current
  representative is strictly below the candidate now splits at its immediate
  predecessor, so its positive prefix is composable. The queued-head half has
  empty/init, stable, successful New, and
  structurally discharged Wait/Forward/UnifyPayload preservation, plus global
  availability for every structurally well-formed canonical history. The
  independent mate-region and raw-mark invariants, unconditional stored-left
  equal-boundary avoidance, queue origin, raw-seam
  discharge, and unconditional full-rule reachability are not, so
  together these are not a complete scheduler API;
- reproducing the first deterministic 1,000-task matched experiment and
  validating its hashed artifacts.
- auditing the frozen 180-task model experiment, amendment, raw responses,
  results, and final Lean-verification hashes without calling the model.

It should not yet be presented as:

- a general Lean/mathlib proof assistant extension;
- a performance-qualified executable sequentializer beyond the documented
  unit-free, cut-free MLL certificate model;
- a pure-complete or Guerrini-linear flat worklist; general checker-accepted
  sequentialization is complete, but the flat fast path still relies on the
  recursive fallback for its exact decision;
- a confluence-checked scheduler: exact-state and structural-only formulations
  have counterexamples, while the marked-domain/thread-partition candidate has
  no committed reproducible audit or theorem;
- a complete isomorphism-canonical proof identity library;
- an arbitrary-isomorphism or conclusion-reordering canonicalizer; the new
  key is exact only for the explicitly documented `ProofNetEquivalent`
  relation and remains subject to its independent output-size envelope;
- evidence that proof-net generation reduces search redundancy beyond the
  committed experiment's narrow, explicitly biased controlled setting.

## Release gate for library readiness

The macro goal may call the project a mature library only after all logical
gaps above are closed, a clean downstream Lake consumer passes on Windows and
Linux, JSON round trips have structured diagnostics and fuzz coverage, public
API docs and
compatibility rules are published, performance limits are measured, and the
matched algorithmic and model-backed experiments report their results whether
positive or negative. Both controlled runs are now complete; the broader-
logic/corpus, hard checking/sequentialization performance, adversarial
large-key qualification, and broader Lean/tactic integration remain open. The
v0.9 release and exact-tag consumer gates are closed.
No external adoption or independent research validation is currently verified;
the v0.10 development branch therefore remains a qualified research library,
not a mature broad proof-net library.
