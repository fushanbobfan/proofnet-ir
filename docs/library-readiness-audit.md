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
   canonical history, the complete invariant, and that exact run. Deriving the
   run/route from every correct certified-reachable shallow `NewGuard`, then
   proving tensor-branch exhaustiveness, progress, and completeness, remains
   open.
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
   fuel are discharged structurally. This is not yet a library-level progress
   result: no theorem excludes blockers from correct canonical histories, and
   endpoint queue absence plus fresh capacity are still downstream of the
   positive run. No new reachability, enabledness, totality, completeness,
   fallback-removal, or complexity guarantee follows.
   `PriorityEnabled` records the selected
   witness and all earlier negatives, is equivalent to the matching
   `DispatchStep`, characterizes exact selected-kind success and dispatcher
   failure, and has a unique selected kind. A completed reachable `[[]]`
   regression proves that the full invariant need not enable any branch, so
   these theorems do not establish intended-state exhaustiveness,
   nonterminality, global progress, or worklist completeness.
   `ProofNetIRNewProgressAudit.lean` now adds a finite, executable audit of the
   specific reachable-state gap around `NewGuard`: it considers only states
   reached by successful initialization and the canonical dispatcher and hard
   fails on an exact guarded `new? = none` witness. The default CI corpus is
   seed 0 at depths 0 through 4, every formula start, and six labelled ordering
   variants (30 certificate cases, 23,184 reachable states, 6,198 guarded
   successes); the opt-in depth-5 extension reaches 96,444 states and 26,658
   guarded successes. Both observed zero guarded failures, inverse guard
   mismatches, cycles, and fuel truncations. Deep acceptance uses
   `unificationCheck` and the kernel theorem `unificationCheck_eq_check`, while
   the 18 cases at depths 0 through 2 also run the direct all-switchings
   checker. This finite receipt does not close input-only `new` sufficiency,
   intended-state exhaustiveness, progress, totality, or completeness.
   `SequentialFigure7TagHistory.lean` now derives a branch-aligned augmentation
   from that exact history and from certified dispatcher reachability. It proves
   exact current-tag provenance, stable tags for all five non-`new` branches,
   strict fresh growth for `new`, touched-set separation, touched-history
   independence at a common concrete state, and history-wide submitted-slot
   `Nodup`. The state-only invariant still admits same-sized forged tag arrays;
   this checkpoint requires proof-carrying history evidence and does not
   separately prove the concrete all-true replacement unreachable.
   Reservation-event-count and whole-history oriented-route generalization,
   exhaustive guard classification,
   unconditional full-rule reachability,
   closing-par scheduler-order exclusion, correct-state
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
- CI now parses `#print axioms` for 717 declarations: 460 public MLL
  logical-boundary theorems must retain exactly `propext`,
  `Classical.choice`, and `Quot.sound`; it separately locks 25 axiom-free,
  110 `propext`-only, and 122 `propext`/`Quot.sound` boundaries;
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
  Exact init/new reachability and tag history plus certified full-rule
  successful traces are present, but unconditional full-rule reachability and
  the required global queue/route commitments are not, so together these are
  not a complete scheduler API;
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
