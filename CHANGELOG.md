# Changelog

## Unreleased

- threaded coordinate-exact scheduler occurrences through the complete
  backward-chord recursion required by the remaining v0.10 contradiction.
  `SchedulerOccurrence` distinguishes a
  visit by `(segment step, in-segment offset, DirectedEdge value)`;
  `tagSchedulerFamily` is proved duplicate-free even when erasing its tags
  produces repeated edge values. Membership now inverts to the exact original
  segment and offset, and every surviving tag retains its classified scheduler
  provenance through a proof-relevant cyclic descent. A positioned obstruction
  is recomputed after every cut from the surviving tags; Lean proves that its
  omitted right occurrence is the zero-offset visit of its simple source
  segment and retains the exact offset of its left occurrence.
  `CyclicIntervalCut.map` erases tagged cuts, while
  `CyclicIntervalCut.exists_lift_map` positionally lifts an edge-level cut from
  its stored append decompositions. This lift is existential, not a value-based
  canonical choice. The existing graph chord theorem is consequently lifted
  through exact tags, well-founded recursion reaches a terminal forward cusp
  without coordinate drift, and the full tagged descent begins at the original
  scheduler family. A coordinate-exact reverse-shell relation is also proved
  to erase to the graph relation and to induce a tagged descent. Graph-level
  reverse-shell normalizations now lift positionally from their exact
  singleton/middle/singleton decompositions; repeated edge values never select
  a scheduler visit by equality alone. The terminal complement cut and every
  shell are consequently lifted to tags, normalized cores compose their exact
  descent with the original family, and every recursively exposed terminal
  cusp is recomputed on the surviving coordinates. Well-founded tagged
  nesting reaches an empty-core or tagged closing-par terminal base with one
  complete descent back to the original scheduler family. In the empty-core
  case every exact visit now has a concrete distinct reverse-valued partner
  from a different scheduler step; same-step pairing is excluded by the
  simple path's duplicate-free edge indices. Turning this finite cross-step
  nesting into the final order contradiction, and excluding the closing-par
  base, remain open;
- hardened the unfinished scheduler-nesting proof objects against existential
  witness drift. `SchedulerPositionedParObstruction` now retains exact linear
  decompositions for the two par occurrences inside the current cyclic
  interval and for their two distinct classified segments inside the original
  scheduler family. The terminal forward-cusp object is indexed by that same
  positioned witness, so its head, last occurrence, common conclusion, cusp,
  and scheduler positions cannot come from different par links. The terminal
  nesting base no longer stores independent duplicate located/positioned
  witnesses: both the outer cusp and a nonempty closing core project from
  their single proof-relevant witnesses. This repairs the representation used
  by the still-open base-case contradiction; it does not claim that the
  empty-core or closing-par bases have yet been excluded;
- added proof-relevant cyclic reverse-shell normalization for an internally
  nonbacktracking closed traversal. The normalization retains the exact
  decomposition `opening ++ normalized ++ reverseTraversal opening`, proves
  the exact length equation, and never replaces positional nesting by mere
  edge membership. Applying it to a terminal scheduler par-cusp complement
  now exposes a finite normal-form core with inherited occurrence-indexed
  scheduler provenance. A nonempty core carries both the exact
  `NormalizedNonemptyParObstruction` and its scheduler-located counterpart;
  its closing boundary is either cusp-free or a classified nontrivial par
  cusp. In the cusp-free case Lean recursively extracts a strictly nested
  terminal forward cusp with a transitive cyclic-interval descent trace.
  Well-founded recursion therefore reduces every fully reflexive flipped
  dependency family to one of two finite scheduler-located base cases: an
  empty shell core or a nontrivial closing-par core. Pure-worklist completeness
  still requires excluding those two bases by the reference-switching or
  scheduler-order contradiction;
- added a generic cyclic scheduler-subarc state carrying a closed full-graph
  walk, internal and closing cusp-freedom, forward reference retention,
  pointwise indexed flipped-segment provenance, and the exact
  scheduler-located par obstruction. Lean now rotates any such state to the
  omitted-right occurrence and cuts at retained-left. A backward retained-left
  starts a nonempty closed cusp-free suffix which is strictly shorter and
  retains every state invariant; correctness re-extracts and scheduler-locates
  the next exact par obstruction. Each step stores the exact larger-list
  rotation and smaller contiguous interval in a proof-relevant cyclic-interval
  descent trace. Well-founded recursion on traversal length therefore closes
  the entire backward branch and proves that every fully reflexive flipped
  dependency family reaches a terminal forward retained-left par-cusp interval
  together with its full order trace back to the original family. This does not
  yet turn that interval into the forbidden reference-switching cycle or strict
  nesting, so correct-state progress and pure-worklist completeness remain
  open;
- strengthened the terminal forward-cusp proof object so “interval” is no
  longer only commentary: it retains the exact cyclic rotation, the
  complementary contiguous interval, and the nontrivial left/right par cusp.
  The complement is kernel-proved nonempty, closed, internally cusp-free, and
  strictly shorter. Any cusp at its closing junction is now proved to be only
  the exact last/first immediate reversal; a second nontrivial par cusp there
  would contradict the inherited boundary cusp-freedom. This complement now
  feeds the proof-relevant reverse-shell normalizer and finite nesting-base
  extraction described above;
- proved that every residual core in the fully cancelling simple dependency
  cycle is nonempty. If a core were empty, its backward source incidence and
  the cyclic successor's backward source incidence would consume the same
  exact premise occurrence. The structural one-parent theorem would then
  identify the two stored par links and hence two adjacent waiting
  conclusions, contradicting prefix injectivity in the at-least-two-node
  dependency cycle. This argument is occurrence-indexed and therefore cannot
  exchange equal-valued parallel edges. Each core also inherits exact
  no-immediate-reverse from its containing dependency segment after removing
  the source and frontier boundaries. The deterministic active residual-core
  family now packages both nonemptiness and internal nonbacktracking. Lean
  composes that exact indexed family into a nonempty closed full-graph walk,
  with the final core returning to the first core's exact source-premise base;
  every occurrence in that walk is retained by the reference switching.
  Cyclic normalization cannot leave a nonempty reduced residue, because that
  would be a nonempty cyclically nonbacktracking walk in the reference
  switching tree. The core-only normal form is therefore empty, and
  proof-relevant normalization localizes an exact reversal to a cyclic
  junction between two nonempty internally reduced cores. Lean now reindexes
  that cyclic list witness to one exact dependency step, preserves both active
  core witnesses, and combines it with cyclic frontier/source chaining. The
  two consecutive dependency segments therefore contain the contiguous
  exact-occurrence word `inner, outer, outer.reverse, inner.reverse`; the
  containing segment's no-immediate-reverse proof also shows the inner and
  outer cancellation layers are nondegenerate. Both original occurrence-
  indexed full-segment witnesses are retained at that same step. Lean
  reconciles each `core ++ frontier` with its exact retained reference-prefix
  walk, preserving compacted index, stored edge, orientation, and target
  pointwise, and proves that the successor reference prefix starts with the
  inner occurrence's exact reverse. The remaining empty-branch obligation is
  to exclude this now path-exposed strict nesting by the exact switching-flip
  argument; pure-worklist completeness is still open;
- retained the occurrence-indexed full-segment decomposition through the
  finite dependency family instead of projecting immediately to endpoint
  classifications. In the fully cancelling empty-normal-form branch, Lean now
  removes each segment's exact backward source incidence and forward reflexive
  frontier, selects the deterministic `tail.dropLast` residual core, proves
  that its endpoints carry one live union-find token, chains every frontier to
  the cyclic successor's exact source incidence, and proves positionally that
  every residual-core edge has both endpoints assigned before the first
  marked-to-unmarked boundary. The resulting active residual-core family is a
  stronger input to the remaining multi-par switching-flip/nesting
  contradiction; that global contradiction and pure-worklist completeness are
  still open;
- retained the exact first marked-to-unmarked scheduler frontier in every
  waiting-par dependency, including assignment of every preceding path
  endpoint. Lean now proves that any forward occurrence entering an unassigned
  vertex is this unique frontier, and that a frontier targeting another
  registered waiting par is reflexive: its formula-premise chase has no hidden
  nontrivial tail. In the fully cancelling simple dependency cycle, every
  source reverse is consequently paired with the unique cyclic predecessor's
  exact last occurrence, and every segment ends at its reflexive frontier.
  This narrows the empty normal form to a multi-node cycle of retained
  reference paths and waiting-par incidences; excluding that remaining nesting
  is still open;
- strengthened the empty-normal-form scheduler obstruction from an arbitrary
  repeated dependency segment to the first repeated conclusion: every chain
  position before the closing endpoint is injective, the retained indexed
  segment family is a simple dependency cycle, the localized cancellation
  crosses two distinct waiting pars, and a singleton empty cycle is
  kernel-excluded. The positive counterexample gate now covers 7,200 reordered
  derivation-generated certificates from 1,200 seeds at depths zero through
  seven, reaching 447 formulas and 319 links with no eager or worklist miss;
  this remains finite evidence rather than the universal completeness proof;
- added an opt-in Windows wrapper for the independent mathematics audit. It
  preserves the byte-frozen preregistered `audit_v010.py` and, only after
  application-control error 4551 for a known generated audit executable,
  launches the same Lean source through `lake env lean --run`; all other
  subprocess failures still fail closed;
- began the scheduler-coverage proof layer for the event-driven worklist:
  a kernel-checked connective status relation distinguishes real queue
  membership, fired conclusions, idle premises, registered waiting pars, and
  tensor deadlocks; initial arming covers every concrete connective. The
  consumer-table fold now has an exact no-missed-dependency theorem, and
  sound queue flags prove that deduplicated single/batched enqueues cannot
  silently lose work. Coverage is preserved by dependency fan-out, waiting
  registration, and whole waiting-par requeue. Real queue and waiting
  registries are proved in-bounds, waiting deduplication is separately sound,
  and popping a real head preserves queue soundness/bounds after clearing
  that exact flag. A pending-premise frontier invariant now avoids the false
  claim that consumed but permanently marked premises remain exposed; under
  this exact invariant, guard-ready par/tensor component construction is
  total, and processing the popped connective always reclassifies it as
  fired, idle, registered waiting, or tensor-deadlocked. Every processing
  branch is also proved to preserve the executable abstraction contract, the
  ordered union-find forest, and formula consistency of every live partial
  derivation component. Structural ownership now proves unique premise
  parents and compound producers. Exact par/tensor frontier-transport
  theorems preserve every non-consumed occurrence, tensor transport accounts
  for representative merging, and each new conclusion is exposed in the
  replacement component. Eager axiom initialization establishes this
  pending-premise coverage from the canonical empty state, every processing
  branch preserves it, and the complete production fuel-bounded run carries
  the bundled abstraction/forest/component/frontier invariant. Popping now
  preserves scheduler coverage for every non-head connective, successful par
  and tensor events transport those classifications through exact dependency
  fan-out, tensor union is proved unable to split an old shared-token class,
  and the processed head closes the temporary coverage hole whenever it is a
  submitted connective. Reverse consumer-table provenance proves every
  dependency enqueue is a submitted connective, waiting registries contain
  only submitted pars, and every real queue head has exact connective
  provenance. The complete finite production run now carries bundled core
  correctness, scheduler coverage, flag soundness, carrier sizes, and
  queue/waiting provenance. Queue and waiting flags are now exact in both
  directions; both concrete registries remain duplicate-free through every
  enqueue, waiting registration, requeue, pop, processing branch, and finite
  production run; and each registry is proved to have length at most the
  submitted-link carrier. Exact transition-level insertion balance is now
  proved for single and batched enqueues, dependency fan-out, waiting
  registration/requeue, firing records, every processing branch, successful
  pops, and finite production runs. From canonical initialization, link
  attempts plus the residual queue length is exactly the cumulative number of
  initial, dependency, and waiting-requeue insertions. Structural linear
  ownership now collapses every consumer bucket to at most one distinct link
  index, so each successful firing adds at most one dependency insertion.
  A proof-only distinct submitted-link firing history bounds successful
  firings by the link carrier; each tensor firing requeues at most the current
  duplicate-free waiting registry, itself bounded by that carrier. These
  source bounds prove all cumulative insertions fit the existing
  `n(n+4)+1` budget. A separate exhaustion theorem proves that any run with a
  residual queue consumed all fuel, and exact accounting therefore proves the
  canonical production queue is empty at the budget. At that genuinely
  quiescent state, scheduler coverage now converts every submitted but
  unfired connective into an explicit proof witness: an idle premise, a
  distinct-thread registered par, or a same-thread tensor deadlock. This
  removes hidden queued work and fuel exhaustion from the remaining progress
  argument. Structural source-link totality, assignment monotonicity from
  axiom initialization through the complete worklist run, and a
  least-formula-complexity choice now prove that an incomplete canonical run
  has a concrete submitted source whose premises are both assigned. This
  eliminates the idle-premise case and leaves exactly a distinct-thread
  registered par or a same-thread tensor deadlock. The abstract semantics now
  carries an active all-left reference subgraph and proves that every semantic
  thread is connected inside it after each start/forward/unify step, every
  finite execution, each concrete worklist processing branch, and the complete
  canonical run. For a declaratively correct certificate, a same-thread
  unfired tensor would close that active path with its two fixed tensor edges,
  producing an edge-simple cycle in the reference switching. Lean therefore
  excludes the tensor-deadlock branch and reduces every incomplete correct
  canonical run to one exact submitted distinct-thread waiting par. The
  converse active-component invariant is now proved as well: reachable
  markings are causally closed, every active retained reference edge remains
  inside one semantic token class, and an active reference walk between
  marked occurrences is equivalent to union-find thread equality. The final
  waiting-par witness is therefore strengthened with a kernel proof that its
  marked premises have no active reference walk. An occurrence-aware
  tree-edge-exchange theorem now proves more: flipping exactly that submitted
  par occurrence yields a reference-switching simple path between its
  premises which avoids the par conclusion. If the endpoints remain in
  different active components, Lean extracts a genuinely unmarked internal
  occurrence on this path, distinct from both premises and the par
  conclusion. A new occurrence-preserving first-frontier theorem now exposes
  an exact traversed reference edge from a marked source into an unmarked
  target, retains an entirely active prefix, and proves that the frontier
  source lies in the left premise's active component. Exact component/thread
  correspondence consequently identifies its token with the waiting par's
  left token. Reversing the path selects the last inactive frontier, proves
  that its marked target carries the waiting par's right token, and yields an
  exact ordered path decomposition with distinct left and right boundaries.
  The canonical obstruction now carries this two-sided bracket.
  Exact retained-edge/source-link lookup plus axiom initialization and causal
  closure now classify it as a forward premise-to-conclusion occurrence of a
  concrete submitted par or tensor. Quiescent scheduler coverage now refines
  the classified frontier further: a par either has its omitted premise
  unassigned or is registered with distinct live tokens, while a tensor has
  its opposite premise unassigned because correctness excludes the
  both-premises-marked deadlock. The same classification is now proved at
  both sides of the bracketed middle region. Cutting the suffix at its first
  unmarked-to-marked reentry now isolates a contiguous block whose
  intervening occurrences have two unmarked endpoints, and preserves exact
  scheduler classifications at both boundary orientations. The obstruction
  now retains the globally minimum-complexity unassigned waiting conclusion.
  Structural premise descent normalizes each oriented boundary to one of two
  exact alternatives: its target has formula complexity strictly above that
  global minimum, or the boundary itself is a concrete registered
  distinct-thread par. A separate strong-induction theorem now proves that
  every unassigned occurrence reaches a concrete registered waiting par by
  strict formula-complexity descent. Both orientations bracketing the first
  inactive block consequently have non-increasing waiting-par chase
  endpoints while retaining the exact path decomposition. This construction
  is now generalized to every registered waiting par: each source has an
  exact outgoing dependency witness containing its conclusion-avoiding
  reference path, marked-to-unmarked frontier, local scheduler obstruction,
  and terminal registered waiting par. Both dependency endpoints are proved
  to lie in the finite formula carrier. A chosen dependency chain of
  `formulas.size + 1` occurrences is therefore proved non-duplicate-free
  while retaining an exact dependency witness at every adjacent step. A
  further kernel theorem extracts concrete indices
  `earlier < later ≤ formulas.size`, equal endpoint conclusions, registered
  waiting evidence for every chain vertex, and every exact dependency witness
  in the resulting nonempty closed segment. At that intermediate stage this
  was only a cycle in the auxiliary waiting-dependency relation. The formula
  chase carried by every
  dependency now additionally retains every exact source connective and
  selected premise in a composable reflexive-transitive proof object; Lean
  proves non-increasing endpoint complexity and strict decrease for every
  nontrivial such path. Every formula-premise step is now lifted to its exact
  full occurrence-graph edge, traversed backward from connective conclusion
  to selected premise. A nontrivial chase therefore supplies a vertex-simple,
  all-backward, internally cusp-free graph path. A new state-indexed chase
  retains unassigned evidence for every visited occurrence, rather than only
  for its endpoints. The marked-to-unmarked frontier classifier now also has
  an occurrence-exact API retaining the concrete full-graph edge and
  orientation, while the former endpoint result is preserved as a
  compatibility projection. Each nontrivial dependency tail is proved not to
  immediately reverse that lifted frontier. A new exact-index all-left-mask
  classifier recovers the submitted axiom/tensor/par occurrence at the same
  full-edge position, including the fact that only the left par incidence is
  retained. Structural formula typing excludes an axiom at the formula-tail
  source, and unique producer ownership synchronizes the frontier link with
  the first tail link. Every nontrivial dependency turn is therefore
  kernel-classified as either a genuine par cusp with equal shared par colors
  or a tensor-colored free turn whose unique-color equality would force the
  excluded immediate reversal. The retained-walk lift now preserves stored
  edge values and orientations pointwise, and each segment propositionally
  binds its classified frontier and formula edge to the actual last prefix
  and first tail occurrences. This closes the parallel-edge gap in which
  endpoint-equal but occurrence-distinct edges could otherwise be classified
  on behalf of the concatenated walk. Every adjacent dependency in the finite
  closed segment now additionally carries one exact composable complete-graph
  walk: the reversed source-par left incidence, retained reference-prefix
  lift, and all-backward formula tail. A graph-generic concatenation theorem
  joins the selected finite family into a genuinely nonempty closed
  occurrence-aware `fullGraph` walk. Added the reusable exact-occurrence
  `Graph.EdgeWalk.NoImmediateReverse` predicate with duplicate-key,
  constant-orientation, and append lemmas. Every individual dependency segment
  now satisfies it: the source/prefix junction is excluded using the original
  simple path's avoided conclusion, the retained prefix inherits a
  reversal-invariant duplicate-free occurrence key, the actual frontier/tail
  junction uses the classified non-reversal witness, and the all-backward tail
  has constant orientation. The concatenated closed walk may still backtrack at
  an inter-segment junction or repeat edge occurrences. A junction-reversal
  theorem now proves that any actual reversal forces the preceding dependency
  chase to be reflexive; the nontrivial case is impossible because both
  boundary edges are backward. The witness is now occurrence-exact: the
  incoming full-graph edge is tied to the retained reflexive frontier and its
  same stored index is proved to be the next waiting par's source incidence.
  `Graph.EdgeWalk.cancelImmediateReverse` and the dependency-level cancellation
  theorem remove exactly that reverse pair while preserving both walk
  endpoints, every remaining occurrence, and the nesting witness; endpoint-
  equal parallel occurrences cannot be substituted. A terminating exact-
  occurrence normalization relation now repeatedly cancels internal pairs,
  rotates a closed walk when its last/first pair reverses, and returns a closed
  normal form whose surviving occurrences all came from the original walk.
  The result is either empty or cyclically nonbacktracking. The empty branch is
  intentionally retained because a nested out-and-back tree walk is a real
  counterexample to nonempty normalization. The cyclic normalizer now returns
  a proof-relevant tree recording every internal and rotated closing
  cancellation. Reduction-level, internal-normalization, and cyclic-
  normalization theorems prove that each source directed-edge value either
  survives or has the reverse orientation of the same stored edge in the
  source; consequently, if the cyclic normal form is empty, the reverse of
  every represented directed-edge value also occurs. This is exact-index
  membership, not a proved bijection between list positions. The scheduler-
  level normalized-walk theorem retains this trace and membership result. It
  additionally proves that every forward occurrence of the original
  dependency walk is reference-kept, and hence that every original edge index
  is reference-kept when the cyclic normal form is empty. This narrows the
  empty branch to a fully retained nested reference-tree walk. The normalized
  scheduler theorem now constructs the corresponding nonempty closed
  `referenceSwitchingGraph.EdgeWalk`, and the public
  `DeclarativelyCorrect.referenceSwitchingTree` theorem packages the exact
  reference graph's tree proof. Closed tree walks can still consist entirely of
  nested backtracking, so these facts do not exclude the branch. The
  proof-relevant cyclic normalization now also proves that a cyclically
  nonbacktracking input is a fixed point and that any nonempty input normalized
  to empty exposes an exact internal or cyclic-closing cancellation site in
  its original representation. A separate append theorem proves that if two
  individually nonbacktracking pieces contain an internal cancellation after
  concatenation, the cancelled pair crosses their unique junction. The
  scheduler theorem now retains the full selected segment decomposition as an
  index-aligned finite family, including every segment's nonemptiness,
  internal nonbacktracking, and endpoint classifications. It localizes the
  exact site to an adjacent or cyclic family junction and proves that the
  incoming occurrence is simultaneously the preceding dependency's retained
  reflexive end and the following waiting par's stored left incidence.
  Excluding that fully retained nesting remains open. Exact
  index/orientation transport now also preserves cyclic nonbacktracking through
  arbitrary occurrence masks, and every valid occurrence switching of a
  correct certificate is exposed directly as a tree. A par-pair-sparse
  nonempty normal form is therefore impossible. The remaining nonempty branch
  now produces one concrete par whose left and right exact occurrences both
  survive; because every forward occurrence is all-left retained, the omitted
  right occurrence is proved backward. Correctness still must exclude the
  exact empty nesting and transport local turn evidence around that concrete
  nonempty obstruction into a suitably classified edge-simple switching cycle
  or forbidden nesting. Thus
  scheduler fuel sufficiency and finite repetition must not be conflated
  with pure-worklist completeness;
- started `v0.10.0-dev` with an explicit proof plan separating independent
  unification-step semantics, scheduler coverage, worklist fuel sufficiency,
  correct-state progress/pure completeness, and the later sequential
  `NEXTAXIOM` whole-program cost theorem;
- added a proof-irrelevant `UnificationMarking` with bounded occurrence/token
  marks and a thread equivalence on a fixed `Nat` carrier, plus an independent
  inductive `UnificationStep` relation for Figure-5 start, forward, and unify.
  `tokenCount` allocates an initial segment of that carrier. Kernel theorems
  show that every abstract step uses a submitted link, marks its fired
  conclusion, and never decreases the allocated-token count; the generated
  API and exact axiom audit include this new boundary;
- found and repaired a genuine development-semantics bug before release: the
  first `FreshExtension` definition omitted carrier elements above the fresh
  token, so global reflexivity made every abstract start step impossible.
  Fresh allocation now preserves the fixed-carrier equivalence relation and
  separately requires the newly allocated carrier element to be isolated
  from every old token. `freshExtension_equivalence` is a kernel-checked
  regression guard for this boundary;
- distinguished raw token identities from semantic thread equivalence in the
  abstract forward/unify rules: an executable representative token may label
  a new conclusion when it belongs to the required premise thread, rather
  than being numerically identical to the premise's originally assigned
  token;
- added the executable-state abstraction boundary:
  `UnificationState.Abstractable` states exact mark-array size plus
  occurrence/token and representative bounds,
  `toMarking` forgets arrays, derivation components, counters, and scheduler
  data, and three axiom-free projection theorems lock raw marks, parent-count
  allocation, and representative equality to the independent semantics. The
  all-unmarked initial state satisfies the bounds internally, and an
  axiom-free theorem shows every yielded representative is allocated;
  representative idempotence is now explicit, and a public state-update
  theorem proves that marking an in-domain conclusion with an allocated token
  preserves the abstraction contract. A second theorem proves this concrete
  update refines the independent forward rule under its exact executable
  guards. Axiom-free witness theorems now recover the raw mark behind every
  successful representative lookup and place that representative in the same
  semantic thread. Identity-parent invariants now prove start preservation,
  global representative identity, fresh-token isolation, and exact
  `startMarking` refinement;
- added observation equivalence for executable states that agree on exactly
  `marks` and `parents`; proved it preserves `Abstractable` and yields the same
  independent `UnificationMarking`;
- factored the exact par guards into `forwardToken?`, proved every successful
  result refines `UnificationStep.forward`, and kernel-checked that the real
  `firePar?` path including component/frontier construction is observation-
  equivalent to that verified update. The real `startAxiom?` path now reuses
  the verified start update, exposes both successful guards, and is proved to
  refine `UnificationStep.start`;
- restated `MergeExtension` as the equivalence closure of the two selected
  classes and proved that it is an equivalence relation for every old thread
  equivalence;
- found a second development-invariant gap with a kernel-checked minimal
  counterexample: the previous bounds/idempotence-only `Abstractable` contract
  admitted `parents = #[1, 0]`, whose fuel-limited representatives look
  idempotent even though a requested root merge need not change the cyclic
  array. Added `OrderedParents`, requiring every non-root pointer to decrease,
  and proved representative nonincrease, allocation bounds, fuel stability,
  and idempotence from this forest invariant. The invariant is now preserved
  by initial axiom setup, start, par/forward, tensor parent updates, whole eager
  passes, and arbitrary saturation prefixes;
- factored tensor guards into `unifyTokens?` and tensor token updates into
  `mergeConclusion`; proved ordered-forest and full `Abstractable`
  preservation for the update, and proved the real `fireTensor?` path is
  observation-equivalent to it;
- proved the exact ordered union-find update theorem on allocated tokens and
  on the full fixed `Nat` carrier: pointing a larger root at a smaller root
  changes `SameThread` precisely by `MergeExtension`, while unallocated
  carrier elements remain singleton classes. `MergeExtension` is also proved
  invariant under equivalent class representatives and under swapping its two
  selected classes;
- proved successful `unifyTokens?` execution refines exactly one independent
  `UnificationStep.unify`, including raw premise marks, distinct premise
  threads, output-thread membership, unchanged allocation count, exact
  conclusion marking, and exact global thread relation. The real
  `fireTensor?` component-building path inherits this refinement through
  observation equivalence;
- added the independent reflexive-transitive `UnificationExecution` relation
  and proved that every real connective firing, complete eager pass, and
  finite eager-saturation prefix preserves the abstraction contract and is
  simulated by such an execution. These are implementation-soundness results;
  scheduler progress and pure worklist completeness remain separate open
  obligations;
- proved the whole successful eager token-semantic run refines one independent
  execution, starting from the empty marking, traversing every submitted axiom
  start, and continuing through the bounded saturation phase. Identity-parent
  preservation across the complete axiom phase supplies fresh-token isolation
  at every start step;
- added `UnificationComponent.FormulaConsistent` and the state-wide
  `ComponentsFormulaConsistent` invariant, requiring every live partial
  derivation to infer exactly the certificate formula labels on its exposed
  occurrence frontier. Kernel proofs cover the actual axiom, par, and tensor
  component constructors, component replacement/retirement, whole axiom
  initialization, complete eager passes, arbitrary saturation prefixes, and
  the complete successful eager run. The final independent derivation verifier
  remains an additional fail-closed boundary;

## v0.9.0 - Graph semantics and checker-free correctness

- started `v0.9.0-dev` by exposing `Graph.Acyclic` as absence of an exact
  stored-edge `EdgeSimpleCycle`, including genuine length-two cycles from
  parallel edge occurrences;
- proved `Graph.IsTree.acyclic`, added positive and negative compile-time
  regressions, generated public API documentation, and expanded the locked
  MLL trust boundary to 46 theorems;
- retained the converse `Bounded ∧ Connected ∧ Acyclic → IsTree` as an
  explicit finite-multigraph forest-count obligation rather than silently
  assuming the current edge-count equation;
- removed all extant Lean linter warnings and enabled package-wide
  `warningAsError`, turning future warning regressions into build failures;
- proved that exact directed-edge occurrences, edge-aware walks, simple
  multigraph cycles, and `Graph.Acyclic` transport through bounded bijective
  vertex renamings; exposed the resulting acyclicity equivalence in the
  generated API and locked both public theorems to exactly
  `[propext, Quot.sound]`; the path-based downstream consumer compiles both
  transport directions and executes successfully;
- completed the finite-multigraph forest converse without assuming the old
  edge-count equation: shortest-path parent edges form a canonical spanning
  tree, every extra stored edge closes an exact occurrence cycle, and
  acyclicity therefore gives `|E| + 1 ≤ |V|`; together with the connected
  lower bound this proves
  `IsTree ↔ Bounded ∧ Connected ∧ Acyclic` and brings the locked public MLL
  trust boundary to 48 theorems;
- added an exhaustive occurrence-aware cycle oracle over exact directed-edge
  traversals, proved its traversal validator sound and complete, proved
  `Graph.isAcyclic = true ↔ Graph.Acyclic`, and derived
  `Graph.isTreeViaAcyclic = Graph.isTree`; self-loops, both orientations of
  parallel edges, a triangle, a disconnected forest, and a tree are covered
  by executable regressions. The oracle is explicitly exponential and raises
  the locked classical public MLL trust boundary to 52 theorems, with the two
  traversal-level theorems separately locked to
  `[propext, Quot.sound]`;
- separated the factorial canonical specification module from the executable
  sequentializer dependency and added `Certificate.verifyDerivation?`: a
  proof-bearing verifier for a supplied cut-free derivation that checks only
  structural well-formedness, inference/desequentialization, and the
  non-factorial intrinsic canonical code. It never enumerates input
  switchings or vertex permutations; Lean proves soundness and completeness
  relative to structural well-formedness plus exact `ProofNetEquivalent`
  desequentialization, with downstream-consumer and negative malformed-input
  regressions, plus 250 generated derivations and the same 250 certificates
  after reversing every stored link list;
- added `Certificate.reconstructDerivation?`, a fuel-bounded automatic
  terminal-par/splitting-tensor reconstruction path whose executable
  definition never calls `Certificate.check` and never enumerates switching
  graphs or vertex permutations. Every returned value carries an accepted,
  exactly `ProofNetEquivalent` derivation output; Lean proves universal
  completeness for every reference-checker-accepted unit-free cut-free MLL
  certificate and the exact Boolean theorem
  `reconstructsDerivation = check`. The current implementation still
  backtracks over terminal-rule candidates and repeated-label boundary
  orders, so no polynomial or linear complexity claim is made. The existing
  291-case native benchmark now measures both paths and recorded
  `reconstruction_ms=1752` versus `sequentialize_ms=6680` in the current
  Windows run under the unchanged 45-second aggregate budget. A separate
  CI-gated 1,000-case audit agrees with the reference checker on exactly 250
  positives and 750 deterministic malformed mutations in 413 ms under a
  15-second budget;
- optimized checker-free reconstruction with a structure-guided fast path
  that aligns repeated boundary occurrences using vertex-number-free
  formula-tree/axiom profiles, orders inverse-rule candidates independently of
  link storage, defers equivalence verification until the completed tree, and
  constructs the exhaustive repeated-label fallback only after the preferred
  candidate fails. The original proved exhaustive path remains the
  completeness fallback and every fast result still passes
  `verifyDerivation?`, while structurally invalid inputs now fail before
  inverse-rule search, so the exact Boolean theorem is unchanged. A new
  CI-gated 18-case skewed/balanced/alternating repeated-label suite includes
  reversed links, reaches 126 formula occurrences, and includes a 22-conclusion
  repeated-boundary case; the recorded Windows run completed in 34,416 ms
  under a 45-second budget. No polynomial or linear worst-case claim is made;
- added the fail-closed `reconstructDerivationWithinLimits` public API and
  structured `ReconstructionLimits`/`ReconstructionError` types. The qualified
  128-formula/96-link/24-conclusion envelope is checked before search and the
  bounded path never invokes exhaustive formula-order fallback. Lean proves
  every bounded success has the complete soundness contract, is accepted by
  the reference semantics, and lies in the complete unbounded decision's
  accepted set. Limit and heuristic errors remain explicitly inconclusive;
  the clean downstream consumer compiles and executes the bounded API;
- corrected the bounded execution path so that the preceding resource claim
  is true in code, not only documentation: reconstruction now takes an
  explicit alignment policy, the unbounded complete path retains exhaustive
  `matchingFormulaOrders`, and `reconstructDerivationWithinLimits` uses a
  preferred-only policy that never constructs that factorial family. All 18
  qualified stress cases still succeed, recording 31,633 ms under the
  unchanged 45-second budget;
- added an exhaustive executable colored-cycle oracle over exact full-graph
  edge occurrences. Lean proves its local traversal test, cyclic cusp test,
  witness search, and `Certificate.isCuspAcyclic` decision equivalent to the
  proposition-level `CuspFreeTraversal`, `CuspFreeCycle`, witness, and
  `CuspAcyclic` contracts. Declarative/reference-checker correctness implies
  oracle acceptance. This is deliberately an exponential differential
  specification;
- proved the exact acyclicity half of the reverse colored correctness bridge.
  Masked walks and simple cycles now lift to their original stored occurrences;
  structural producer ownership and one-choice-per-par masks rule out every
  local and closing cusp in a retained cycle. Consequently, for every
  structurally well-formed certificate,
  `CuspAcyclic ↔ all occurrence-order switchings are Acyclic`. This theorem
  distinguishes parallel equal-valued edges by list index. It does not yet
  promote acyclicity to the connected tree property; the connectedness/
  contraction bridge and a non-enumerative implementation remain open;
- factored the remaining logical obligation exactly. Lean now proves both
  `DeclarativelyCorrect` and `check = true` equivalent to structural
  well-formedness, `CuspAcyclic`, and
  `AllOccurrenceSwitchingsConnected`. Retained subgraphs inherit structural
  bounds, the colored theorem supplies every switching's acyclicity, and
  edge-list permutation transports the resulting trees back to the public
  switching representation. Thus the only remaining all-switchings
  correctness quantifier is connectedness;
- completed that connectedness bridge. A finite maximal-acyclic-extension
  proof establishes
  `Bounded ∧ Acyclic ∧ |E| + 1 = |V| → Connected`; exact switching selections
  retain a common edge count, so structural well-formedness plus
  `CuspAcyclic` makes universal switching connectedness equivalent to one
  deterministic all-left `ReferenceSwitchingConnected` graph. Consequently
  Lean proves
  `check = true ↔ StructurallyWellFormed ∧ CuspAcyclic ∧
  ReferenceSwitchingConnected`;
- added `Certificate.compactCheck`, which executes that compact criterion
  without enumerating switching graphs and is proved Boolean-equal to
  `Certificate.check`. Its current `isCuspAcyclic` phase is an exhaustive
  colored-cycle specification oracle, so this is not yet a linear-time or
  contraction-complexity claim;
- audited all ten pages and eight figures of Guerrini's LICS 1999 primary
  paper and mapped its axiom/start, unary-par/forward, and
  binary-tensor/unify rules to the current cut-free certificate syntax. Added
  a deterministic token-unification pass that carries partial derivations and
  independently verifies its completed tree. Lean proves every fast-path
  success checker-accepted. The exact `Certificate.unificationCheck` API
  short-circuits through this pass and uses the already complete
  checker-free sequentializer on a miss, yielding the theorem
  `unificationCheck = check` without switching enumeration. A new 1,500-case
  CI audit plus a structurally well-formed disconnected sentinel recorded 750
  positive hits, zero positive misses, and zero false positives in its first
  Windows run. A separate 6,000-case positive counterexample search spans
  1,000 derivation seeds, depths zero through five, six storage orders, up to
  111 formula occurrences and 79 links; its first run also found no fast-path
  miss. These finite searches remain empirical evidence. Pure fast-path
  completeness,
  ready/waiting worklists, and Guerrini's linear bound remain explicitly open.
  Added proof-relevant eager-scan statistics: Lean certifies at most
  `|links|` passes, exactly `passes * |links|` link visits, and therefore a
  quadratic link-visit ceiling. Frontier, union-find, verification, and
  fallback costs remain outside that scoped theorem. Added an event-driven
  premise-consumer worklist with a flat waiting-par set. Its candidate is
  independently verified; Lean proves fast-path soundness, exact fallback
  agreement with `check`, and the conservative `n(n+4)+1` link-attempt cap.
  The 1,500/6,000-case gates observed no worklist miss or false positive.
  `unificationCheck` now tries worklist, eager scan, then complete recursive
  reconstruction. Fuel sufficiency, pure completeness, `NEXTAXIOM`, and a
  full linear cost theorem remain open;
- published `v0.8.0` and changed the clean external consumer from candidate
  commit `925855572b316376445eafa36e043596f49637bc` to the exact public tag;
  Lake resolves that tag to release commit
  `09a21c328070d53e9fe26b09ed13d2650ab756db`;

## v0.8.0 - Intrinsic non-factorial canonical key

- added an intrinsic occurrence-forest canonicalizer that never enumerates
  link-list permutations. Lean proves exact formula-vertex coverage, exact
  link permutation, invariance, in-class representation, and canonical-form
  equality iff exactly `ProofNetEquivalent` on structurally well-formed or
  checker-accepted inputs;
- added the distinct `proofnet-canonical-key-0.2` /
  `proofnet-equivalent-intrinsic-v1` typed and JSON key, bounded native parser,
  schema and fixture, checked-v0.3 semantic migration, safe matcher theorem,
  API documentation, and path-consumer coverage. It removes v0.1's seven-link
  ceiling without reinterpreting any old bytes;
- added a 1,000-case differential comparison against the factorial v0.7 oracle,
  a separate 1,000-case mixed derivation-generated accepted-net audit, 5,000
  malformed intrinsic-key cases, and a measured four-case
  25/49/97/145-link benchmark. The aggregate intrinsic-key time was 120 ms on
  the recorded Windows run under a five-second budget; the independent
  one-million-character wire envelope remains fail closed;
- added a clean downstream Lake consumer pinned to candidate commit
  `925855572b316376445eafa36e043596f49637bc`; it installs from GitHub and
  typechecks exact intrinsic-key equality, safe matching, v0.3 migration, and
  generation above the retained v0.1 seven-link ceiling;

## v0.7.0 - Exact ProofNetEquivalent canonical key

- added `proofNetCanonicalFingerprint?`, the lexicographically least v0.3
  string in the complete finite `ProofNetEquivalent` canonical family; Lean
  proves totality, candidate membership, and forward invariance under
  `ProofNetEquivalent`. This JSON-string convenience remains forward-only
  because the project does not assume `Json.compress` injectivity;
- added an explicitly versioned, length-framed structural token encoder with
  kernel-proved injectivity and `proofNetCanonicalCode?`, the least structural
  code in the complete finite family. On structurally well-formed certificates,
  `proofNetEquivalent_iff_canonicalCode` proves code equality iff exactly
  `ProofNetEquivalent`; checker acceptance supplies those premises. This typed
  exact key still materializes the factorial family;
- added the separate `proofnet-canonical-key-0.1` /
  `proofnet-equivalent-v1` JSON contract, bounded native parser with structured
  errors, JSON Schema and real axiom-key fixture, v0.3-to-key semantic
  migration, and the untrusted-key-safe
  `proofNetEquivalent_of_matchesCanonicalKey` theorem. The wire passes 1,000
  deterministic encode/decode and reversed-link properties plus 5,000
  deterministic malformed-key fuzz cases;
- qualified the factorial wire generator with a hard seven-link ceiling checked
  before canonical-family evaluation. Bounded generation and parsed-key
  matching now fail closed above that limit, their equality has an exact
  `ProofNetEquivalent` iff theorem under the stated bound, and the CI benchmark
  covers 1-, 4-, and 7-link accepted certificates (5,065 total family
  candidates) under a separate 10-second budget;
- added a clean downstream consumer pinned first to the exact public candidate
  revision and then to the `v0.7.0` tag. It compiles the bounded-key exactness theorem, safe parsed-key
  matching, fail-closed over-limit behavior, and executable
  sequentialization independently of the working tree;

## v0.6.0 - Persistent LeanProp bridge

- began the conservative v0.6 LeanProp bridge without changing the MLL
  certificate/checker semantics: derivations are indexed by separate
  persistent and linear proposition contexts;
- added proof-relevant exchange data, explicit persistent weakening and
  contraction, no linear structural rules, and a theorem that the linear-axiom
  leaf count is exactly the linear-context length; the theorem uses exactly
  `propext` because proposition-valued contexts are dependent indices;
- added conjunction, implication, equality-rewrite, universal-instantiation,
  and existential-witness nodes plus an axiom-free total interpreter into Lean
  proof terms at arbitrary universes;
- added kernel-checked smoke templates for persistent duplication/discard,
  linear pairing/modus ponens, equality transport, universal instantiation,
  and existential introduction, including path-dependent downstream use.
- added a proposition-independent schema calculus and a universal
  instantiation theorem using exactly `propext` for its dependent proposition
  indices, plus a deterministic 600-template corpus across six
  persistent/linear rule strata and a CI uniqueness/size gate;
- added an unindexed raw-schema checker with nine stable path-aware error
  categories and a theorem that rechecking any erased indexed schema recovers
  its exact sequent; the theorem uses exactly `propext`, while exchange-boundary
  recovery is axiom-free;
- expanded the LeanProp corpus gate to 600 erased positives and 1,000 malformed
  inputs covering every error category plus nested-path propagation with exact
  diagnostics;
- added the strict `leanprop-schema-0.1` JSON contract, deterministic encoder,
  depth-bounded native Lean parser, and checker-gated `checkedFromString`
  boundary; all positive and negative corpus cases traverse the wire path;
- added executable raw-to-indexed elaboration and kernel proofs that it has
  exactly the same result/diagnostic boundary as `infer?` and exists for every
  checker acceptance; checked wire values now retain the indexed derivation
  and expose universal `toPacked`/`sound` proof reconstruction;
- proved that the Type-valued context-permutation syntax represents exactly
  proposition-level `List.Perm` under `Nonempty`, made every such persistent
  or linear exchange admissible, and proved both environment round trips;
- added a typed persistent structural normalizer that recursively cancels
  contraction-over-weakening redexes; kernel theorems prove reduced output,
  fixed points for reduced derivations, idempotence, structural-size
  nonincrease, exact linear-resource preservation, and pointwise proof
  interpretation preservation;
- added independent JSON Schema fixtures and a deterministic 5,000-case native
  LeanProp parser mutation-fuzz gate;
- added a Lean corpus exporter and CI-checked SHA-256 manifest over all 1,600
  labeled wire records, with no independent Python acceptance oracle;
- added a clean remote Lake consumer pinned to the public `v0.6.0` tag. It
  checks valid/invalid wire inputs and typechecks the retained
  boundary, packed witness, universal soundness theorem, and persistent
  structural-normalization API without using the source checkout as a path
  dependency.

## v0.5.2 - Repeated-label pruning and model-backed audit

- added numeric-free one-hop incident-link views to repeated-label occurrence
  alignment and proved that every direct `ProofNetEquivalent` witness satisfies
  the new constraint; this is a completeness-preserving performance filter,
  not a change to proof-net identity;
- qualified the new filter on the 180-task repeated-label/negative experiment
  corpus: Lean rejected every one of 176 distinct corruptions and accepted and
  executably sequentialized all 88 distinct positive certificates in the
  264-input batch;
- preregistered a 180-task held-out model experiment across depths 2--4,
  unique/two-label/one-label strata, positive/negative polarity, and exact
  reference repair distances two/three, with corpus, prompt, implementation,
  and protocol hashes committed before any task-specific model response;
- replaced the experiment repair baseline's unmetered factorial
  materialization with exact distance-layer enumeration. Enumeration and
  checker time are both inside the stated 1,000-candidate/60-second budget.
- recorded protocol amendment 1 after the original runner completed all 360
  model calls but spent roughly 100 minutes in algorithmic scoring without
  reaching Lean verification: the original runner and raw responses remain
  frozen, while a separately hashed amended runner enforces a real per-method
  60-second process deadline and atomic per-task recovery.
- completed the amended 180-task model experiment and committed all raw,
  per-task, summary, and report artifacts: focused search solved 85, direct
  net generation 160, distance-ordered repair 180, model direct 117, and model
  repair 2; Lean rejected all 184 distinct invalid inputs and accepted and
  sequentialized all 92 distinct accepted outputs.

## v0.5.1 - Derivation soundness and exact checked identity

- proved that the explicit exchange index guard already implies the redundant
  element-level `List.Perm` check, and that accepted reorders lift through
  non-injective formula projection without assuming unique labels;
- proved `CutFreeDerivation.build?_exists_of_infer?` and the exact
  `infer?_eq_some_iff_build?_conclusions` synchronization theorem: formula
  inference and occurrence-aware fragment construction now have the same
  success domain and exactly the same ordered formula boundary;
- proved graph-tree and structural-certificate composition for axiom, par,
  tensor, and exchange, then closed full derivation-first soundness:
  every successful `build?` is declaratively correct and checker-accepted;
- proved totality of `desequentializeChecked?` and `elaborate?` on every
  successful independent `infer?` result, with exact ordered boundary labels
  and a kernel `Derivation` retained in the returned value.
- made ordered conclusions constrain occurrence alignments during exact
  `ProofNetEquivalent` search and proved the constrained generator remains
  complete for every direct equivalence witness;
- added `CheckedCertificate.sameProofNet?` with an iff theorem exposing the
  supported exact pairwise identity boundary for checker-accepted inputs,
  without changing the wire formats or claiming arbitrary graph isomorphism;
- added a 64-pair repeated-label structural stress case: the previous
  unconstrained label search has `(64!)^2` theoretical orders, while the new
  boundary-constrained generator creates exactly one candidate. This is a
  regression result, not a polynomial-time complexity claim.

## v0.5.0 - Executable totality, canonical family, and matched experiment

- added the proof-bearing executable `Certificate.sequentialize` API with
  staged errors, checker-gated inverse-rule search, exhaustive repeated-label
  boundary matching, accepted desequentialization, and an exact
  `ProofNetEquivalent` result on success;
- corrected the first development checkpoint's over-strong
  `ReindexEquivalent` postcondition after a reversed-link-order accepted
  certificate exposed a false runtime failure; executable identity now
  enumerates formula-compatible vertex bijections and checks link permutation,
  with the counterexample and all 250 generated nets under reversed link order
  retained as regressions;
- added 250 broad generated executable-sequentialization regressions plus a
  dedicated repeated-formula-boundary test;
- extended the path-dependency consumer to execute the new API and consume its
  proof-net-equivalence theorem;
- proved that the optimized repeated-label occurrence backtracker enumerates
  every fresh duplicate-free formula-compatible occurrence permutation;
- proved completeness of the executable direct proof-net-equivalence search on
  structurally well-formed certificates, including link-list permutations;
- connected the finite boundary-alignment search to a proved candidate and
  proved that the executable axiom branch succeeds on all four possible
  checker-accepted axiom-only representations; proved terminal-par and
  splitting-tensor rebuild completeness/soundness, strict recursive descent,
  and fuel induction, closing universal totality of the public
  `Certificate.sequentialize` API on every checker-accepted certificate;
- exposed `Certificate.proofNetEquivalent?` and proved that on structurally
  well-formed certificates it decides `ProofNetEquivalent` exactly;
- added a deterministic 5,000-case malformed-JSON fuzz harness around the
  native checked parser, including the formula-depth limit, and required it in
  CI;
- added a verified 291-case depth-2/3/4 runtime workload with a 45-second CI
  regression budget and documented the observed depth-sensitive search cost;
- added a kernel-environment-generated public API reference with CI drift and
  unsafe-declaration checks, plus an external Lake consumer tutorial;
- added a CI trust audit pinning ten public logical-boundary theorems to exactly
  `propext`, `Classical.choice`, and `Quot.sound`;
- corrected the Pfenning PDF duplicate audit from 178 to 168 unique pages and
  completed ordered text and rendered-image inspection of every unique page;
- completed the ordered Manin page matrix for all 389 physical pages,
  including visual inspection of the extraction-empty cover, Kochen-Specker
  graphs on pages 99-100, graph-language pages 307-313, and an embedded-image
  audit of the final interval;
- completed the ordered 75-page Marcolli-Berwick-Chomsky source matrix and
  rendered all 19 numbered figures plus three algebraic tables, explicitly
  separating its linguistic Merge “Minimal Search” theorem from proof-net
  sequentialization and focused MLL search;
- completed the ordered 76-page Park source matrix and rendered every page
  carrying mathematical diagrams, code, or data, explicitly separating its
  contact-topology computations from ProofNet-IR claims; all seven original
  project PDFs and the Rowling chat now have complete recorded coverage.
- added a deterministic 1,000-task matched MLL experiment with fixed
  depth-2/3/4 strata and equal 1,000-unit method budgets; focused search solved
  760 tasks, while formula-skeleton net generation and one-edit repair solved
  all 1,000 under their deliberately easier controlled conditions;
- batch-rechecked 930 distinct invalid and 930 distinct accepted experiment
  certificates in Lean, rejecting every mutation and successfully executing
  `Certificate.sequentialize` on every accepted certificate; committed the
  hashed corpus, per-task results, report, and artifact validator without
  claiming a general or model-backed advantage.
- added the executable finite `proofNetCanonicalFamily` specification and
  proved that, on structurally well-formed certificates, extensional equality
  of family membership is equivalent exactly to `ProofNetEquivalent`;
  ordered conclusions, connective-premise order, formula labels, and axiom
  endpoint orientation remain significant, so this is not arbitrary graph
  isomorphism;
- added canonical-family regressions, downstream consumption, generated API
  documentation, and an eleventh exact-axiom trust audit boundary; the
  factorial family is documented as a specification oracle rather than a
  compact production wire key.

## v0.4.0 - General sequentialization

- added `LinkPermutationEquivalent` and the generated `ProofNetEquivalent`
  relation so general sequentialization can ignore semantically irrelevant
  link-list storage order without weakening ordered conclusions or connective
  premises;
- proved in Lean that arbitrary link permutation preserves structural
  well-formedness, all independent par switchings, declarative correctness,
  `Correct`, and the executable checker;
- added a regression certificate that is checker-equivalent under link
  permutation but provably not in the narrower `ReindexEquivalent` class.
- defined the evidence-rich `SequentializationResult` contract and proved it
  transports checker acceptance, ordered boundary labels, and kernel-typed
  derivations;
- added vertex deletion/compaction laws plus a checker-gated terminal-par
  inverse operation, with generated regression coverage over every terminal
  par found in 250 deterministic derivation-first certificates.
- added checker-gated splitting-tensor discovery with full-graph component
  partitioning, cross-link rejection, local renumbering, and two independently
  accepted premises; every one of the 250 generated non-axiom nets exposes at
  least one accepted inverse par or tensor step;
- began the universal graph proof: deleting an in-bounds vertex preserves
  boundedness, has exact incident-edge accounting, preserves the tree
  edge-count equation for leaves, and has an exact adjacency/walk embedding;
- completed the graph theorem that deleting any leaf of an `IsTree` graph
  yields another `IsTree`, including unique incident-edge reasoning,
  simple-walk leaf avoidance, and connectedness preservation.
- proved from certificate ownership and independent `ChoiceSelection`
  semantics that every terminal par conclusion is a degree-one leaf in every
  switching graph; also added the exact `TerminalParReduction` interface that
  turns switching-deletion evidence into checker preservation.
- proved that every proposition-level splitting tensor makes the executable
  candidate return two structurally well-formed certificates, including exact
  restriction/index transport, local link typing, duplicate-free boundaries,
  source ownership, and the root parent-use decrement on both components.
- proved that every switching of either splitting-tensor component lifts to an
  input switching as an exact induced restriction; the restricted graphs are
  bounded and connected because a same-side simple path cannot cross the
  degree-two terminal tensor separator.
- proved the finite connected-graph lower bound `V <= E + 1`, exact tensor
  vertex/edge partitions, and full `IsTree` preservation for both induced
  components; added `TerminalTensorReduction`, declarative/checker preservation,
  and total checker-gated splitting for every accepted splitting input.
- added formula-complexity ranks and proved that every structurally well-formed
  certificate containing a tensor/par link has a terminal connective link;
  the global existence of a splitting tensor remains separate.
- added edge-indexed oriented multigraph edges and composable/reversible
  edge-aware walks, preserving parallel-edge identity and projecting soundly
  to the existing checker-facing vertex walk semantics; this is the base layer
  for the remaining colored-path/Yeo proof.
- added edge-aware simple multigraph cycles, exact full-edge source annotations,
  local switching-incidence colors, cusp semantics, and reversal invariance;
  proved that every stored par link yields two exact indexed incidences aimed
  at its conclusion with the shared par color.
- proved simple-cycle edge indices are duplicate-free and bounded by the
  stored multigraph edge count, including genuine two-parallel-edge cycles.
- strengthened tree counting from edge values to stored occurrences: in every
  `IsTree`, shortest-path parent-edge indices of non-root vertices occupy every
  edge index exactly once, including in multigraphs.
- proved the full occurrence-level acyclicity theorem: `IsTree` excludes every
  edge-aware simple multigraph cycle, by a minimum shortest-path-rank argument;
  added a kernel-checked triangle-cycle regression independent of `isTree`.
- added a full-occurrence switching mask relation, proved it equivalent to the
  independent one-edge-per-par `ChoiceSelection`, and proved its retained
  multiset is exactly the checker switching graph up to edge-list order.
- proved the full correctness-to-colored-acyclicity bridge: a cusp-free exact
  multigraph cycle uses at most one premise occurrence from each par pair,
  admits a switching mask that preserves every cycle edge, and therefore
  contradicts `IsTree`; `DeclarativelyCorrect.cuspAcyclic` now states the
  kernel-checked result for every independent switching.
- added duplicate-free exact-edge simple paths, cusp-free continuations and
  their disjointness-safe concatenation; defined the strengthened directed-edge
  ordering used by generalized Yeo and proved it irreflexive and transitive.
- added both-orientation enumeration of every stored edge occurrence and a
  generic theorem that every nonempty duplicate-free finite list has a maximal
  member under any irreflexive transitive relation.
- added exact-edge simple-cycle reversal and simple prefix extraction; defined
  closing cusps, splitting vertices, cusping edges, and a finite internal-cusp
  count with its cusp-free characterization.
- proved that a cusp-acyclic non-splitting vertex admits a freely closing cycle
  with a nontrivial internal cusp, and that a freely oriented such cycle yields
  a simple cusp-free continuation to its first cusping edge. The universal
  separation condition required by generalized Yeo remains open.
- proved cusp-count additivity with an explicit concatenation boundary and
  invariance under full traversal reversal; minimal freely closing cycles can
  therefore be reoriented without losing minimality.
- added exact simple-path prefixing, truncation of cusp-free continuations at
  their first intersection with a finite vertex list, structural looplessness
  of full proof-net occurrences, and the two cusp-adjacent head-edge exclusion
  lemmas needed by the remaining bungee contradiction.
- proved exact simple-path reversal, suffix extraction, source/target and edge
  occurrence uniqueness, and a constructor closing two oppositely directed
  simple paths into an occurrence-aware simple cycle.
- constructed the normalized first-intersection bungee cycle with verified
  vertex and edge disjointness, and proved cusp-acyclicity forces a cusp at its
  splice from the later prefix into the old return suffix. Minimal-cycle cusp
  arithmetic remains the next bungee obligation.
- proved that normalized intersection cycle has exactly one internal cusp and
  that a one-cusp concatenation split at its cusp has two cusp-free pieces.
- added exact simple-cycle rotation and complementary wrap-around path
  extraction, preserving occurrence identity and vertex simplicity; these are
  the graph constructors needed for the minimal-cycle rerouting step.
- proved cyclic cusp-count invariance under list rotation; strengthened the
  complementary arc with base-vertex and edge-occurrence containment; and
  constructed the first-return bungee splice as an exact simple cycle that can
  be rotated back to the original base. The remaining obligation is to prove
  the rotated splice closes cusp-free and derive the strict minimality
  inequality.
- normalized that same-base splice to an exact traversal formula, proved its
  closing transition is free, and completed the minimal cusp-count inequality;
  for every first intersection strictly away from the old base, the removed
  arc and later path now close into a forbidden cusp-free simple cycle. The
  degenerate first-hit-at-base orientation branch remains before universal
  bungee separation is complete.
- closed both endpoint orientations of the hit-at-base branch with two exact
  same-base replacement cycles. Consequently the oriented bungee
  contradiction is complete for every first hit at or before the selected
  cusp; the symmetric wrap-around case where the first cycle hit lies after
  the cusp remains.
- completed the symmetric after-cusp wrap-around branch: extracted exact old
  wrap/segment paths, built the same-base replacement, proved closing and
  minimal cusp-count constraints, and closed the final forbidden cusp-free
  cycle. What remains is the exhaustive first-intersection position classifier
  and the adjacent hit at the incoming cusp edge's source.
- completed the adjacent incoming-edge branch by reversing the ambient cycle
  when the old prefix is nonempty and by a two-orientation same-base
  minimality argument at the old base; the exhaustive first-intersection
  classifier now covers every source occurrence and excludes the cusp partner
  by simple-path freshness.
- upgraded the minimal first-cusp continuation to a genuine `OrderingPath`,
  proved that every non-splitting target has a strict cusping
  `EdgeOrdering` successor, and closed finite generalized-Yeo maximality to
  obtain a colored `SplittingVertex` in every nonempty cusp-acyclic occurrence
  graph.
- added exact par/tensor annotation-origin lemmas, cusping-occurrence inversion,
  cusping-restricted maximality, and a generic lift from duplicate-free vertex
  walks to exact occurrence-aware simple paths; proved
  `SplittingVertex.toSplittingTensor`, closing the colored-to-deletion splitting
  bridge for terminal tensors without collapsing parallel stored edges.
- defined the representation-specific `SequentializationEdge` carrier and
  proved the exact parent occurrence of every non-boundary carrier target gives
  a strict `EdgeOrdering` successor with the full universal separation field;
  finite parametrized generalized-Yeo maximality now yields a target that is
  both colored-splitting and terminal.
- proved `DeclarativelyCorrect.terminalPar_or_splittingTensor_exists` and the
  checker-facing corollary: every accepted certificate containing a connective
  exposes a mathematical terminal par or splitting tensor. The remaining main
  theorem is well-founded recursive reconstruction plus output equivalence.
- proved strict formula-occurrence decrease for terminal-par peeling and for
  both components of every splitting-tensor restriction, establishing the
  measure obligations needed by well-founded sequentialization.
- completed the axiom-only recursive base: correctness forces exactly two
  occurrences and one axiom; its boundary and endpoint orientation are
  classified exhaustively, and every case now yields a full
  `SequentializationResult` with a kernel-checked derivation tree and explicit
  proof-net equivalence.
- factored the recursive rule layer into a separate
  `LogicalSequentializationResult`: exact terminal-boundary inference/build
  equations and kernel-checked par/tensor composition now reconstruct the
  ordered input sequent using explicit exchange, providing an independently
  auditable precursor to graph reconstruction.
- proved full logical sequentialization by well-founded recursion on formula
  occurrences: every checker-accepted certificate has a kernel-typed
  `Derivation` of exactly its ordered conclusion formulas. The proof includes
  exact par-compaction labels, tensor restriction labels, context partitioning,
  strict recursive descent, and the classified axiom base.
- proved that the generated `ProofNetEquivalent` relation flattens to one
  composite bounded vertex reindexing followed by one link permutation;
  added the functorial reindexing and symmetry/transitivity lemmas needed to
  compose those direct witnesses.
- proved the first-order desequentializer's central synchronization invariant:
  every successful `build?` has balanced formula/root boundaries, and its
  formula boundary is exactly the result of the independent `infer?` pass.
  Projection laws for positional `pick?` and validated `reorder?`, plus an
  internal-fragment witness for every `SequentializationResult`, make the
  occurrence-level reconstruction proof stateable without trusting runtime
  coincidence.
- completed full first-order reverse sequentialization. Exact terminal-par
  reconstruction and splitting-tensor occurrence-boundary reconstruction now
  compose child renamings by a bounded block sum, build concrete par/tensor
  rules plus executable exchange, and prove the resulting certificate
  `ProofNetEquivalent` to the input. The well-founded
  `sequentialization_of_check` theorem returns a `SequentializationResult` for
  every accepted certificate, and `generallySequentializable` exposes the
  public proposition-level result.

## v0.3.1 - Complete order-preserving reindex normal forms

- proved that structural well-formedness makes the first-occurrence traversal
  a duplicate-free enumeration of exactly all formula vertices;
- constructed the explicit bounded `VertexRenaming` induced by that traversal
  and proved normalization is literally an in-class reindexing of every
  structurally well-formed certificate;
- proved the converse theorem: for structurally well-formed certificates,
  equal v0.3 certificate normal forms are equivalent to `ReindexEquivalent`;
- added the executable `reindexEquivalent?` decision procedure with iff
  theorems for structurally well-formed and checker-accepted inputs;
- proved v0.3 normalization preserves checker acceptance for every accepted
  certificate, not only the generated regression corpus.

No JSON field, `reindex-v1` algorithm, or accepted-certificate semantics
changed from v0.3.0.

## v0.3.0 - Checked input and reindex-invariant wire keys

### Included

- added a `VertexRenaming` equivalence layer with inverse round trips and
  kernel-checked invariance of structural validation, switching semantics,
  declarative correctness, and the complete Boolean checker;
- added the versioned v0.3 `reindex-v1` normal-form key and proved that every
  pair of `ReindexEquivalent` certificates has exactly the same serialized
  key;
- retained v0.2 decoding, added v0.3 decoding and a v0.2-to-v0.3 migration API,
  and validated both formats through the checker-gated untrusted-input
  boundary;
- added a v0.3 JSON Schema and fixture, 250 generated Lean round trips, and an
  independent 1,000-record property audit covering deterministic vertex
  permutations, schema validity, idempotence, and link-order sensitivity;
- published an explicit compatibility policy for Lean and wire-format APIs.

### Explicit boundaries

- the proved direction is `ReindexEquivalent -> equal reindex-v1 key`; a
  converse/completeness theorem and a proof that normalization constructs an
  in-class representative for every structurally well-formed certificate are
  still open;
- `reindex-v1` preserves link order, conclusion order, tensor/par premise
  order, and axiom endpoint order. It is not arbitrary graph-isomorphism
  canonical labeling;
- general sequentialization of every checker-accepted net remains open.

- added an independent conclusion-inference pass for first-order derivation
  trees and proved `infer?_sound`: every successful inference denotes a
  kernel-typed `Derivation`;
- strengthened explicit exchange validation with a checked `List.Perm`
  boundary and `reorder?_perm` theorem;
- added `elaborate?`, whose result connects the inferred sequent, a
  kernel-typed derivation, matching proof-net conclusion labels, and checker
  acceptance in one public boundary;
- added honest source-coverage and library-readiness audits so targeted reading
  and research-prototype functionality cannot be presented as completion.
- added a separate downstream Lake consumer that imports the public library,
  exercises certificate checking and `elaborate?`, and runs in CI.
- recorded a representation-level comparison with the primary Rocq proof-net
  formalization to guide sequentialization without silently copying a theorem
  for a different graph model.
- added a native Lean parser for canonical v0.2 JSON, path-aware parse errors,
  canonical-form validation, and a safe checked-input boundary for untrusted
  external certificates.
- formalized loop erasure for arbitrary inductive graph walks and proved the
  uniform `vertexCount` path bound on bounded graphs;
- strengthened the public specification to full iff theorems
  `isTree_iff_isTree`, `check_iff_correct`, and
  `check_iff_declarativelyCorrect` for unbounded walk semantics, and proved
  the unbounded and fuel-indexed correctness contracts equivalent.
- completed a text-and-visual audit of all 33 pages of *Geometry of
  Neuroscience*, with a per-page matrix that classifies it as adjacent
  generated exposition and forbids using it as evidence for proof-net
  correctness, sequentialization, canonicalization, or performance.
- added a lossless certificate-reindexing foundation: bounded bijective vertex
  renamings preserve out-of-bounds status, transport ordered links and
  conclusions, commute with formula lookup, and recover the literal source
  certificate after applying the transported inverse; local link typing and
  node ownership/count predicates are proved invariant;
- completed whole-certificate reindexing invariance for structural validation,
  graph adjacency and walks, boundedness, connectedness, declarative tree
  semantics, switching correctness, and the executable checker; added the
  reflexive, symmetric, and transitive `ReindexEquivalent` relation and proved
  it preserves `Correct` and `DeclarativelyCorrect`. Canonical v0.2 JSON remains
  intentionally numbering-sensitive; v0.3 adds a separate reindex-invariant
  key without changing the v0.2 contract.

## v0.2.0 - Derivation trees, canonical data, and focused baseline

### Included

- first-order arbitrary cut-free MLL derivation trees with explicit resource
  positions and exchange permutations;
- validated general desequentialization from those trees to proof-net
  certificates, plus a checked result that carries `certificate.check = true`;
- a deterministic derivation generator whose first 250 depth-two trees all
  desequentialize and pass the reference checker;
- versioned canonical certificate JSON that normalizes link order, conclusion
  order, and symmetric axiom orientation while preserving formula-array vertex
  identities;
- a committed, deterministic 1,000-record JSONL dataset with 250 valid
  derivation outputs and 750 labeled corruptions, checked again by the
  independent Python oracle;
- a runnable focused cut-free one-sided MLL search baseline with eager par
  decomposition, exhaustive tensor/resource-split search, memoization, and
  search counters;
- schemas, dataset manifest/checksum, regeneration checks, smoke fixtures, and
  GitHub CI coverage for the entire path.

### Explicit boundaries

- canonical serialization is not graph-isomorphism canonicalization;
- desequentialization is general, but reverse sequentialization of every
  checker-accepted proof net is still not implemented;
- the dataset is a correctness/repair substrate, not evidence that graph
  generation outperforms focused proof search.

## v0.1.1 - Mathematical audit hardening

### Changed

- audited the compiled checker against an independent Python oracle on all
  33,868 simple undirected graphs through six vertices and 1,000 generated or
  mutated proof-net certificates;
- added proposition-level link, node, and certificate structural semantics and
  proved `wellFormed_iff_structurallyWellFormed`;
- strengthened `DeclarativelyCorrect` and `FuelDeclarativelyCorrect` so their
  structural premise no longer calls the Boolean checker;
- changed formula Boolean equality to the lawful instance derived from
  `DecidableEq`;
- added multigraph parallel-edge regression coverage and made the audit a
  required CI step.

No v0.1 certificate schema or accepted-fragment semantics changed.

## v0.1.0 - Verified MLL reference core

### Included

- pinned Lean 4.32.0 toolchain and reproducible Lake build;
- unit-free, cut-free MLL formulas, occurrences, axiom/tensor/par links, and
  structural certificate checks;
- exhaustive par-switching enumeration plus an independent inductive
  one-edge-per-par selection semantics;
- finite graph tree checking with independent unbounded and fuel-indexed walk
  semantics;
- checker soundness for declarative switching correctness and soundness/
  completeness for the independent fuel-indexed contract;
- explicit exchange and recursive identity derivations for `A, A-dual`;
- recursive canonical identity-certificate generation and certificate-gated
  reconstruction;
- labeled invalid mutations, 61 compile-time assertions, and a 210-formula
  generated sanity corpus;
- versioned JSON Schema and valid/invalid fixtures;
- CI, architecture, trust-boundary, literature, experiment, and reading-ledger
  documentation.

### Explicit non-goals

- general sequentialization of every accepted MLL proof net;
- a proof that every unbounded walk normalizes within `vertexCount` steps;
- units, Mix, cut, additives, exponentials, quantifiers, or a Lean tactic;
- a claim that graph generation outperforms focused sequent proof search.

These items remain tracked in `docs/roadmap.md` and are not implied by the
v0.1.0 release label.
