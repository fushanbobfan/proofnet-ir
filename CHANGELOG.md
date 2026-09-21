# Changelog

## Unreleased

The rolling `v0.10.0-dev` branch builds the sequential Figures 7–8 scheduler
and its proof layer on top of `v0.9.0`. Entries are one per mathematics
checkpoint, newest first; wrapper-transport steps are folded into the family
they served, and `git log` holds the per-commit record.

- closed D6, the whole-program cost theorem of the public decision:
  `ProofNetIR/Figure7/Cost.lean` runs the decision with operation counters
  of every phase (`sequentialDecisionWithStats`, Boolean equal to
  `unificationCheck`; list traversals by length, array accesses by one,
  formulas by symbols), and `ProofNetIR/Figure7/CostBound.lean` proves
  `decisionStats_total_le_of_structural`, `152 * (formulas + 1) * (formulas +
  links + conclusions + 1)` for structurally well-formed inputs, and
  `decisionStats_total_le`, `152 * inputSize²` for all inputs; linearity
  (D6-linear) stays open. On the way, the `forward`/`unifyPayload` duplicate
  guards became the linear `nodupGuard` (quadratic guards made a run cubic),
  a waiting potential pays payload activation, live trees have no exchange
  nodes, and `verifyDerivation?` compares canonicalizations, not cubic codes;
- closed D2: `Certificate.unificationCheck`, the exact public decision, is now
  `sequentialFastCheck` alone (`ProofNetIR/Figure7/Sequential.lean`), with no
  eager scan, worklist tier, or recursive reconstruction fallback;
  `unificationCheck_eq_sequentialFastCheck` is D2 by `rfl`, and
  `unificationCheck_eq_check` and its iff forms keep their names and
  statements. The three former tiers stay public with their own theorems.
  The benchmark now times the public decision (`sequential_decision_ms`) and
  measures the reference check honestly (the previous per-input millisecond
  deltas truncated to zero). The convergence gate's prose ratio now counts
  net prose growth, so rewriting stale descriptions in place is not penalized;
- closed D1, completeness of the sequential fast path:
  `sequentialFastCheck_eq_check` (`sequentialFastCheck = check`), through
  `sequentialFastCheck_complete`. `occurrenceBuild_par_eq` and
  `occurrenceBuild_tensor_eq` prove the par and tensor cases of the fresh-index
  correspondence (`relabelLink` names its link action), `occurrenceBuild_exists`
  closes the induction over occurrence derivations, and
  `occurrenceBuild_equivalent` turns a covering linear derivation into a bounded
  vertex renaming plus link permutation, so the desequentialized final tree is
  `ProofNetEquivalent` to the input and `verifyDerivation?` accepts it;
- proved final structure and inference for fully marked reachable correct nets:
  `finalComponents_eq_singleton` identifies the sole component and full ownership;
  `finalFrontier_perm` identifies its frontier with the input conclusions;
  `sequentialFinalTree?_eq_some` proves extraction with a duplicate-free exchange;
  `sequentialFinalTree?_infer_eq` proves exact inference and accepted desequentialization.
  Exposed the unchanged closure seed `seed_of_drained`. The fresh-index correspondence
  tracks labels, roots, and submitted links; `occurrenceBuild_axiom_eq` and
  `occurrenceBuild_exchange_eq` prove its axiom and exchange cases. The par/tensor
  cases, full-carrier proof-net equivalence, and fast-path completeness (D1) remain open;
- proved initialization totality for the sequential fast path:
  `StructurallyWellFormed.initializeReservation?_isSome` shows that
  `initializeReservation?` succeeds at every in-bounds start of a structurally
  well-formed certificate, through the carrier bound
  `StructurallyWellFormed.formulaComplexityAt_lt_size` (descending through
  producer links visits distinct occurrences, so a formula's connective count
  is below the occurrence count), the clear-through search totality, the
  exact route's endpoint orientation, and the initial enqueue and
  reservation guards. Completeness of `sequentialFastCheck` now rests only on
  the verification of the final component's derivation;
- added the sequential fast path (`ProofNetIR/Figure7/Sequential.lean`):
  `runDispatcher` executes the canonical dispatcher for a bounded number of
  calls threading the scheduler invariant; `sequentialReconstruct?` and
  `sequentialFastCheck` initialize at the first conclusion, run the
  formula-carrier budget, exchange the final component's frontier into the
  conclusion order, and accept only after `verifyDerivation?`, so
  `sequentialFastCheck_sound` is by construction. `runDispatcher_spec`
  proves that from a started reachable state of a correct certificate the
  run ends reachable, fully marked, and unable to dispatch. Completeness
  (D1) remains open: initialization totality at the first conclusion and
  verification of the final component's derivation are not proved;
- refuted D5's unrestricted nonterminal enabledness: the reachable empty
  scheduler of one correct axiom is unmarked and cannot dispatch
  (`priorityEnabled_not_allReachable`). Proved the corrected conjunction
  `figure7Enabledness_started_and_sequentialize`: reachable shallow `new`
  guards suffice, and a reachable nonterminal state has a priority branch
  exactly when initialized; accepted certificates retain recursive API
  completion. This does not prove completion of the Figures 7–8 replacement,
  fast-path completeness, or a whole-program cost bound;
- closed ledger item D3, Figure-7 progress:
  `CanonicalTagHistory.dispatch_or_allMarked` (and its reachable-state form
  `ReachableByImplementedDispatcher.dispatch_or_allMarked`) proves that a
  started reachable state of a correct certificate either dispatches or has
  every occurrence marked. The drained case is
  `ReachableByImplementedDispatcher.allMarked_of_drained`: with an
  empty active bucket the active region has no switching boundary edge
  (`RegionClosure.class_of_empty_active`), so connectedness makes the active
  class the whole net. The history-tail law and its created-head branches
  are not used; they remain open as stated in `ProofNetIR/Figure7/Closure.lean`;
- proved `RegionClosure` preserved by every canonical dispatcher rule
  (`ConclStep`, `NopStep`, `WaitStep`, `ForwardStep`, `NewStep`,
  `UnifyPayloadStep`, and `DispatchStep.regionClosure`), lifted it to every
  executed history and dispatcher-reachable state, and derived C12 at every
  reachable state of a correct certificate
  (`ReachableByImplementedDispatcher.guardedHeadTail`).
  `CanonicalTagHistory.nopWaitTailLaw_iff` closes the `nop` and `wait`
  branches of the history-tail law: extending a canonical prefix by either
  rule adds no obligation. The `forward` and `unifyPayload` created-head
  branches remain open and are stated exactly at the end of
  `ProofNetIR/Figure7/Closure.lean`;
- proved C12 from region closure and switching connectedness in
  `ProofNetIR/Figure7/Closure.lean`. `RegionClosure` is order-free: it places
  every marked vertex in the class of the sigma boundary below its mark and
  requires the marked part of each region to be closed under the link
  structure except at pars whose other premise lies outside.
  `RegionClosure.guardedParHeadTail` derives C12 from closure, `SchedulerInvariant`,
  and `DeclarativelyCorrect` by cutting every boundary par of the active
  region and taking a boundary edge of that switching
  (`boundary_edge_of_correct`); `RegionClosure.ofInitialReservation` proves closure after
  every correct initialization. Preservation by the six rules, reachability,
  and the tail-law branches remain open;
- added `--inductiveness-probe` to `proofnet_ir_tail_law_search`: bucket
  permutations (with a compiled `SchedulerInvariant` proof) and bare pop/mark
  prefixes seed finite dispatcher-closed snapshot sets on which each candidate
  is tested for preservation by every rule. Order-based candidates I1-I3
  are refuted at reachable states; I4-I6 hold there but the strongest bundle
  is not inductive (kernel-checked `forward` obstruction). The order-free
  region-closure candidate CLOSURE holds at all 2,289,024 reachable states,
  is preserved by all six rules on 15,405,918 closure-satisfying snapshot
  edges, and implies C12 at every one of them; scaffolding only, no theorem;
- probed the active ready bucket at every reachable state of the finite
  tail-law search: SHAPE (connective conclusions followed by atoms) and PAIRS
  (every atom's axiom partner is in the run or already marked) hold at all
  1,217,664 default and 1,071,360 wait-focus states; scaffolding only, no
  theorem;
- proved C12 (`ParHeadGuardTailNonconclusion`, `ProofNetIR/Figure7/TailLaw.lean`)
  for every correct initial reservation and its exact implications for the
  `nop` and `wait` remaining-top obligations, and certified that C12 plus
  `SchedulerInvariant` is not preserved by a canonical `nop`, with a
  canonically unreachable pre-state; C12 reachability, the history-tail law,
  and D3 remain open;
- added `--invariant-probe` to `proofnet_ir_tail_law_search` and CI. It
  evaluates candidate state invariants at every reachable state of both
  certificate sets: C12 holds everywhere, C8 shows at least two raw vertices
  at every `nop`/`wait` pre-state, and C1, C3, C4, C6, C7, C11, and C13 fail;
  two kernel-checked probes show C3 is false after a canonical `nop` and that
  `SchedulerInvariant` alone does not imply the tail condition;
- added `proofnet_ir_tail_law_search`, a finite search for
  `CanonicalTagHistory.ActiveTopDebtTailLaw` over checked derivation-generated
  certificates with exact canonical replay, and its `--wait-focus` mode (1,152
  certificate cases, 34,560 histories, 25,920 `wait` steps); both fail closed
  on budget exhaustion and found no violation; finite evidence only;
- added `docs/goal-ledger.md` and `scripts/check_convergence.py`, a
  standard-library-only CI gate that caps new modules, path and theorem-name
  length, prose additions, and maintained-document size, and confines new
  theorem names to the changelog, generated API, roadmap, and ledger;
- bounded canonical Figure-7 dispatcher histories in
  `ProofNetIR/Figure7/Termination.lean`: `dispatchMeasure` counts marked
  occurrences, each successful dispatch adds exactly one
  (`DispatchStep.measure_eq`), an executed history makes at most
  `certificate.formulas.size` calls (`ExecutedHistory.dispatchCount_le`), and
  `dispatch_stops` closes ledger item D4; no progress, later-state totality,
  or terminal-state completeness follows;
- classified the marked re-entry target of a `nop` or `wait` under exact
  ready-tail failure (`SequentialFigure7MarkedTargetWaitingMateExternal*`,
  `SequentialFigure7WaitingReentryContinuation*`,
  `SequentialFigure7FutureWorkQueueStatus`,
  `SequentialFigure7FutureWorkExactLocation`; 18 modules). Under
  `SchedulerInvariant`, `DeclarativelyCorrect`, a canonical history, and a
  selected outer par, the target is raw work outside the active carrier, an
  exact return to the selected/mate pair, an older future-work endpoint, or an
  older marked representative, each with a current-state queue-status
  receipt (`UnmarkedOutsideActiveSchedulerStatus`). These are conditional
  classifications; none is the tail law;
- authenticated and totally ordered raw-mark chronology in canonical tag
  history (`SequentialFigure7RawMarkCausalOrder`,
  `SequentialFigure7MarkedTargetRawReturn*`,
  `SequentialFigure7MarkedTargetNopRawReturnElimination`; 17 modules):
  distinct authentic marked vertices are strictly comparable, the first
  causal descent re-roots a sibling continuation after its shared marked
  conclusion, complete raw-return cancellation retains both endpoint
  junctions, and the typed `nop` raw return to the current opposite premise
  is eliminated;
- localized the commitment-interval par outcome against the active carrier
  (`SequentialFigure7CommitmentIntervalPar*`,
  `SequentialFigure7ActiveTopDebtParent*`; 16 modules): a positive retained
  `sigma` interval composes its adjacent commitment paths; under supplied
  reference-switching connectedness, the strictly older external mate of an
  actual `nop` or `wait` re-enters the active carrier by an exact
  outside-to-inside edge, and the selected-head and active-owned-mate exits
  are excluded;
- stated the active-top debt residual exactly
  (`SequentialFigure7ActiveTopResidual`, `ActiveTopMarkedNonconclusionDebt`,
  `ActiveTopDebtBranchResidual`, `ActiveTopDebtQueueTail`,
  `ActiveTopDebtHistoryTail`, `ContinuationCredit`,
  `ContinuationCreditPreservation`, `ContinuationExit`,
  `EndpointLocalityObstruction`): `ActiveTopDrained` names the post-history
  ready-head boundary, `ReachableByImplementedDispatcher.dispatch_or_activeTopDrained`
  reduces progress to draining it, `CanonicalTagHistory.ActiveTopDebtTailLaw`
  names the remaining obligation, and
  `WaitStep.not_activeTopContinuationExitLocalized` shows that obligation is
  not local to one step;
- proved the older-marked-tensor predecessor invariant over complete
  canonical histories (`SequentialFigure7OlderMarkedTensorPredecessor*`, six
  modules) and reduced the six rule families at a supplied ready head to one
  exact residual (`SequentialFigure7ReadyHeadDispatchResidual`); strengthened
  `proofnet_ir_new_progress_audit` to classify typed `ReadyHeadInput`
  availability at every replayed state;
- separated older reservation events from the active region
  (`SequentialFigure7OlderEventFutureWorkTouch*`, nine modules;
  `OlderEventTouchSeparation`; `OlderRawMarkedRegion*`, five modules;
  `ActiveRegionTouchOrder`, `ActiveRegionAvailability`,
  `ActiveRegionEnabledness`, `ActiveRegionTouchSeparation`,
  `ActiveConclusionTouch`): one induction over `CanonicalTagHistory` proves
  `OlderEventFutureWorkTouchSeparated` from structural well-formedness, each
  creating rule preserves it and the raw-marked-region separation, and under
  an active `NewGuard` structural source search reaches the active tensor
  mate;
- made the commitment spine exact (`SequentialFigure7CommitmentSpine`,
  `RawMarkHistory`, `RawMarkReservationAnchor`, `CommitmentEdgeReferencePath`,
  `CommitmentEdgeTargetAvoidance`, `CommitmentIntervalTargetAvoidance`,
  `EqualBoundaryCommitmentTargetAvoidance`, `StrictCommitmentTargetAvoidance`,
  `StrictOlderSigmaSplit`, `CommitmentBlockerAdvance`,
  `CommitmentBlockerMaximality`): every adjacent pair retained in final
  `sigma` recovers its historical `new` event and a canonical simple reference
  path from parent to child, and positive intervals compose such paths while
  avoiding a supplied future-New candidate;
- added the cross-representative future-work invariant
  (`SequentialFigure7CrossRepresentativeInvariant` and five preservation
  modules): `FutureWorkAt` retains an exact `sigma`/`ready` position or an
  initialized waiting cell, and every successful rule preserves it;
- reified reservation history (`SequentialFigure7ReservationLedger`,
  `TouchOrigin`, `RegionBoundaries`, `ReservationRealization`,
  `TerminalPartnerGeometry`, `SameRepresentativeEventTouch`,
  `SameRepresentativeGeometry`, `TouchCompleteness`,
  `SequentialComponentReferenceGeometry`,
  `SequentialComponentSourceLeftGeometry`): every initialization or canonical
  `new` is an unforgeable event ordered by immutable raw age, every global
  `Touched` witness is one such event, and a supplied source-left run is
  complete for its structural region;
- made the source-left obstruction boundary exact (`SequentialFreshSourceBlocker`,
  `SequentialFreshSourceLeftRun`, `SequentialFigure7BlockerHistory`,
  `SequentialFigure7QueueHistory`, `SequentialFigure7FreshCapacity`,
  `SequentialFigure7NewRegion`,
  `Certificate.StructurallyWellFormed.links_length_le_formulas_size`): the
  production `NEXTAXIOM` search is a fuel-indexed proof-relevant run, every
  dynamic blocker in an authentic history is classified, and a queued endpoint
  of a submitted axiom is retained from the prior queue or touched by its
  event;
- added the canonical six-rule dispatcher and its enabledness layers
  (`SequentialFigure7Dispatcher`, `TagHistory`, `StableEnabled`,
  `PriorityEnabled`, `UnifyPayloadEnabled`, `NewInputNecessary`, `NewEnabled`,
  `NewEnabledCore`, `NewInputCore`, `ProgressInvariant`, `TensorAdjacency`,
  `ProofNetIRNewProgressAudit.lean`): `dispatch?` tries `concl`, `nop`,
  `new`, `wait`, `forward`, `unifyPayload` in that fixed precedence, typed
  `DispatchStep` witnesses recover the exact rule taken,
  `FutureWaitingUndefined` keeps unallocated waiting cells undefined, and the
  finite audit replays every post-initialization state of its certificate
  sets;
- added the local Figure-7 rules and the complete state invariant
  (`SequentialFigure7Rules`, `History`, `New`, `Unify`, `UnifyOne`,
  `UnifyPayload`, `UnifyPayloadInvariant`, `SequentialSchedulerInvariant`):
  `unifyPayload?` rebuilds the active bucket as
  `conclusion :: (payload ++ previousReady ++ activeReady)`, and every
  successful typed step preserves the occurrence-exact `SchedulerInvariant`,
  including arbitrary finite waiting payloads;
- added the delayed Figures 7–8 stack and the reservation bridge
  (`SequentialSchedulerState`, `SequentialSchedulerBridge`,
  `SequentialUnification`, `SequentialRoute`, `SequentialConsumerIndex`,
  `SequentialComponentProvenance`): `RawTokenAge` is the immutable discovery
  order, `ReservationState` couples the delayed stack with the production
  core and the search-tag array, and the later `RealizesSigma` bridge is
  proved; the literal printed Figure-7 `new` is kept as an audit helper
  distinct from the production transition;
- refuted flat-scheduler confluence with derivation-generated and structural
  counterexample regressions, and narrowed the closing-package layer in
  `ProofNetIR/Unification.lean`: coordinate-exact `SchedulerOccurrence`s,
  the data-indexed closing package with its endpoint zipper, cyclic
  reverse-shell normalization, and the nonempty-residual-core theorem for the
  fully cancelling dependency cycle, none of which claims the v0.10
  contradiction;
- began the scheduler-coverage proof layer for the event-driven worklist and
  the independent token semantics (`ProofNetIR/UnificationSemantics.lean`):
  `UnificationMarking`, `UnificationStep`, and the reflexive-transitive
  `UnificationExecution` relation; `forwardToken?` and `unifyTokens?` refine
  exactly one abstract step each, the exact ordered union-find update theorem
  holds on the full `Nat` carrier, the whole successful eager run refines one
  independent execution, and `ComponentsFormulaConsistent` holds through
  every component operation; two development-invariant bugs (`FreshExtension`
  and the `Abstractable` contract) were found by kernel-checked
  counterexamples and repaired before release;
- added an opt-in Windows wrapper for the byte-frozen preregistered
  `audit_v010.py` mathematics audit;
- started `v0.10.0-dev` with an explicit proof plan separating independent
  unification-step semantics, scheduler coverage, worklist fuel sufficiency,
  correct-state progress and pure completeness, and the later sequential
  implementation;

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
