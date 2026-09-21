# Convergence goal ledger

This ledger names the terminal results that justify further surface growth.
The propositions below are target theorem shapes; `open` means no declaration
with that statement exists. Every named declaration was checked by Lean.
Core certificate/check declarations are in `ProofNetIR/Checker.lean`; scheduler
state/invariant declarations are in `ProofNetIR/SequentialSchedulerBridge.lean`.
Figure-7 history, dispatch results, and reachability are in
`ProofNetIR/SequentialFigure7Dispatcher.lean`; `NewGuard`, `NewEnabled`, and
`PriorityEnabled` are in the matching `NewInputCore`, `NewEnabledCore`, and
`PriorityEnabled` modules. The termination theorem is in
`ProofNetIR/Figure7/Termination.lean`.

## Terminal theorems

| ID | Target and status | Checked evidence and source |
| --- | --- | --- |
| D1 | **Closed (retargeted 2026-09-20):** completeness of a checker-free fast path, the sequential Figures 7–8 executable: `Certificate.sequentialFastCheck = Certificate.check`. | `Certificate.sequentialFastCheck_eq_check` in `ProofNetIR/Figure7/Sequential.lean` has exactly the statement below. Soundness is `sequentialFastCheck_sound` (acceptance requires `verifyDerivation?`); completeness is `sequentialFastCheck_complete`: initialization at the first conclusion succeeds (`StructurallyWellFormed.initializeReservation?_isSome`), the bounded run ends reachable, fully marked, and stopped (`runDispatcher_spec`, from D3 and D4), the final state has one live component owning the carrier with frontier the conclusions (`finalComponents_eq_singleton`, `finalFrontier_perm`, `sequentialFinalTree?_eq_some`), and the exchanged derivation is verified because its desequentialization is proof-net equivalent to the input (`occurrenceBuild_exists`: every occurrence derivation builds with the fresh-index correspondence `OccurrenceBuildMatch`; `occurrenceBuild_equivalent`: a covering linear derivation yields a bounded vertex renaming and a link permutation). The legacy flat-worklist form `Certificate.unificationWorklistFastCheck = Certificate.check` stays recorded below as D1-flat; it is still open, blocked by H-closing-par, and not on the critical path. Soundness of the flat path is `Certificate.unificationWorklistFastCheck_sound` (`ProofNetIR/Unification.lean`). |
| D2 | **Closed:** the public exact decision is the sequential fast path alone, with no recursive reconstruction fallback, and `Certificate.unificationCheck = Certificate.check` remains a theorem. | `Certificate.unificationCheck` is now defined in `ProofNetIR/Figure7/Sequential.lean` as `certificate.sequentialFastCheck`; `unificationCheck_eq_sequentialFastCheck` has exactly the statement below (by `rfl`), and `unificationCheck_eq_check` follows from D1. The former three-way disjunction of `unificationWorklistFastCheck`, `unificationFastCheck`, and `reconstructsDerivation` is gone from the public decision; the three components remain public with their own soundness and completeness theorems. |
| D3 | **Closed:** Figure-7 progress. | `CanonicalTagHistory.dispatch_or_allMarked` in `ProofNetIR/Figure7/Closure.lean` has exactly the statement below. It combines `ReachableByImplementedDispatcher.dispatch_or_activeTopDrained` (`ProofNetIR/SequentialFigure7ActiveTopResidual.lean`) with `ReachableByImplementedDispatcher.allMarked_of_drained`: a drained active region has no switching boundary edge, so by connectedness its class is the whole net. The tail-law route through `ActiveTopMarkedNonconclusionDebt` is not used. |
| D4 | **Closed:** bounded termination of repeated dispatcher execution. | `dispatch_stops` in `ProofNetIR/Figure7/Termination.lean` has exactly the statement below. |
| D5 | **Refuted as stated; corrected mathematical conjunction closed:** later-state `NEXTAXIOM` guards suffice; nonterminal priority enabledness requires initialization. The Figures 7–8 replacement of the eager prototype is realized by D2: the public decision is the sequential executable. | `priorityEnabled_not_allReachable` in `ProofNetIR/Figure7/Enabledness.lean` refutes conjunct 2 using the reachable empty scheduler of one correct axiom. `figure7Enabledness_started_and_sequentialize` proves conjuncts 1 and 3 unchanged and the exact initialization equivalence below; the replacement itself is D2's redefinition of the public decision. |
| D6 | **Closed (retargeted 2026-09-20 to the sequential decision):** a whole-program cost theorem for the public decision `unificationCheck`: an explicit operation count over every phase of one run (structural check, initialization search, each dispatcher call, final extraction, verification), quadratic in the carrier, links, and conclusions of a structurally well-formed certificate, and quadratic in the submitted text of any certificate. | `SequentialCost.decisionStats_total_le_of_structural` and `SequentialCost.decisionStats_total_le` in `ProofNetIR/Figure7/CostBound.lean` have exactly the statements below, for the counters `sequentialDecisionWithStats` of `ProofNetIR/Figure7/Cost.lean` (Boolean equal to `unificationCheck` by `sequentialDecisionWithStats_accepted`). The model charges every list traversal by its length, every array access by one, formulas in symbols with an atom name as one symbol, and the duplicate guards at their carrier-bounded cost; the verifier now compares intrinsic canonicalizations instead of their string codes, whose unary length framing made the code size cubic. The bound is quadratic, not linear: the stack is list-based with tail access, buckets are rebuilt by append, and the consumer index is recomputed per rule attempt; linearity is D6-linear. The former flat-worklist statement stays below as D6-flat, open and off the critical path (`UnificationWorklistCandidateResult.linkAttemptsWithinBudget` in `ProofNetIR/Unification.lean` covers link attempts only). |
| D6-linear | **Open (later goal, recorded 2026-09-20):** a linear whole-program bound for the public decision on structurally well-formed certificates, `constant * SequentialCost.submittedSize`. | Needs constant-time stack access and bucket merge and a single consumer-index construction; not planned for v0.10. Proposition below. |

### Target propositions

D1 (closed by `Certificate.sequentialFastCheck_eq_check`; the executable
accepts only after `verifyDerivation?` succeeds on the final derivation):
```lean
∀ certificate : Certificate,
  certificate.sequentialFastCheck = certificate.check
```

D1-flat (legacy form, still open, not on the critical path):
```lean
∀ certificate : Certificate,
  certificate.unificationWorklistFastCheck = certificate.check
```

D2 (closed by `Certificate.unificationCheck_eq_sequentialFastCheck`):
```lean
∀ certificate : Certificate,
  certificate.unificationCheck = certificate.sequentialFastCheck
```

D3:
```lean
∀ {certificate state} {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (started : 0 < state.stack.nextAge),
  let invariant := history.schedulerInvariant correct.1
  (∃ result, dispatch? certificate state invariant = some result) ∨
    state.core.allMarked = true
```

D4:
```lean
∀ {certificate : Certificate}
    (run : Nat → SequentialSchedulerBridge.ReservationState),
  SequentialSchedulerBridge.SchedulerInvariant certificate (run 0) →
  (∀ n, n < certificate.formulas.size →
    ∀ (invariant : SequentialSchedulerBridge.SchedulerInvariant certificate (run n)) result,
      dispatch? certificate (run n) invariant = some result →
        result.after = run (n + 1)) →
  ∃ n < certificate.formulas.size + 1,
    ∃ invariant : SequentialSchedulerBridge.SchedulerInvariant certificate (run n),
      dispatch? certificate (run n) invariant = none
```

D5 (original statement, refuted by its second conjunct; retained verbatim):
```lean
(∀ {certificate state},
    ReachableByImplementedDispatcher certificate state →
    certificate.DeclarativelyCorrect →
    NewGuard certificate state → NewEnabled certificate state) ∧
(∀ {certificate state}
    (reachable : ReachableByImplementedDispatcher certificate state)
    (correct : certificate.DeclarativelyCorrect),
    let invariant := reachable.schedulerInvariant correct.1
    state.core.allMarked ≠ true →
      ∃ kind, PriorityEnabled certificate state invariant kind) ∧
(∀ certificate : Certificate, certificate.check = true →
    ∃ result : ExecutableSequentializationResult certificate,
      certificate.sequentialize = .ok result)
```

The corrected D5 conjunction preserves conjuncts 1 and 3 and replaces only
conjunct 2 with the following exact, proved equivalence:
```lean
∀ {certificate state}
    (reachable : ReachableByImplementedDispatcher certificate state)
    (correct : certificate.DeclarativelyCorrect),
  let invariant := reachable.schedulerInvariant correct.1
  state.core.allMarked ≠ true →
    ((∃ kind, PriorityEnabled certificate state invariant kind) ↔
      0 < state.stack.nextAge)
```

D6 (closed; `SequentialCost.submittedSize` is `formulas.size + links.length +
conclusions.length + 1` and `SequentialCost.inputSize` adds the symbols of
every stored formula, because a malformed input can carry formulas larger
than its carrier and the structural check compares them):
```lean
∀ certificate : Certificate, certificate.StructurallyWellFormed →
  certificate.sequentialDecisionWithStats.stats.total ≤
    152 * (certificate.formulas.size + 1) * SequentialCost.submittedSize certificate
```
```lean
∀ certificate : Certificate,
  certificate.sequentialDecisionWithStats.stats.total ≤
    152 * SequentialCost.inputSize certificate * SequentialCost.inputSize certificate
```

D6-linear (later goal, open; needs constant-time stack access and bucket
merge and a single consumer-index construction):
```lean
∃ constant : Nat, ∀ certificate : Certificate, certificate.StructurallyWellFormed →
  certificate.sequentialDecisionWithStats.stats.total ≤
    constant * SequentialCost.submittedSize certificate
```

D6-flat (legacy form, still open, not on the critical path):
```lean
∃ constant : Nat, ∀ (certificate : Certificate)
    (result : UnificationWorklistVerificationResult certificate),
  certificate.unificationWorklistReconstructWithStats = .ok result →
    let stats := result.candidate.stats
    stats.initialEnqueues + stats.dependencyEnqueues +
      stats.waitingRequeues + stats.linkAttempts + stats.successfulFirings ≤
        constant * (certificate.formulas.size + certificate.links.length + 1)
```

## Open hypotheses

| ID | Hypothesis and status | Source |
| --- | --- | --- |
| H-tail | **Open:** `DeclarativelyCorrect → CanonicalTagHistory.ActiveTopDebtTailLaw`. | `ProofNetIR/SequentialFigure7ActiveTopDebtHistoryTail.lean`. Reduction in `ProofNetIR/Figure7/TailLaw.lean`: the `nop` and `wait` obligations follow from the state predicate `ParHeadGuardTailNonconclusion` (C12) on the pre-state (`NopStep.tailNonconclusion_of_parHeadGuard`, `WaitStep.tailNonconclusion_of_parHeadGuard`), and C12 holds after every correct initialization (`InitialReservationStep.parHeadGuardTail`). C12 is not a state-only inductive invariant: `parHeadGuardTail_not_inductive` exhibits a correct certificate and a `SchedulerInvariant` state satisfying C12 whose canonical `nop` successor violates it, with that pre-state proved canonically unreachable. The suffix strengthening C13 fails the probe (173,226 default and 474,336 wait-focus states) because earlier pops can mark a later head's mate and tensor actions change the active layer. The finite probe reports C12 at all 1,217,664 default and 1,071,360 wait-focus reachable states. No longer needed for D3 (closed directly from region closure). Closed half, in `ProofNetIR/Figure7/Closure.lean`: the order-free `RegionClosure` holds after every correct initialization (`RegionClosure.ofInitialReservation`), is preserved by every rule (`DispatchStep.regionClosure`), so every dispatcher-reachable state satisfies C12 (`ReachableByImplementedDispatcher.guardedHeadTail`, via the cutting switching of `boundary_edge_of_correct`), and a `nop` or `wait` extension of a canonical prefix adds no tail-law obligation (`CanonicalTagHistory.nopWaitTailLaw_iff`). Remaining: the created-head obligations of the `forward` and `unifyPayload` branches, stated exactly at the end of that module. |
| H-closing-par | **Open, off the critical path since D1 was retargeted:** exclude the surviving closing-par obstruction for the flat worklist. | `ProofNetIR/Unification.lean`; `docs/roadmap.md` near the `unificationWorklistFastCheck` item |
| H-quiescent | **Open, off the critical path since D1 was retargeted:** correct quiescent flat-worklist states make progress. | `ProofNetIR/Unification.lean`; `docs/roadmap.md` immediately after closing-par exclusion |
| H-nextaxiom | **Closed:** choose a valid later-state `NEXTAXIOM` start under the exact shallow guard below. | Corrected D5, conjunct 1; `ProofNetIR/Figure7/Enabledness.lean`. |
| H-enabled | **Refuted as stated; corrected form closed:** a reachable nonterminal state has a priority witness exactly when initialized. | Corrected D5, conjunct 2; the original proposition below fails at the reachable empty scheduler. `ProofNetIR/Figure7/Enabledness.lean`. |

H-tail:
```lean
∀ {certificate state} {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history),
  certificate.DeclarativelyCorrect → tagHistory.ActiveTopDebtTailLaw
```

H-closing-par (source-local schema; its exact carrier is private):
```lean
closingParObstruction → False
```

H-quiescent (source-local schema; its exact state carrier is private):
```lean
correctQuiescentState → worklistCanFire
```

H-nextaxiom:
```lean
∀ {certificate state},
  ReachableByImplementedDispatcher certificate state →
  certificate.DeclarativelyCorrect →
  NewGuard certificate state → NewEnabled certificate state
```

H-enabled:
```lean
∀ {certificate state}
    (reachable : ReachableByImplementedDispatcher certificate state)
    (correct : certificate.DeclarativelyCorrect),
  let invariant := reachable.schedulerInvariant correct.1
  state.core.allMarked ≠ true →
    ∃ kind, PriorityEnabled certificate state invariant kind
```

## Closing an item

- A kernel-checked theorem closes an item only when its statement is exactly the proposition recorded here.
- Equivalent syntax is acceptable only after Lean checks the equivalence in the kernel.
- A kernel-checked counterexample may close a false item by refuting its exact proposition.
- The counterexample must replace the false item with the strongest honest successor statement.
- Update this row and the matching roadmap item in the same checkpoint that adds the theorem or counterexample.
