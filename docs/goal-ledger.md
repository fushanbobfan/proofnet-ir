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
| D1 | **Open (retargeted 2026-09-20):** completeness of a checker-free fast path, now the sequential Figures 7–8 executable: `Certificate.sequentialFastCheck = Certificate.check`, where `sequentialFastCheck` initializes at the first conclusion, runs `dispatch?` until it stops, and accepts only a derivation that passes `verifyDerivation?`. | The route is D4 (the run stops within `formulas.size + 1` calls) plus D3 (it stops fully marked on a correct certificate) plus the pending fact that a fully marked final state carries one verifiable derivation. The legacy flat-worklist form `Certificate.unificationWorklistFastCheck = Certificate.check` stays recorded below as D1-flat; it is still open, blocked by H-closing-par, and no longer on the critical path. Soundness of the flat path is `Certificate.unificationWorklistFastCheck_sound` (`ProofNetIR/Unification.lean`). |
| D2 | **Blocked by D1:** make the public exact decision the sequential fast path alone, removing the recursive reconstruction fallback, while `Certificate.unificationCheck = Certificate.check` remains a theorem. | The current decision `Certificate.unificationCheck` (`ProofNetIR/Unification.lean`) is `unificationWorklistFastCheck || unificationFastCheck || reconstructsDerivation`; the last disjunct is the fallback. |
| D3 | **Closed:** Figure-7 progress. | `CanonicalTagHistory.dispatch_or_allMarked` in `ProofNetIR/Figure7/Closure.lean` has exactly the statement below. It combines `ReachableByImplementedDispatcher.dispatch_or_activeTopDrained` (`ProofNetIR/SequentialFigure7ActiveTopResidual.lean`) with `ReachableByImplementedDispatcher.allMarked_of_drained`: a drained active region has no switching boundary edge, so by connectedness its class is the whole net. The tail-law route through `ActiveTopMarkedNonconclusionDebt` is not used. |
| D4 | **Closed:** bounded termination of repeated dispatcher execution. | `dispatch_stops` in `ProofNetIR/Figure7/Termination.lean` has exactly the statement below. |
| D5 | **Open:** later-state `NEXTAXIOM` start selection, exhaustive nonterminal enabledness, and completion of the Figures 7–8 sequential executable. | `docs/roadmap.md` records both open items and the Figures 7–8 replacement. The recursive API's existing `Certificate.sequentialize_complete` in `ProofNetIR/ExecutableSequentialization.lean` does not close the replacement goal. |
| D6 | **Open:** a whole-program cost theorem over every implemented operation. | `UnificationWorklistCandidateResult.linkAttemptsWithinBudget` in `ProofNetIR/Unification.lean` covers link attempts only, not frontier search, union-find, verification, or fallback cost. |

### Target propositions

D1 (the executable `sequentialFastCheck` is to be defined in the same
checkpoint; it must accept only after `verifyDerivation?` succeeds on the
final derivation, so soundness is by construction):
```lean
∀ certificate : Certificate,
  certificate.sequentialFastCheck = certificate.check
```

D1-flat (legacy form, still open, not on the critical path):
```lean
∀ certificate : Certificate,
  certificate.unificationWorklistFastCheck = certificate.check
```

D2 (the public decision without a recursive fallback):
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

D5 (the last conjunct is already known for the recursive API):
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

D6 (after the counters cover the entire execution):
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
| H-nextaxiom | **Open:** choose a valid later-state `NEXTAXIOM` start. | `ProofNetIR/SequentialUnification.lean`; `docs/roadmap.md` under later-state start selection |
| H-enabled | **Open:** every reachable nonterminal branch has a `PriorityEnabled` witness. | `ProofNetIR/SequentialFigure7PriorityEnabled.lean`; `docs/roadmap.md` under the Figures 7–8 replacement |

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
