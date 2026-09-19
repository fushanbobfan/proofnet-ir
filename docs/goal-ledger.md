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
| D1 | **Open:** pure worklist completeness, `Certificate.unificationWorklistFastCheck = Certificate.check`. | Soundness is `Certificate.unificationWorklistFastCheck_sound`; the fallback hybrid is `Certificate.unificationWorklistCheck_eq_check`. Both are in `ProofNetIR/Unification.lean`. |
| D2 | **Blocked by D1:** remove the recursive reconstruction fallback, then make the public worklist decision the fast path alone. | The current fallback is in `Certificate.unificationWorklistCheck`, `ProofNetIR/Unification.lean`. |
| D3 | **Open unconditionally:** Figure-7 progress. | `ReachableByImplementedDispatcher.dispatch_or_activeTopDrained` and `SchedulerInvariant.no_readyHead_iff_activeTopDrained` are in `ProofNetIR/SequentialFigure7ActiveTopResidual.lean`; `SchedulerInvariant.allMarked_of_activeTopDrained_of_nonconclusionDebt` is in `ProofNetIR/SequentialFigure7ActiveTopMarkedNonconclusionDebt.lean`; `CanonicalTagHistory.activeTopMarkedNonconclusionDebt_of_tailLaw` is in `ProofNetIR/SequentialFigure7ActiveTopDebtHistoryTail.lean`. These prove the target conditional on H-tail. |
| D4 | **Closed:** bounded termination of repeated dispatcher execution. | `dispatch_stops` in `ProofNetIR/Figure7/Termination.lean` has exactly the statement below. |
| D5 | **Open:** later-state `NEXTAXIOM` start selection, exhaustive nonterminal enabledness, and completion of the Figures 7–8 sequential executable. | `docs/roadmap.md` records both open items and the Figures 7–8 replacement. The recursive API's existing `Certificate.sequentialize_complete` in `ProofNetIR/ExecutableSequentialization.lean` does not close the replacement goal. |
| D6 | **Open:** a whole-program cost theorem over every implemented operation. | `UnificationWorklistCandidateResult.linkAttemptsWithinBudget` in `ProofNetIR/Unification.lean` covers link attempts only, not frontier search, union-find, verification, or fallback cost. |

### Target propositions

D1:
```lean
∀ certificate : Certificate,
  certificate.unificationWorklistFastCheck = certificate.check
```

D2 (the extensional fact required before deleting the fallback branch):
```lean
∀ certificate : Certificate,
  certificate.unificationWorklistCheck =
    certificate.unificationWorklistFastCheck
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
| H-tail | **Open:** `DeclarativelyCorrect → CanonicalTagHistory.ActiveTopDebtTailLaw`. | `ProofNetIR/SequentialFigure7ActiveTopDebtHistoryTail.lean` |
| H-closing-par | **Open:** exclude the surviving closing-par obstruction for the flat worklist. | `ProofNetIR/Unification.lean`; `docs/roadmap.md` near the `unificationWorklistFastCheck` item |
| H-quiescent | **Open:** correct quiescent flat-worklist states make progress. | `ProofNetIR/Unification.lean`; `docs/roadmap.md` immediately after closing-par exclusion |
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
