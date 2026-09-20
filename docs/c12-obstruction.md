# C12 preservation obstruction

`ProofNetIR/Figure7/TailLaw.lean` defines `ParHeadGuardTailNonconclusion` (C12),
proves the correct initialization case, and derives the exact `nop` and `wait`
remaining-top obligations conditional on C12 in the pre-state. Empty-state C12
is checked privately. Reachable C12, H-tail, and D3 remain open.

## Refuted preservation statement

The kernel-checked `parHeadGuardTail_not_inductive` exhibits:

```lean
∃ (certificate : Certificate) (before after : ReservationState)
    (invariant : SchedulerInvariant certificate before),
  certificate.DeclarativelyCorrect ∧
  ParHeadGuardTailNonconclusion certificate before ∧
  Nonempty (DispatchStep certificate before invariant ⟨.nop, after⟩) ∧
  ¬ ParHeadGuardTailNonconclusion certificate after ∧
  ¬ ReachableByImplementedDispatcher certificate before
```

The certificate has atoms `0=a`, `1=a⊥`, `2=b`, `3=b⊥`, `4=c`, `5=c⊥`;
links `axiom(0,1)`, `axiom(2,3)`, `axiom(4,5)`, `tensor(2,4,6)`,
`tensor(3,0,7)`, `par(6,1,8)`, `par(5,7,9)`; and conclusions `[8,9]`.
Its checker acceptance is reduced in the kernel and transported to declarative
correctness. All witness computations use `decide +kernel`.

Starting at 4, canonical `new; unifyPayload` reaches ready `[[6,5,3]]`.
The countermodel instead permutes that bucket to `[[3,6,5]]` and performs only
the prepared prefix on tensor premise 3. Both operations preserve the state-only
scheduler invariant. The resulting state has sigma `[0]`, ready `[[6,5]]`, and
marks `[none,none,some 1,some 0,some 0,none,none,none,none,none]`.
C12 holds because 5 is a non-conclusion in the tail. Its canonical `nop` marks
6 and leaves `[[5]]`; vertex 5 has par mate 7, which remains unmarked, so C12
would require a member of the empty tail.

This is **not a reachable counterexample**. A list of 111 snapshots (including
duplicates and the empty state) is kernel-verified to cover every initialization
and to be closed under dispatcher success. Induction on `ExecutedHistory`
therefore covers histories of arbitrary length. The countermodel is absent
from that list. The closure proof, not the trace-generation fuel, establishes
unreachability.

## Probe of a proposed strengthening

C13 requires C12's guard/tail condition at every suffix of the active bucket,
using the same pre-state marks. The new probe checks it at every state in both
existing sets. The rerun produced:

```text
invariant-probe set=default C12 par-head-guard-tail-nonconclusion states=1217664 fails=0
invariant-probe set=default C13 par-suffix-guard-tail-nonconclusion states=1217664 fails=173226
invariant-probe set=wait-focus C12 par-head-guard-tail-nonconclusion states=1071360 fails=0
invariant-probe set=wait-focus C13 par-suffix-guard-tail-nonconclusion states=1071360 fails=474336
```

These are finite measurements, not a reachable-invariance theorem. C13 is not
a viable induction hypothesis: earlier pops can mark a later head's mate, and
earlier tensor actions can change the active layer.

## Exact remaining goals

The actual history induction must retain the reachability information absent
from the refuted state-only statement. In particular, its `nop` case remains:

```lean
certificate : Certificate
before after : ReservationState
history : ExecutedHistory certificate before
correct : certificate.DeclarativelyCorrect
invariant : SchedulerInvariant certificate before
prior : ParHeadGuardTailNonconclusion certificate before
dispatch : DispatchStep certificate before invariant ⟨.nop, after⟩
step : NopStep certificate before after
currentTail : ∃ pending, pending ∈ step.prepared.stackResult.remainingTop ∧
  pending ∉ certificate.conclusions
⊢ ParHeadGuardTailNonconclusion certificate after
```

This goal is not refuted. No preservation proof or reachable counterexample is
claimed. The other later-step preservation cases remain unproved as well.

`popReadyMark?_exact` supplies
`before.stack.ready.getLast? = some (vertex :: remainingTop)` and
`before.stack.sigma.getLast? = some rawAge`. The guard facts are
`NopStep.mate_unmarked_before`, `WaitStep.mate_marked_before`, and
`WaitStep.younger`. Thus the two conditional tail theorems use the same pre-state
and raw age as the requested C12 statement. The private lookup lemma
`exists_connectiveBelow?_eq_some_par_of_structural` in
`SequentialFigure7Rules.lean` supplies an exact executable par view; the
`ConnectiveBelow` structure itself retains its unique consumer and submitted link.

The unchanged created-head obligations in `CanonicalTagHistory.ActiveTopDebtTailLaw` are:

```lean
-- forward
step.consumer.conclusion ∉ certificate.conclusions ∨
  (ActiveTopMarkedNonconclusionPresent certificate after →
    ∃ pending, pending ∈ step.prependStep.activeReady ∧ pending ∉ certificate.conclusions)
-- unifyPayload
step.consumer.conclusion ∉ certificate.conclusions ∨
  (ActiveTopMarkedNonconclusionPresent certificate after →
    ∃ pending, pending ∈ step.mergeStep.payload ++ step.mergeStep.previousReady ++
      step.mergeStep.activeReady ∧ pending ∉ certificate.conclusions)
```

Neither created-head branch is closed. No ledger or roadmap item is marked complete.
