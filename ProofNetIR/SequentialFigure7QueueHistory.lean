import ProofNetIR.SequentialFigure7FreshCapacity
import ProofNetIR.SequentialFigure7NewRegion

namespace ProofNetIR

/-!
# Exact axiom-endpoint queue history for Figure 7

This module tracks only queued occurrences that are endpoints of one exact
submitted axiom.  A stable rule may enqueue an untagged connective conclusion,
so no theorem here claims that every queued occurrence is tagged.  The final
bridges remain conditional on an exact source-left route or run; they do not
make `NewGuard` sufficient and prove no dispatcher progress or totality.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

namespace DispatchTagEvidence

/-- One dispatcher event can retain an exact axiom endpoint from the old
queue or touch it in the event's unique `NEXTAXIOM` call.

The restriction to an endpoint of the supplied exact axiom is essential:
`wait`, `forward`, and `unifyPayload` may enqueue an untagged connective
conclusion. -/
theorem queued_axiom_endpoint_old_or_touched
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result)
    (structural : certificate.StructurallyWellFormed)
    {axiomIndex : Nat} {left right endpoint : Vertex}
    (exactAxiom :
      certificate.links[axiomIndex]? = some (.axiom left right))
    (endpointAt : endpoint = left ∨ endpoint = right)
    (queued : endpoint ∈ result.after.stack.queuedVertices) :
    endpoint ∈ before.stack.queuedVertices ∨
      evidence.Touched endpoint := by
  have axiomMembership :
      Link.axiom left right ∈ certificate.links :=
    List.mem_of_getElem? exactAxiom
  cases evidence with
  | concl step =>
      have middleQueued :
          endpoint ∈ step.prepared.after.stack.queuedVertices := by
        simpa only [step.output_eq] using queued
      exact Or.inl (step.prepared.after_queued_subset_before middleQueued)
  | nop step =>
      have middleQueued :
          endpoint ∈ step.prepared.after.stack.queuedVertices := by
        simpa only [step.output_eq] using queued
      exact Or.inl (step.prepared.after_queued_subset_before middleQueued)
  | new step =>
      let prepared : PreparedStep before := {
        stackResult := step.stackResult
        coreMarked := step.coreMarked
        stack_eq := step.stack_eq
        core_mark_eq := step.core_mark_eq }
      have afterQueued : endpoint ∈ step.stackAfter.queuedVertices := by
        simpa only [step.output_eq] using queued
      rw [operationalNewEnqueue?_queuedVertices_eq
        step.stack_enqueue_eq] at afterQueued
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at afterQueued
      have oldQueued :
          endpoint ∈ step.stackResult.after.queuedVertices →
            endpoint ∈ before.stack.queuedVertices := by
        intro membership
        apply prepared.after_queued_subset_before
        exact membership
      have reachedTouched : step.search.Touched step.reached := by
        rcases step.route.storedEndpoints with
          ⟨reachedEq, _partnerEq⟩ | ⟨reachedEq, _partnerEq⟩
        · exact Or.inr (Or.inl reachedEq)
        · exact Or.inr (Or.inr reachedEq)
      have partnerTouched : step.search.Touched step.partner := by
        rcases step.route.storedEndpoints with
          ⟨_reachedEq, partnerEq⟩ | ⟨_reachedEq, partnerEq⟩
        · exact Or.inr (Or.inr partnerEq)
        · exact Or.inr (Or.inl partnerEq)
      rcases afterQueued with (inReady | sameReached | samePartner) |
          inWaiting
      · apply Or.inl
        apply oldQueued
        exact List.mem_append_left _ inReady
      · subst endpoint
        exact Or.inr reachedTouched
      · subst endpoint
        exact Or.inr partnerTouched
      · apply Or.inl
        apply oldQueued
        exact List.mem_append_right _ inWaiting
  | wait step =>
      have afterQueued :
          endpoint ∈ step.destination.stackAfter.queuedVertices := by
        simpa only [step.destination.output_eq] using queued
      rcases SequentialStackState.prependWaiting?_some_iff.mp
          step.destination.stack_eq with ⟨prepend⟩
      rcases
          (ProofNetIR.SequentialFigure7.PrependWaitingStep.mem_queuedVertices_iff
            prepend).mp afterQueued with
        sameConclusion | middleQueued
      · have impossible : False :=
          structural.axiomEndpoint_ne_connectiveConclusion
            axiomMembership endpointAt
            (List.mem_of_getElem? step.submitted_par) (by
              subst endpoint
              simp [Link.produces])
        contradiction
      · exact Or.inl
          (step.prepared.after_queued_subset_before middleQueued)
  | forward step =>
      have afterQueued : endpoint ∈ step.stackAfter.queuedVertices := by
        simpa only [step.output_eq] using queued
      rcases
          (ProofNetIR.SequentialFigure7.PrependReadyTopStep.mem_queuedVertices_iff
            step.prependStep).mp afterQueued with
        sameConclusion | middleQueued
      · have impossible : False :=
          structural.axiomEndpoint_ne_connectiveConclusion
            axiomMembership endpointAt
            (List.mem_of_getElem? step.submitted_par) (by
              subst endpoint
              simp [Link.produces])
        contradiction
      · exact Or.inl
          (step.prepared.after_queued_subset_before middleQueued)
  | unifyPayload step =>
      have afterQueued : endpoint ∈ step.stackAfter.queuedVertices := by
        simpa only [step.output_eq] using queued
      rcases (step.mergeStep.mem_queuedVertices_iff).mp afterQueued with
        sameConclusion | middleQueued
      · have impossible : False :=
          structural.axiomEndpoint_ne_connectiveConclusion
            axiomMembership endpointAt
            (List.mem_of_getElem? step.submitted_tensor) (by
              subst endpoint
              simp [Link.produces])
        contradiction
      · exact Or.inl
          (step.prepared.after_queued_subset_before middleQueued)

end DispatchTagEvidence

namespace CanonicalTagHistory

/-- In a canonical dispatcher history, any currently queued endpoint of one
exact submitted axiom was touched by initialization or a recorded `new`.

This theorem is deliberately endpoint-specific and does not classify arbitrary
queued connective conclusions as tagged. -/
theorem queued_axiom_endpoint_touched
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed)
    {axiomIndex : Nat} {left right endpoint : Vertex}
    (exactAxiom :
      certificate.links[axiomIndex]? = some (.axiom left right))
    (endpointAt : endpoint = left ∨ endpoint = right)
    (queued : endpoint ∈ state.stack.queuedVertices) :
    tagHistory.Touched endpoint := by
  induction tagHistory with
  | empty =>
      simp [ReservationState.empty, SequentialStackState.empty,
        SequentialStackState.queuedVertices,
        SequentialStackState.waitingVertices] at queued
      rcases queued with ⟨cell, ⟨_, rfl⟩, membership⟩
      simp [WaitingCell.vertices] at membership
  | init step =>
      have endpointPair :=
        (step.mem_queuedVertices_iff).mp queued
      have endpointTouched : step.result.Touched endpoint := by
        rcases step.route.storedEndpoints with
          ⟨reachedEq, partnerEq⟩ | ⟨reachedEq, partnerEq⟩
        · rcases endpointPair with rfl | rfl
          · exact Or.inr (Or.inl reachedEq)
          · exact Or.inr (Or.inr partnerEq)
        · rcases endpointPair with rfl | rfl
          · exact Or.inr (Or.inr reachedEq)
          · exact Or.inr (Or.inl partnerEq)
      exact endpointTouched
  | later prior evidence induction =>
      rcases evidence.queued_axiom_endpoint_old_or_touched
          structural exactAxiom endpointAt queued with
        oldQueued | newTouched
      · exact Or.inl (induction oldQueued)
      · exact Or.inr newTouched

/-- The reached and partner endpoints of a current exact source-left run are
absent from the pure marked-stack queue determined by any selected ready head.

If either endpoint were still queued, the endpoint-specific history theorem
would make its current input tag true, contradicting the run's exact freshness
field. -/
theorem fresh_run_endpoints_not_markedStack_queued
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed)
    (head : ReadyHeadInput state)
    {runState : UnificationState} {fuel : Nat}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate runState fuel state.tags start
      trace reached partner linkIndex) :
    reached ∉ head.markedStack.queuedVertices ∧
      partner ∉ head.markedStack.queuedVertices := by
  have reachedFresh : state.tags[reached]? = some false :=
    run.traceFresh (List.mem_of_getLast? run.traceLast)
  have partnerFresh : state.tags[partner]? = some false :=
    run.partnerFresh
  constructor
  · intro queued
    have oldQueued : reached ∈ state.stack.queuedVertices :=
      head.markedStack_queued_subset_before queued
    have touched : tagHistory.Touched reached := by
      rcases run.exactAxiom with exactLink | exactLink
      · exact tagHistory.queued_axiom_endpoint_touched structural
          exactLink (Or.inl rfl) oldQueued
      · exact tagHistory.queued_axiom_endpoint_touched structural
          exactLink (Or.inr rfl) oldQueued
    have tagged : state.tags[reached]? = some true :=
      tagHistory.tagged_iff_touched.2 touched
    rw [tagged] at reachedFresh
    contradiction
  · intro queued
    have oldQueued : partner ∈ state.stack.queuedVertices :=
      head.markedStack_queued_subset_before queued
    have touched : tagHistory.Touched partner := by
      rcases run.exactAxiom with exactLink | exactLink
      · exact tagHistory.queued_axiom_endpoint_touched structural
          exactLink (Or.inr rfl) oldQueued
      · exact tagHistory.queued_axiom_endpoint_touched structural
          exactLink (Or.inl rfl) oldQueued
    have tagged : state.tags[partner]? = some true :=
      tagHistory.tagged_iff_touched.2 touched
    rw [tagged] at partnerFresh
    contradiction

/-- Canonical tag/queue history, the complete state invariant, and one exact
source-left run package the local source-region obligations for `new`.

This construction assumes the exact run.  It does not derive that run from
`NewGuard`, assert that another executor call succeeds, or prove progress. -/
def newSourceRegionInputOfRun
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {trace : List Vertex} {reached partner : Vertex} {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate guard.head.markedCore
      certificate.formulas.size before.tags guard.tensor.mate
      trace reached partner linkIndex) :
    NewSourceRegionInput certificate before where
  guard := guard
  trace := trace
  reached := reached
  partner := partner
  linkIndex := linkIndex
  run := run
  reached_not_queued :=
    (tagHistory.fresh_run_endpoints_not_markedStack_queued
      invariant.structural guard.head run).1
  partner_not_queued :=
    (tagHistory.fresh_run_endpoints_not_markedStack_queued
      invariant.structural guard.head run).2
  fresh_capacity := by
    have formulaCapacity :=
      tagHistory.fresh_terminal_capacity invariant.structural run
    change before.stack.nextAge < before.stack.waiting.size
    rw [invariant.stack_wellShaped.waiting_size]
    exact formulaCapacity

/-- A canonical history upgrades the exact route in `NewInput` to the complete
local source-region package. -/
theorem newSourceRegionInput_of_newInput
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (input : NewInput certificate before) :
    Nonempty (NewSourceRegionInput certificate before) := by
  rcases input.route.toFreshSourceLeftRun invariant.structural with ⟨run⟩
  exact ⟨tagHistory.newSourceRegionInputOfRun invariant input.guard run⟩

/-- In a canonical history, the existing exact-route necessary input entails
local input-only `new` enabledness.  The indexed execution history supplies
the already-proved future-waiting invariant.

The exact route remains an explicit premise through `NewInputNecessary`; this
is not a `NewGuard`-sufficiency, reachability, progress, or totality theorem. -/
theorem newEnabled_of_inputNecessary
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (necessary : NewInputNecessary certificate before) :
    NewEnabled certificate before := by
  rcases necessary with ⟨input⟩
  rcases tagHistory.newSourceRegionInput_of_newInput invariant input with
    ⟨sourceRegion⟩
  exact sourceRegion.newEnabled invariant history.futureWaitingUndefined

/-- On a state equipped with its exact canonical history and complete scheduler
invariant, the current input-only `new` criterion is exactly the older
exact-route necessary input.  This equivalence is history-indexed; it does not
make `NewGuard` sufficient. -/
theorem newEnabled_iff_inputNecessary
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before) :
    NewEnabled certificate before ↔
      NewInputNecessary certificate before := by
  constructor
  · exact NewEnabled.inputNecessary
  · exact tagHistory.newEnabled_of_inputNecessary invariant

end CanonicalTagHistory

/-- A certified dispatcher-reachable state whose exact-route necessary `new`
input holds is locally `NewEnabled`.

Reachability supplies only the already-proved canonical history, state
invariant, and future-cell invariant.  The theorem still assumes
`NewInputNecessary` and therefore proves neither exhaustive enabledness nor
dispatcher progress or totality. -/
theorem ReachableByImplementedDispatcher.newEnabled_of_inputNecessary
    {certificate : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate state)
    (structural : certificate.StructurallyWellFormed)
    (necessary : NewInputNecessary certificate state) :
    NewEnabled certificate state := by
  rcases reachable with ⟨history⟩
  rcases history.hasCanonicalTagHistory with ⟨tagHistory⟩
  exact tagHistory.newEnabled_of_inputNecessary
    (history.schedulerInvariant structural) necessary

/-- On a certified dispatcher-reachable state, `NewEnabled` is equivalent to
the exact-route necessary input.  The theorem does not characterize
`NewGuard`, dispatcher progress, or dispatcher totality. -/
theorem ReachableByImplementedDispatcher.newEnabled_iff_inputNecessary
    {certificate : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate state)
    (structural : certificate.StructurallyWellFormed) :
    NewEnabled certificate state ↔
      NewInputNecessary certificate state := by
  constructor
  · exact NewEnabled.inputNecessary
  · exact reachable.newEnabled_of_inputNecessary structural

end SequentialFigure7

end ProofNetIR
