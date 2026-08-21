/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalTemporal
import ProofNetIR.SequentialFigure7ActiveTopDebtParentExternalEndpointCrossing
import ProofNetIR.SequentialFigure7ActiveTopDebtParentExternalReentryTarget

/-!
# Figure-7 active-mate waiting external commitment re-entry

The two external temporal endpoints forced by an active-owned exact waiting
mate now retain their precise older commitment split, an active-carrier
boundary crossing, a theorem-derived reverse re-entry, and the selected-or-marked
historical failure classification. Reversing the crossing works uniformly for ready,
waiting, and marked endpoints, so this interface never widens back to the raw
or waiting branches of the older shared commitment carrier.

The result carrier stores crossing and re-entry evidence separately; it does
not equate arbitrary stored witnesses.

This is a failure reduction. It does not eliminate the selected or marked
re-entry targets, identify a distinct payer, derive the history-tail law, or
establish completion, progress, termination, or totality.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- Reverse an owned-to-external crossing into an exact external-to-owned
re-entry, reversing the retained directed edge at the same time. -/
theorem ActiveCarrierExternalEndpointCrossing.reentry
    {certificate : Certificate} {owned : List Vertex} {endpoint : Vertex}
    (crossing :
      ActiveCarrierExternalEndpointCrossing certificate owned endpoint) :
    ActiveCarrierExternalEndpointReentry certificate owned endpoint := by
  rcases crossing with
    ⟨path, directed, startOwned, pathFinishes, directedMembership,
      sourceOwned, targetOutside⟩
  refine ⟨path.reverse, directed.reverse, ?_, ?_, ?_, ?_, ?_⟩
  · exact pathFinishes
  · exact startOwned
  · change directed.reverse ∈
      Graph.EdgeWalk.reverseTraversal path.traversed
    simp only [Graph.EdgeWalk.reverseTraversal, List.mem_map, List.mem_reverse]
    exact ⟨directed, directedMembership, rfl⟩
  · simpa using targetOutside
  · simpa using sourceOwned

private theorem ReadyHeadInput.selectedOwnedAccounted
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned) :
    input.vertex ∈ owned ∧
      Certificate.OwnedOccurrenceAccounted state.core input.rawAge component
        owned := by
  rcases input.activeComponent invariant with
    ⟨actual, _actualUsed, actualOwned, actualLookup, actualOccurrence,
      actualAccounted, selectedOwned, _activeRoot⟩
  have actualEq : actual = component :=
    Option.some.inj
      (Option.some.inj (actualLookup.symm.trans componentLookup))
  subst actual
  have ownedEq : actualOwned = owned :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      actualOccurrence.derivation occurrence.derivation
  constructor
  · simpa [ownedEq] using selectedOwned
  · simpa [ownedEq] using actualAccounted

private theorem activeSelected_externalEndpointCrossing
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (connected : certificate.ReferenceSwitchingConnected)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    (selectedOwned : input.vertex ∈ owned)
    {endpoint : Vertex}
    (endpointBound : endpoint < certificate.formulas.size)
    (endpointOutside : endpoint ∉ owned) :
    ActiveCarrierExternalEndpointCrossing certificate owned endpoint := by
  have selectedBound : input.vertex < certificate.formulas.size :=
    occurrence.derivation.owned_inBounds invariant.structural input.vertex
      selectedOwned
  have graphSelectedBound :
      input.vertex < certificate.referenceSwitchingGraph.vertexCount := by
    simpa [Certificate.referenceSwitchingGraph, Certificate.fullGraph,
      Graph.retainEdges] using selectedBound
  have graphEndpointBound :
      endpoint < certificate.referenceSwitchingGraph.vertexCount := by
    simpa [Certificate.referenceSwitchingGraph, Certificate.fullGraph,
      Graph.retainEdges] using endpointBound
  have zeroToSelected :
      certificate.referenceSwitchingGraph.Walk 0 input.vertex :=
    connected.2 input.vertex graphSelectedBound
  have zeroToEndpoint :
      certificate.referenceSwitchingGraph.Walk 0 endpoint :=
    connected.2 endpoint graphEndpointBound
  have selectedToEndpoint := zeroToSelected.symm.trans zeroToEndpoint
  rcases selectedToEndpoint.toSimple with ⟨_steps, _visited, simple⟩
  rcases simple.liftToEdgeSimplePathWithEdges
      (fun _ membership ↦ membership) with
    ⟨path, pathStarts, pathFinishes, _pathVertices, _pathEdges⟩
  have pathStartOwned : path.start ∈ owned := by
    simpa [pathStarts] using selectedOwned
  have finishMembership : path.finish ∈ path.vertices := by
    simpa [Graph.EdgeSimplePath.vertices] using
      path.walk.finish_mem_visitedVertices
  have finishRejected : owned.contains path.finish = false := by
    simpa [pathFinishes] using endpointOutside
  rcases path.exists_traversed_boundary_of_start_true
      (fun vertex ↦ owned.contains vertex) (by simpa using pathStartOwned)
      ⟨path.finish, finishMembership, finishRejected⟩ with
    ⟨directed, directedMembership, sourceAccepted, targetRejected⟩
  exact ⟨path, directed, pathStartOwned, pathFinishes, directedMembership,
    by simpa using sourceAccepted, by simpa using targetRejected⟩

/-- The exact two-case external endpoint left by an active waiting mate after
retaining its older commitment split, crossing, re-entry, and
failure-conditioned historical classification. The refinement theorem derives
its re-entry by reversing its crossing; this carrier stores the two witnesses
separately. -/
inductive ActiveMateWaitingParentExternalCommitmentReentryFailureOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) {terminal : Vertex}
    (consumer : ConnectiveBelow certificate terminal) : Prop where
  | olderFuture
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion)
      (older : boundary < input.rawAge)
      (outside : consumer.conclusion ∉ owned)
      (commitmentSplit :
        tagHistory.StrictOlderCommitmentSplit boundary input.rawAge)
      (crossing :
        ActiveCarrierExternalEndpointCrossing certificate owned
          consumer.conclusion)
      (reentry :
        ActiveCarrierExternalEndpointReentry certificate owned
          consumer.conclusion)
      (failureStatus :
        ActiveCarrierExternalReentryFailureHistoricalStatus tagHistory input
          component owned consumer.conclusion) :
      ActiveMateWaitingParentExternalCommitmentReentryFailureOutcome
        tagHistory input component owned consumer
  | olderMarked
      (conclusionAge : RawTokenAge)
      (marked :
        state.core.marks[consumer.conclusion]? = some (some conclusionAge))
      (olderRepresentative :
        state.core.representative conclusionAge < input.rawAge)
      (outside : consumer.conclusion ∉ owned)
      (commitmentSplit : tagHistory.StrictOlderCommitmentSplit
        (state.core.representative conclusionAge) input.rawAge)
      (crossing :
        ActiveCarrierExternalEndpointCrossing certificate owned
          consumer.conclusion)
      (reentry :
        ActiveCarrierExternalEndpointReentry certificate owned
          consumer.conclusion)
      (failureStatus :
        ActiveCarrierExternalReentryFailureHistoricalStatus tagHistory input
          component owned consumer.conclusion) :
      ActiveMateWaitingParentExternalCommitmentReentryFailureOutcome
        tagHistory input component owned consumer

namespace ActiveMateWaitingParentExternalTemporalOutcome

/-- Refine an active waiting mate's two external temporal endpoints through
the exact older commitment, boundary crossing, reverse re-entry, and
failure-conditioned historical target pipeline. -/
theorem commitmentReentryFailureOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    (outcome : ActiveMateWaitingParentExternalTemporalOutcome certificate state
      input owned consumer)
    (tagHistory : CanonicalTagHistory certificate history)
    (connected : certificate.ReferenceSwitchingConnected)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveMateWaitingParentExternalCommitmentReentryFailureOutcome tagHistory
      input component owned consumer := by
  rcases input.selectedOwnedAccounted invariant componentLookup occurrence with
    ⟨selectedOwned, accounted⟩
  cases outcome with
  | olderFuture boundary work older outside =>
      have firstMembership : boundary ∈ state.stack.sigma :=
        work.rawAge_mem_sigma invariant
      have commitmentSplit :
          tagHistory.StrictOlderCommitmentSplit boundary input.rawAge :=
        tagHistory.strictOlderCommitmentSplit_to_top invariant firstMembership
          input.sigma_top older
      have endpointUnmarked :
          state.core.marks[consumer.conclusion]? = some none :=
        invariant.queued_vertices_unmarked consumer.conclusion work.mem_queued
      have coreMarksSize :
          state.core.marks.size = certificate.formulas.size := by
        rw [invariant.realizesSigma.marks_eq]
        exact invariant.stack_wellShaped.marks_size
      have endpointBound : consumer.conclusion < certificate.formulas.size := by
        rcases Array.getElem?_eq_some_iff.mp endpointUnmarked with
          ⟨markBound, _markValue⟩
        simpa [coreMarksSize] using markBound
      have crossing :=
        activeSelected_externalEndpointCrossing input connected invariant
          occurrence selectedOwned endpointBound outside
      have reentry := crossing.reentry
      exact .olderFuture boundary work older outside commitmentSplit crossing
        reentry
        (reentry.targetFailureHistoricalStatus tagHistory input invariant
          componentLookup occurrence accounted noTail)
  | olderMarked conclusionAge marked olderRepresentative outside =>
      have stackMarked :
          state.stack.marks[consumer.conclusion]? =
            some (some conclusionAge) := by
        rw [← invariant.realizesSigma.marks_eq]
        exact marked
      have ageBound : conclusionAge < state.stack.nextAge :=
        invariant.stack_wellShaped.assigned_age_bound consumer.conclusion
          conclusionAge stackMarked
      have boundaryLookup :=
        invariant.realizesSigma.representative_eq_boundary ageBound
      have firstMembership :
          state.core.representative conclusionAge ∈ state.stack.sigma :=
        sigmaBoundary?_mem boundaryLookup
      have commitmentSplit : tagHistory.StrictOlderCommitmentSplit
          (state.core.representative conclusionAge) input.rawAge :=
        tagHistory.strictOlderCommitmentSplit_to_top invariant firstMembership
          input.sigma_top olderRepresentative
      have coreMarksSize :
          state.core.marks.size = certificate.formulas.size := by
        rw [invariant.realizesSigma.marks_eq]
        exact invariant.stack_wellShaped.marks_size
      have endpointBound : consumer.conclusion < certificate.formulas.size := by
        rcases Array.getElem?_eq_some_iff.mp marked with
          ⟨markBound, _markValue⟩
        simpa [coreMarksSize] using markBound
      have crossing :=
        activeSelected_externalEndpointCrossing input connected invariant
          occurrence selectedOwned endpointBound outside
      have reentry := crossing.reentry
      exact .olderMarked conclusionAge marked olderRepresentative outside
        commitmentSplit crossing reentry
        (reentry.targetFailureHistoricalStatus tagHistory input invariant
          componentLookup occurrence accounted noTail)

end ActiveMateWaitingParentExternalTemporalOutcome

end SequentialFigure7
end ProofNetIR
