/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7FutureWorkExactLocation

/-!
# Figure-7 future-work queue status

This module relates the scheduler's flattened queue to proof-relevant future
work, orders future work outside the active occurrence carrier below the active
boundary, and classifies an outside raw-unmarked vertex by its current
scheduler status.

These results classify the current state only. They do not establish a unique
future-work boundary, historical non-production, a next dispatcher rule,
progress, completion, or termination.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- Current scheduler status of an in-bounds raw-unmarked vertex relative to a
supplied owned list. The classifier below connects that list to the active
occurrence carrier. -/
def UnmarkedOutsideActiveSchedulerStatus
    (certificate : Certificate) (state : ReservationState)
    (input : ReadyHeadInput state) (owned : List Vertex)
    (vertex : Vertex) : Prop :=
  state.core.marks[vertex]? = some none ∧
    vertex ∉ owned ∧
    ((vertex ∉ state.stack.queuedVertices ∧
        vertex ∉ state.core.liveFrontierVertices ∧
        ¬ Produced state vertex) ∨
      ∃ boundary,
        FutureWorkAt state boundary vertex ∧
          boundary < input.rawAge ∧
          FutureWorkAtExactSchedulerLocation certificate state boundary vertex)

namespace FutureWorkAt

/-- Future work outside the active occurrence carrier belongs to a strictly
older scheduler boundary. -/
theorem boundary_lt_active_of_not_owned
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    {boundary : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt state boundary vertex)
    (notOwned : vertex ∉ owned) :
    boundary < input.rawAge := by
  have boundaryNeActive : boundary ≠ input.rawAge := by
    intro sameBoundary
    subst boundary
    cases work with
    | ready sigmaAt readyAt member =>
        rcases invariant.ready_bucket_frontier_exact sigmaAt readyAt with
          ⟨readyComponent, readyLookup, exactMembership⟩
        have componentEq : readyComponent = component :=
          Option.some.inj
            (Option.some.inj
              (readyLookup.symm.trans componentLookup))
        subst readyComponent
        have vertexFrontier : vertex ∈ component.frontier :=
          ((exactMembership vertex).mp member).1
        exact notOwned
          (occurrence.derivation.frontier_subset_owned vertex vertexFrontier)
    | waiting waitingAt _member =>
        have activeUndefined :
            state.stack.waiting[input.rawAge]? = some .undefined :=
          invariant.stack_operationalWaitingDomain.active_undefined
            invariant.stack_wellShaped input.sigma_top
        rw [activeUndefined] at waitingAt
        simp at waitingAt
  have boundaryMembership : boundary ∈ state.stack.sigma :=
    work.rawAge_mem_sigma invariant
  rcases List.getLast?_eq_some_iff.mp input.sigma_top with
    ⟨sigmaPrefix, sigmaEq⟩
  have increasing :=
    invariant.stack_wellShaped.sigma_partition.strictIncreasing
  rw [sigmaEq] at boundaryMembership increasing
  simp only [List.mem_append, List.mem_singleton] at boundaryMembership
  rcases boundaryMembership with inPrefix | same
  · exact (List.pairwise_append.mp increasing).2.2 boundary inPrefix
      input.rawAge (by simp)
  · exact False.elim (boundaryNeActive same)

end FutureWorkAt
end SequentialFigure7

namespace SequentialSchedulerBridge
namespace SchedulerInvariant

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialFigure7

/-- Flattened queue membership is equivalent to a proof-relevant `FutureWorkAt`
witness at some scheduler boundary. -/
theorem mem_queued_iff_exists_futureWorkAt
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {vertex : Vertex} :
    vertex ∈ state.stack.queuedVertices ↔
      ∃ boundary, FutureWorkAt state boundary vertex := by
  constructor
  · intro queued
    unfold SequentialStackState.queuedVertices at queued
    rcases List.mem_append.mp queued with readyMembership | waitingMembership
    · rcases List.mem_flatten.mp readyMembership with
        ⟨bucket, bucketMembership, vertexMembership⟩
      rcases List.getElem?_of_mem bucketMembership with
        ⟨position, readyAt⟩
      have positionBound : position < state.stack.ready.length :=
        (List.getElem?_eq_some_iff.mp readyAt).1
      have sigmaBound : position < state.stack.sigma.length := by
        rw [← invariant.stack_wellShaped.ready_aligned]
        exact positionBound
      refine ⟨state.stack.sigma[position], .ready ?_ readyAt vertexMembership⟩
      exact List.getElem?_eq_getElem sigmaBound
    · unfold SequentialStackState.waitingVertices at waitingMembership
      rcases List.mem_flatMap.mp waitingMembership with
        ⟨cell, cellMembership, vertexMembership⟩
      cases cell with
      | undefined =>
          simp [WaitingCell.vertices] at vertexMembership
      | initialized payload =>
          rcases List.getElem?_of_mem cellMembership with
            ⟨boundary, waitingAtList⟩
          have waitingAt :
              state.stack.waiting[boundary]? =
                some (.initialized payload) := by
            rw [← Array.getElem?_toList]
            exact waitingAtList
          exact ⟨boundary, .waiting waitingAt (by
            simpa [WaitingCell.vertices] using vertexMembership)⟩
  · rintro ⟨_boundary, work⟩
    exact work.mem_queued

/-- An in-bounds raw-unmarked vertex outside the active carrier is either
absent from the current queue and observable production domains or exact work
at a strictly older scheduler boundary. -/
theorem unmarkedOutsideActiveSchedulerStatus
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {vertex : Vertex}
    (unmarked : state.core.marks[vertex]? = some none)
    (outside : vertex ∉ owned) :
    UnmarkedOutsideActiveSchedulerStatus certificate state input owned vertex := by
  refine ⟨unmarked, outside, ?_⟩
  by_cases queued : vertex ∈ state.stack.queuedVertices
  · right
    rcases (invariant.mem_queued_iff_exists_futureWorkAt).mp queued with
      ⟨boundary, work⟩
    exact ⟨boundary, work,
      work.boundary_lt_active_of_not_owned input invariant componentLookup
        occurrence outside,
      work.exactSchedulerLocation invariant⟩
  · left
    have notLive : vertex ∉ state.core.liveFrontierVertices := by
      intro live
      exact queued
        (invariant.unmarked_liveFrontier_mem_queued live unmarked)
    have notProduced : ¬ Produced state vertex := by
      intro produced
      rcases produced with marked | live
      · rcases marked with ⟨age, markedAt⟩
        rw [unmarked] at markedAt
        simp at markedAt
      · exact notLive live
    exact ⟨queued, notLive, notProduced⟩

end SchedulerInvariant
end SequentialSchedulerBridge
end ProofNetIR
