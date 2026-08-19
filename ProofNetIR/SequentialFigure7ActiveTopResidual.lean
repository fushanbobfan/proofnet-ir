/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderMarkedTensorPredecessorHistory

/-!
# Active-top ready-head residual

This module isolates the remaining structural ready-head obligation after exact
implemented-dispatcher history has eliminated every ready-head rule residual.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- The live component at the active scheduler boundary has no raw-unmarked
frontier occurrence. -/
def ActiveTopDrained (state : ReservationState) : Prop :=
  ∃ rawAge component,
    state.stack.sigma.getLast? = some rawAge ∧
      state.core.components[rawAge]? = some (some component) ∧
        ∀ vertex, vertex ∈ component.frontier →
          state.core.marks[vertex]? ≠ some none

/-- A started invariant state has an exact active boundary, active ready
bucket, and live-component interpretation of that bucket. -/
private theorem activeTop_exact
    {state : ReservationState} {carrierSize : Nat}
    (wellShaped : state.stack.WellShaped carrierSize)
    (readyExact : ReadyBucketFrontierExact state)
    (started : 0 < state.stack.nextAge) :
    ∃ rawAge bucket component,
      state.stack.sigma.getLast? = some rawAge ∧
        state.stack.ready.getLast? = some bucket ∧
          state.core.components[rawAge]? = some (some component) ∧
            ∀ vertex,
              vertex ∈ bucket ↔
                vertex ∈ component.frontier ∧
                  state.core.marks[vertex]? = some none := by
  have sigmaNonempty : state.stack.sigma ≠ [] := by
    intro sigmaEmpty
    have nextAgeZero : state.stack.nextAge = 0 :=
      wellShaped.sigma_partition.empty_iff.mp sigmaEmpty
    exact (Nat.ne_of_gt started) nextAgeZero
  let rawAge := state.stack.sigma.getLast sigmaNonempty
  have sigmaTop : state.stack.sigma.getLast? = some rawAge :=
    List.getLast?_eq_some_getLast sigmaNonempty
  have readyNonempty : state.stack.ready ≠ [] := by
    intro readyEmpty
    have sigmaLengthZero : state.stack.sigma.length = 0 := by
      have aligned := wellShaped.ready_aligned
      rw [readyEmpty] at aligned
      simpa using aligned.symm
    apply sigmaNonempty
    cases sigmaEquation : state.stack.sigma with
    | nil => rfl
    | cons head tail =>
        simp [sigmaEquation] at sigmaLengthZero
  let bucket := state.stack.ready.getLast readyNonempty
  have readyTop : state.stack.ready.getLast? = some bucket :=
    List.getLast?_eq_some_getLast readyNonempty
  rcases List.getLast?_eq_some_iff.mp sigmaTop with
    ⟨sigmaPrefix, sigmaDecomposition⟩
  rcases List.getLast?_eq_some_iff.mp readyTop with
    ⟨readyPrefix, readyDecomposition⟩
  have prefixLengths : readyPrefix.length = sigmaPrefix.length := by
    have aligned := wellShaped.ready_aligned
    rw [readyDecomposition, sigmaDecomposition] at aligned
    simpa using aligned
  have sigmaLookup :
      state.stack.sigma[sigmaPrefix.length]? = some rawAge := by
    rw [sigmaDecomposition]
    simp
  have readyLookup :
      state.stack.ready[sigmaPrefix.length]? = some bucket := by
    rw [readyDecomposition, ← prefixLengths]
    simp
  rcases readyExact sigmaLookup readyLookup with
    ⟨component, componentLookup, exactMembership⟩
  exact ⟨rawAge, bucket, component, sigmaTop, readyTop,
    componentLookup, exactMembership⟩

/-- In a started scheduler-invariant state, absence of a ready head is exactly
the structural residual that the active live component has no raw-unmarked
frontier occurrence. -/
theorem SchedulerInvariant.no_readyHead_iff_activeTopDrained
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    (started : 0 < state.stack.nextAge) :
    (¬ Nonempty (ReadyHeadInput state)) ↔ ActiveTopDrained state := by
  rcases activeTop_exact invariant.stack_wellShaped
      invariant.ready_bucket_frontier_exact started with
    ⟨rawAge, bucket, component, sigmaTop, readyTop,
      componentLookup, exactMembership⟩
  constructor
  · intro noHead
    cases bucket with
    | nil =>
        refine ⟨rawAge, component, sigmaTop, componentLookup, ?_⟩
        intro vertex frontier unmarked
        have inEmpty : vertex ∈ ([] : List Vertex) :=
          (exactMembership vertex).mpr ⟨frontier, unmarked⟩
        simp at inEmpty
    | cons vertex readyTail =>
        exfalso
        apply noHead
        exact ⟨{
          vertex
          readyTail
          rawAge
          top_ready := readyTop
          sigma_top := sigmaTop }⟩
  · rintro ⟨drainedRawAge, drainedComponent, drainedSigmaTop,
      drainedComponentLookup, frontierFree⟩ ⟨head⟩
    have rawAgeEq : rawAge = drainedRawAge :=
      Option.some.inj (sigmaTop.symm.trans drainedSigmaTop)
    subst drainedRawAge
    have componentEq : component = drainedComponent :=
      Option.some.inj
        (Option.some.inj
          (componentLookup.symm.trans drainedComponentLookup))
    subst drainedComponent
    have bucketEq : bucket = head.vertex :: head.readyTail :=
      Option.some.inj (readyTop.symm.trans head.top_ready)
    have headMembership : head.vertex ∈ component.frontier ∧
        state.core.marks[head.vertex]? = some none :=
      (exactMembership head.vertex).mp (by simp [bucketEq])
    exact frontierFree head.vertex headMembership.1 headMembership.2

/-- A started reachable state satisfies the disjunction of one exact canonical
dispatcher step and the active-top structural residual. The alternatives are
not claimed to be exclusive, and the residual is not interpreted as semantic
completion. -/
theorem ReachableByImplementedDispatcher.dispatch_or_activeTopDrained
    {certificate : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate state)
    (correct : certificate.DeclarativelyCorrect)
    (started : 0 < state.stack.nextAge) :
    let invariant := reachable.schedulerInvariant correct.1
    (∃ result : Figure7DispatchResult,
        dispatch? certificate state invariant = some result) ∨
      ActiveTopDrained state := by
  let invariant := reachable.schedulerInvariant correct.1
  change (∃ result : Figure7DispatchResult,
      dispatch? certificate state invariant = some result) ∨
    ActiveTopDrained state
  by_cases headExists : Nonempty (ReadyHeadInput state)
  · left
    rcases headExists with ⟨head⟩
    exact reachable.readyHead_dispatch correct head
  · right
    exact
      (SchedulerInvariant.no_readyHead_iff_activeTopDrained
        invariant started).mp headExists

end SequentialFigure7
end ProofNetIR
