/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import
  ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryContinuationWaiting

/-!
# Figure-7 waiting continuation producer orientation

Orients an active-representative target inside an exact older waiting producer
without importing carrier, history, or ready-tail assumptions.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

private theorem markedRepresentativeEqBoundary
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {vertex : Vertex} {rawAge boundary : RawTokenAge}
    (marked : state.core.marks[vertex]? = some (some rawAge))
    (boundaryLookup :
      sigmaBoundary? state.stack.sigma rawAge = some boundary) :
    state.core.representative rawAge = boundary := by
  have stackMarked : state.stack.marks[vertex]? = some (some rawAge) := by
    rw [← invariant.realizesSigma.marks_eq]
    exact marked
  have rawAgeBound : rawAge < state.stack.nextAge :=
    invariant.stack_wellShaped.assigned_age_bound vertex rawAge stackMarked
  have realized := invariant.realizesSigma.representative_eq_boundary rawAgeBound
  exact Option.some.inj (realized.symm.trans boundaryLookup)

private theorem waitingProducerOrientation
    {certificate : Certificate} {target : Vertex}
    (consumer : ConnectiveBelow certificate target)
    (structural : certificate.StructurallyWellFormed)
    {linkIndex : Nat} {left right olderPremise youngerPremise : Vertex}
    (linkLookup :
      certificate.links[linkIndex]? =
        some (.par left right consumer.conclusion))
    (premiseOrientation :
      (olderPremise = left ∧ youngerPremise = right) ∨
        (olderPremise = right ∧ youngerPremise = left)) :
    (target = olderPremise ∧ consumer.mate = youngerPremise) ∨
      (target = youngerPremise ∧ consumer.mate = olderPremise) := by
  have consumerMembership : consumer.submittedLink ∈ certificate.links :=
    List.mem_of_getElem? consumer.link_eq
  have consumerProduces :
      consumer.submittedLink.produces consumer.conclusion = true := by
    cases kindEq : consumer.kind <;>
      simp [ConnectiveBelow.submittedLink, SequentialConnectiveKind.asLink,
        kindEq, Link.produces]
  have sameLink :=
    UnificationState.StructurallyWellFormed.producerLink_unique
      structural consumerMembership consumerProduces
        (List.mem_of_getElem? linkLookup)
        (by simp [Link.produces])
  cases kindEq : consumer.kind <;> cases sideEq : consumer.side <;>
    simp [ConnectiveBelow.submittedLink, SequentialConnectiveKind.asLink,
      kindEq] at sameLink
  all_goals
    rcases premiseOrientation with orientation | orientation
    · rcases orientation with ⟨rfl, rfl⟩
      rcases sameLink with ⟨rfl, rfl, _⟩
      have premiseEq := consumer.premise_eq
      simp_all [TensorPremiseSide.premise, TensorPremiseSide.mate,
        ConnectiveBelow.mate]
    · rcases orientation with ⟨rfl, rfl⟩
      rcases sameLink with ⟨rfl, rfl, _⟩
      have premiseEq := consumer.premise_eq
      simp_all [TensorPremiseSide.premise, TensorPremiseSide.mate,
        ConnectiveBelow.mate]

namespace FutureWorkAtExactWaitingLocation

/--
An exact older waiting conclusion whose consumed target is represented at an
active boundary has that target as its younger premise and the opposite mate
as its older premise.
-/
theorem activeTargetProducerOrientation
    {certificate : Certificate} {state : ReservationState}
    {active boundary targetAge : RawTokenAge} {target : Vertex}
    (invariant : SchedulerInvariant certificate state)
    (consumer : ConnectiveBelow certificate target)
    (location :
      FutureWorkAtExactWaitingLocation certificate state boundary
        consumer.conclusion)
    (targetMarked : state.core.marks[target]? = some (some targetAge))
    (targetRepresentative : state.core.representative targetAge = active)
    (boundaryOlder : boundary < active) :
    ∃ (payload : List Vertex) (linkIndex : Nat) (left right : Vertex)
        (olderPremise youngerPremise : Vertex)
        (olderAge youngerAge youngerBoundary : RawTokenAge),
      state.stack.waiting[boundary]? = some (.initialized payload) ∧
        consumer.conclusion ∈ payload ∧
        certificate.links[linkIndex]? =
          some (.par left right consumer.conclusion) ∧
        (SequentialUnification.sourceIndex certificate)[consumer.conclusion]? =
          some
            [{ linkIndex := linkIndex,
               link := .par left right consumer.conclusion }] ∧
        state.core.marks[consumer.conclusion]? = some none ∧
        ((olderPremise = left ∧ youngerPremise = right) ∨
          (olderPremise = right ∧ youngerPremise = left)) ∧
        state.core.marks[olderPremise]? = some (some olderAge) ∧
        state.core.marks[youngerPremise]? = some (some youngerAge) ∧
        sigmaBoundary? state.stack.sigma olderAge = some boundary ∧
        sigmaBoundary? state.stack.sigma youngerAge = some youngerBoundary ∧
        boundary < youngerBoundary ∧
        target = youngerPremise ∧
        consumer.mate = olderPremise ∧
        targetAge = youngerAge ∧
        youngerBoundary = active ∧
        state.core.representative olderAge = boundary ∧
        state.core.representative youngerAge = active := by
  rcases location with
    ⟨payload, linkIndex, left, right, olderPremise, youngerPremise,
      olderAge, youngerAge, youngerBoundary, waitingAt, member, linkLookup,
      sourceLookup, unmarked, premiseOrientation, olderMarked, youngerMarked,
      olderBoundary, youngerBoundaryLookup, boundaryLt⟩
  have olderRepresentative :=
    markedRepresentativeEqBoundary invariant olderMarked olderBoundary
  have youngerRepresentative :=
    markedRepresentativeEqBoundary invariant youngerMarked
      youngerBoundaryLookup
  rcases waitingProducerOrientation consumer invariant.structural linkLookup
      premiseOrientation with targetOlder | targetYounger
  · rcases targetOlder with ⟨targetOlder, _mateYounger⟩
    have targetAgeEq : targetAge = olderAge := by
      have marksEq := targetMarked.symm.trans
        (by simpa [← targetOlder] using olderMarked)
      exact Option.some.inj (Option.some.inj marksEq)
    have boundaryEqActive : boundary = active := by
      rw [← olderRepresentative, ← targetAgeEq]
      exact targetRepresentative
    exact False.elim ((Nat.ne_of_lt boundaryOlder) boundaryEqActive)
  · rcases targetYounger with ⟨targetYounger, mateOlder⟩
    have targetAgeEq : targetAge = youngerAge := by
      have marksEq := targetMarked.symm.trans
        (by simpa [← targetYounger] using youngerMarked)
      exact Option.some.inj (Option.some.inj marksEq)
    have youngerBoundaryActive : youngerBoundary = active := by
      rw [← youngerRepresentative, ← targetAgeEq]
      exact targetRepresentative
    exact ⟨payload, linkIndex, left, right, olderPremise, youngerPremise,
      olderAge, youngerAge, youngerBoundary, waitingAt, member, linkLookup,
      sourceLookup, unmarked, premiseOrientation, olderMarked, youngerMarked,
      olderBoundary, youngerBoundaryLookup, boundaryLt, targetYounger,
      mateOlder, targetAgeEq, youngerBoundaryActive, olderRepresentative,
      by simpa [youngerBoundaryActive] using youngerRepresentative⟩

end FutureWorkAtExactWaitingLocation

end SequentialFigure7
end ProofNetIR
