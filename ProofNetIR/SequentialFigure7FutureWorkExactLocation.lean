/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CrossRepresentativeInvariant

/-!
# Figure-7 exact future-work locations

This module exposes the exact scheduler semantics hidden by `FutureWorkAt`.
Ready work is tied to its sigma slot, ready bucket, live component frontier,
and raw-unmarked conclusion.  Waiting work is tied to its exact waiting cell,
submitted par producer, oriented marked premises, and strictly younger active
boundary.  Consequently, both premises of any connective conclusion stored as
future work have concrete raw marks.

The results classify already-present future work under a scheduler invariant.
They do not create future work, choose a dispatcher branch, or imply progress,
termination, or completion.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- Exact scheduler semantics behind one future-work occurrence. -/
inductive FutureWorkAtExactSchedulerLocation
    (certificate : Certificate) (state : ReservationState) :
    RawTokenAge → Vertex → Prop where
  | ready {position : Nat} {boundary : RawTokenAge}
      {bucket : List Vertex} {vertex : Vertex}
      {component : UnificationComponent}
      (sigmaAt : state.stack.sigma[position]? = some boundary)
      (readyAt : state.stack.ready[position]? = some bucket)
      (member : vertex ∈ bucket)
      (componentLookup :
        state.core.components[boundary]? = some (some component))
      (frontier : vertex ∈ component.frontier)
      (unmarked : state.core.marks[vertex]? = some none) :
      FutureWorkAtExactSchedulerLocation certificate state boundary vertex
  | waiting {boundary : RawTokenAge} {payload : List Vertex}
      {vertex : Vertex} {linkIndex : Nat} {left right : Vertex}
      {olderPremise youngerPremise : Vertex}
      {olderAge youngerAge youngerBoundary : RawTokenAge}
      (waitingAt : state.stack.waiting[boundary]? =
        some (.initialized payload))
      (member : vertex ∈ payload)
      (linkLookup : certificate.links[linkIndex]? =
        some (.par left right vertex))
      (sourceLookup :
        (SequentialUnification.sourceIndex certificate)[vertex]? =
          some [{ linkIndex := linkIndex, link := .par left right vertex }])
      (unmarked : state.core.marks[vertex]? = some none)
      (premiseOrientation :
        (olderPremise = left ∧ youngerPremise = right) ∨
          (olderPremise = right ∧ youngerPremise = left))
      (olderMarked :
        state.core.marks[olderPremise]? = some (some olderAge))
      (youngerMarked :
        state.core.marks[youngerPremise]? = some (some youngerAge))
      (olderBoundary :
        sigmaBoundary? state.stack.sigma olderAge = some boundary)
      (youngerBoundaryLookup :
        sigmaBoundary? state.stack.sigma youngerAge = some youngerBoundary)
      (boundaryLt : boundary < youngerBoundary) :
      FutureWorkAtExactSchedulerLocation certificate state boundary vertex

/-- Project a future-work occurrence to its exact ready-component or waiting
span semantics. -/
theorem FutureWorkAt.exactSchedulerLocation
    {certificate : Certificate} {state : ReservationState}
    {boundary : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt state boundary vertex)
    (invariant : SchedulerInvariant certificate state) :
    FutureWorkAtExactSchedulerLocation certificate state boundary vertex := by
  cases work with
  | ready sigmaAt readyAt member =>
      rcases invariant.ready_bucket_frontier_exact sigmaAt readyAt with
        ⟨component, componentLookup, exactMembership⟩
      have facts := (exactMembership vertex).mp member
      exact .ready sigmaAt readyAt member componentLookup facts.1 facts.2
  | waiting waitingAt member =>
      rcases invariant.waiting_span_exact waitingAt member with
        ⟨linkIndex, left, right, olderPremise, youngerPremise,
          olderAge, youngerAge, youngerBoundary, linkLookup, sourceLookup,
          unmarked, premiseOrientation, olderMarked, youngerMarked,
          olderBoundary, youngerBoundaryLookup, boundaryLt⟩
      exact .waiting waitingAt member linkLookup sourceLookup unmarked
        premiseOrientation olderMarked youngerMarked olderBoundary
        youngerBoundaryLookup boundaryLt

private theorem mem_liveFrontierVertices
    {state : ReservationState} {index : Nat}
    {component : UnificationComponent} {vertex : Vertex}
    (componentLookup : state.core.components[index]? = some (some component))
    (frontier : vertex ∈ component.frontier) :
    vertex ∈ state.core.liveFrontierVertices := by
  unfold UnificationState.liveFrontierVertices
  apply List.mem_flatMap.mpr
  refine ⟨some component, ?_, ?_⟩
  · exact List.mem_of_getElem? (by simpa using componentLookup)
  · simpa using frontier

/-- Both premises of an exact connective conclusion stored as future work have
concrete raw marks, whether that work is ready or waiting. -/
theorem ConnectiveBelow.premisesMarked_of_futureWork
    {certificate : Certificate} {state : ReservationState} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex)
    {boundary : RawTokenAge}
    (work : FutureWorkAt state boundary consumer.conclusion)
    (invariant : SchedulerInvariant certificate state) :
    (∃ vertexAge,
        state.core.marks[vertex]? = some (some vertexAge)) ∧
      ∃ mateAge,
        state.core.marks[consumer.mate]? = some (some mateAge) := by
  have consumerMembership : consumer.submittedLink ∈ certificate.links :=
    List.mem_of_getElem? consumer.link_eq
  have consumerProduces :
      consumer.submittedLink.produces consumer.conclusion = true := by
    cases kindEq : consumer.kind <;>
      simp [ConnectiveBelow.submittedLink, SequentialConnectiveKind.asLink,
        Link.produces, kindEq]
  cases work with
  | ready sigmaAt readyAt member =>
      rcases invariant.ready_bucket_frontier_exact sigmaAt readyAt with
        ⟨component, componentLookup, exactMembership⟩
      have frontier := (exactMembership consumer.conclusion).mp member |>.1
      have produced : Produced state consumer.conclusion :=
        .inr (mem_liveFrontierVertices componentLookup frontier)
      cases kindEq : consumer.kind with
      | tensor =>
          have premises :=
            invariant.produced_premises_marked consumerMembership
          simp [ConnectiveBelow.submittedLink,
            SequentialConnectiveKind.asLink, kindEq] at premises
          have premises := premises produced
          cases sideEq : consumer.side with
          | storedLeft =>
              have vertexEq : vertex = consumer.storedLeft := by
                simpa [TensorPremiseSide.premise, sideEq] using
                  consumer.premise_eq
              rcases premises with ⟨⟨leftAge, leftMarked⟩,
                rightAge, rightMarked⟩
              refine ⟨⟨leftAge, ?_⟩, ⟨rightAge, ?_⟩⟩
              · exact (congrArg (fun candidate ↦ state.core.marks[candidate]?)
                  vertexEq).trans leftMarked
              · simpa [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEq]
                  using rightMarked
          | storedRight =>
              have vertexEq : vertex = consumer.storedRight := by
                simpa [TensorPremiseSide.premise, sideEq] using
                  consumer.premise_eq
              rcases premises with ⟨⟨leftAge, leftMarked⟩,
                rightAge, rightMarked⟩
              refine ⟨⟨rightAge, ?_⟩, ⟨leftAge, ?_⟩⟩
              · exact (congrArg (fun candidate ↦ state.core.marks[candidate]?)
                  vertexEq).trans rightMarked
              · simpa [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEq]
                  using leftMarked
      | par =>
          have premises :=
            invariant.produced_premises_marked consumerMembership
          simp [ConnectiveBelow.submittedLink,
            SequentialConnectiveKind.asLink, kindEq] at premises
          have premises := premises produced
          cases sideEq : consumer.side with
          | storedLeft =>
              have vertexEq : vertex = consumer.storedLeft := by
                simpa [TensorPremiseSide.premise, sideEq] using
                  consumer.premise_eq
              rcases premises with ⟨⟨leftAge, leftMarked⟩,
                rightAge, rightMarked⟩
              refine ⟨⟨leftAge, ?_⟩, ⟨rightAge, ?_⟩⟩
              · exact (congrArg (fun candidate ↦ state.core.marks[candidate]?)
                  vertexEq).trans leftMarked
              · simpa [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEq]
                  using rightMarked
          | storedRight =>
              have vertexEq : vertex = consumer.storedRight := by
                simpa [TensorPremiseSide.premise, sideEq] using
                  consumer.premise_eq
              rcases premises with ⟨⟨leftAge, leftMarked⟩,
                rightAge, rightMarked⟩
              refine ⟨⟨rightAge, ?_⟩, ⟨leftAge, ?_⟩⟩
              · exact (congrArg (fun candidate ↦ state.core.marks[candidate]?)
                  vertexEq).trans rightMarked
              · simpa [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEq]
                  using leftMarked
  | waiting waitingAt member =>
      rcases invariant.waiting_span_exact waitingAt member with
        ⟨linkIndex, left, right, olderPremise, youngerPremise,
          olderAge, youngerAge, youngerBoundary, linkLookup, _sourceLookup,
          _unmarked, premiseOrientation, olderMarked, youngerMarked,
          _olderBoundary, _youngerBoundaryLookup, _boundaryLt⟩
      have sameLink :=
        UnificationState.StructurallyWellFormed.producerLink_unique
          invariant.structural consumerMembership consumerProduces
          (List.mem_of_getElem? linkLookup) (by simp [Link.produces])
      cases kindEq : consumer.kind <;> cases sideEq : consumer.side <;>
        simp [ConnectiveBelow.submittedLink, SequentialConnectiveKind.asLink,
          kindEq] at sameLink
      · rcases premiseOrientation with orientation | orientation
        · rcases orientation with ⟨rfl, rfl⟩
          rcases sameLink with ⟨rfl, rfl, _⟩
          have vertexEq : vertex = consumer.storedLeft := by
            simpa [TensorPremiseSide.premise, sideEq] using
              consumer.premise_eq
          refine ⟨⟨olderAge, ?_⟩, ⟨youngerAge, ?_⟩⟩
          · exact (congrArg (fun candidate ↦ state.core.marks[candidate]?)
              vertexEq).trans olderMarked
          · simpa [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEq] using
              youngerMarked
        · rcases orientation with ⟨rfl, rfl⟩
          rcases sameLink with ⟨rfl, rfl, _⟩
          have vertexEq : vertex = consumer.storedLeft := by
            simpa [TensorPremiseSide.premise, sideEq] using
              consumer.premise_eq
          refine ⟨⟨youngerAge, ?_⟩, ⟨olderAge, ?_⟩⟩
          · exact (congrArg (fun candidate ↦ state.core.marks[candidate]?)
              vertexEq).trans youngerMarked
          · simpa [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEq] using
              olderMarked
      · rcases premiseOrientation with orientation | orientation
        · rcases orientation with ⟨rfl, rfl⟩
          rcases sameLink with ⟨rfl, rfl, _⟩
          have vertexEq : vertex = consumer.storedRight := by
            simpa [TensorPremiseSide.premise, sideEq] using
              consumer.premise_eq
          refine ⟨⟨youngerAge, ?_⟩, ⟨olderAge, ?_⟩⟩
          · exact (congrArg (fun candidate ↦ state.core.marks[candidate]?)
              vertexEq).trans youngerMarked
          · simpa [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEq] using
              olderMarked
        · rcases orientation with ⟨rfl, rfl⟩
          rcases sameLink with ⟨rfl, rfl, _⟩
          have vertexEq : vertex = consumer.storedRight := by
            simpa [TensorPremiseSide.premise, sideEq] using
              consumer.premise_eq
          refine ⟨⟨olderAge, ?_⟩, ⟨youngerAge, ?_⟩⟩
          · exact (congrArg (fun candidate ↦ state.core.marks[candidate]?)
              vertexEq).trans olderMarked
          · simpa [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEq] using
              youngerMarked

end SequentialFigure7
end ProofNetIR
