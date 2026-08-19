/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveRegionEnabledness
import ProofNetIR.SequentialFigure7PriorityEnabled
import ProofNetIR.SequentialFigure7TensorAdjacency

/-!
# Figure-7 ready-head dispatch residual

Every canonical ready head satisfies an inclusive dichotomy: one
fixed-priority branch is enabled, or a marked tensor exposes an exact gap. In
the gap branch, the mate resolves to a retained sigma boundary strictly below
the active top, but no input-only witness identifies it with the active top's
immediate predecessor. The gap does not assert that the enabled branch is
absent.

The reachable wrapper turns the positive branch into an exact canonical
dispatcher step. This module does not prove that the residual is unreachable,
establish a queue-origin invariant, bridge semantic nonterminality to a ready
head, or prove unconditional dispatcher progress or totality.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

/-- Exact marked-tensor predecessor gap exposed by the ready-head reduction.

The tensor mate resolves to a strictly older retained sigma boundary, but no
input-only witness identifies that boundary with the active top's immediate
predecessor. This carrier alone does not state that every priority branch is
disabled. -/
structure ReadyHeadMarkedTensorPredecessorGap
    (certificate : Certificate) (before : ReservationState)
    (head : ReadyHeadInput before) : Type where
  consumer : ConnectiveBelow certificate head.vertex
  mateRawAge : RawTokenAge
  mateBoundary : RawTokenAge
  tensor_kind : consumer.kind = .tensor
  mate_marked :
    before.core.marks[consumer.mate]? = some (some mateRawAge)
  mate_boundary :
    sigmaBoundary? before.stack.sigma mateRawAge = some mateBoundary
  mate_boundary_lt_active : mateBoundary < head.rawAge
  no_predecessor :
    ¬ ∃ previousBoundary : RawTokenAge,
      Nonempty
        (SigmaPredecessorInput before.stack.sigma head.rawAge mateRawAge
          previousBoundary)

private theorem mem_liveFrontierVertices_of_raw
    {state : UnificationState} {token : Nat}
    {component : UnificationComponent} {vertex : Vertex}
    (componentLookup :
      state.components[token]? = some (some component))
    (vertexMembership : vertex ∈ component.frontier) :
    vertex ∈ state.liveFrontierVertices := by
  unfold UnificationState.liveFrontierVertices
  apply List.mem_flatMap.mpr
  refine ⟨some component, ?_, ?_⟩
  · exact List.mem_of_getElem? (by simpa using componentLookup)
  · simpa using vertexMembership

private theorem markedTensor_representative_ne_active
    {certificate : Certificate} {before : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (head : ReadyHeadInput before)
    (consumer : ConnectiveBelow certificate head.vertex)
    (tensorKind : consumer.kind = .tensor)
    {mateRawAge : RawTokenAge}
    (mateMarked :
      before.core.marks[consumer.mate]? = some (some mateRawAge)) :
    before.core.representative mateRawAge ≠
      before.core.representative head.rawAge := by
  let tensor : TensorBelow := {
    linkIndex := consumer.linkIndex
    storedLeft := consumer.storedLeft
    storedRight := consumer.storedRight
    conclusion := consumer.conclusion
    side := consumer.side }
  have tensorValid :
      tensor.Valid certificate certificate.consumerIndex head.vertex := by
    refine ⟨consumer.consumer_eq, ?_, ?_, ?_⟩
    · simpa [tensor, SequentialConnectiveKind.asLink, tensorKind] using
        consumer.link_eq
    · simpa [tensor, SequentialConnectiveKind.asLink, tensorKind] using
        consumer.wellFormed
    · simpa [tensor, TensorBelow.premise] using consumer.premise_eq
  have tensorMateMarked :
      before.core.marks[tensor.mate]? = some (some mateRawAge) := by
    simpa [tensor, TensorBelow.mate, ConnectiveBelow.mate] using mateMarked
  have tensorMembership :
      Link.tensor tensor.storedLeft tensor.storedRight tensor.conclusion ∈
        certificate.links :=
    List.mem_of_getElem? tensorValid.2.1
  have headReady : head.vertex ∈ before.stack.ready.flatten := by
    apply List.mem_flatten.mpr
    exact ⟨head.vertex :: head.readyTail,
      List.mem_of_getLast? head.top_ready, by simp⟩
  have headQueued : head.vertex ∈ before.stack.queuedVertices := by
    unfold SequentialStackState.queuedVertices
    exact List.mem_append_left _ headReady
  have headUnmarked : before.core.marks[head.vertex]? = some none :=
    invariant.queued_vertices_unmarked head.vertex headQueued
  have conclusionNotProduced : ¬ Produced before tensor.conclusion := by
    intro produced
    have premises :=
      invariant.produced_premises_marked tensorMembership produced
    cases sideEquation : tensor.side with
    | storedLeft =>
        rcases premises.1 with ⟨_headAge, headMarked⟩
        have headIsLeft : head.vertex = tensor.storedLeft := by
          simpa [TensorBelow.premise, TensorPremiseSide.premise,
            sideEquation] using tensorValid.2.2.2
        rw [← headIsLeft, headUnmarked] at headMarked
        simp at headMarked
    | storedRight =>
        rcases premises.2 with ⟨_headAge, headMarked⟩
        have headIsRight : head.vertex = tensor.storedRight := by
          simpa [TensorBelow.premise, TensorPremiseSide.premise,
            sideEquation] using tensorValid.2.2.2
        rw [← headIsRight, headUnmarked] at headMarked
        simp at headMarked
  rcases head.activeComponent invariant with
    ⟨activeComponent, _activeUsed, activeOwned, activeLookup,
      activeWitness, activeAccounted, headOwned, activeRoot⟩
  rcases SchedulerInvariant.exactMarkedOccurrenceOwner invariant
      tensorMateMarked with
    ⟨ownerRawAge, ownerIndex, ownerComponent, _ownerUsed, ownerOwned,
      ownerMarked, ownerRepresentative, ownerLookup, ownerWitness,
      _ownerAccounted, mateOwned⟩
  have ownerRawAgeEq : ownerRawAge = mateRawAge := by
    exact Option.some.inj
      (Option.some.inj (ownerMarked.symm.trans tensorMateMarked))
  subst ownerRawAge
  intro sameRepresentative
  have ownerIndexEq : ownerIndex = head.rawAge := by
    calc
      ownerIndex = before.core.representative mateRawAge :=
        ownerRepresentative.symm
      _ = before.core.representative head.rawAge := sameRepresentative
      _ = head.rawAge := activeRoot
  have ownerLookupAtActive :
      before.core.components[head.rawAge]? = some (some ownerComponent) := by
    simpa [ownerIndexEq] using ownerLookup
  have componentEq : ownerComponent = activeComponent := by
    exact Option.some.inj
      (Option.some.inj (ownerLookupAtActive.symm.trans activeLookup))
  subst ownerComponent
  have ownedEq : ownerOwned = activeOwned :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      ownerWitness.derivation activeWitness.derivation
  have mateActiveOwned : tensor.mate ∈ activeOwned := by
    rw [← ownedEq]
    exact mateOwned
  rcases activeWitness.referencePath_within_owned mateActiveOwned headOwned with
    ⟨componentPath, componentStarts, componentFinishes,
      componentPathOwned⟩
  have conclusionNotOwned : tensor.conclusion ∉ activeOwned := by
    intro conclusionOwned
    apply conclusionNotProduced
    rcases activeAccounted tensor.conclusion conclusionOwned with
      ⟨rawAge, marked, _representative⟩ | ⟨_unmarked, frontier⟩
    · exact Or.inl ⟨rawAge, marked⟩
    · exact Or.inr
        (mem_liveFrontierVertices_of_raw activeLookup frontier)
  have componentAvoids :
      tensor.conclusion ∉ componentPath.vertices := by
    intro conclusionMembership
    exact conclusionNotOwned
      (componentPathOwned tensor.conclusion conclusionMembership)
  have combinedStarts : componentPath.start = tensor.mate :=
    componentStarts
  have combinedFinishes : componentPath.finish = head.vertex :=
    componentFinishes
  cases sideEquation : tensor.side with
  | storedLeft =>
      have headIsLeft : head.vertex = tensor.storedLeft := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using tensorValid.2.2.2
      have mateIsRight : tensor.mate = tensor.storedRight := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      apply referenceAcyclic_no_tensorBypass invariant.structural
        correct.referenceSwitchingTree.acyclic tensorMembership
          componentPath.reverse
      · exact combinedFinishes.trans headIsLeft
      · exact combinedStarts.trans mateIsRight
      · simpa using componentAvoids
  | storedRight =>
      have headIsRight : head.vertex = tensor.storedRight := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using tensorValid.2.2.2
      have mateIsLeft : tensor.mate = tensor.storedLeft := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      apply referenceAcyclic_no_tensorBypass invariant.structural
        correct.referenceSwitchingTree.acyclic tensorMembership componentPath
      · exact combinedStarts.trans mateIsLeft
      · exact combinedFinishes.trans headIsRight
      · exact componentAvoids

private theorem markedTensor_strictOlderSigmaBoundary
    {certificate : Certificate} {before : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (head : ReadyHeadInput before)
    (consumer : ConnectiveBelow certificate head.vertex)
    (tensorKind : consumer.kind = .tensor)
    {mateRawAge : RawTokenAge}
    (mateMarked :
      before.core.marks[consumer.mate]? = some (some mateRawAge)) :
    ∃ mateBoundary : RawTokenAge,
      sigmaBoundary? before.stack.sigma mateRawAge = some mateBoundary ∧
        mateBoundary < head.rawAge := by
  have stackMarked :
      before.stack.marks[consumer.mate]? = some (some mateRawAge) := by
    rw [← invariant.realizesSigma.marks_eq]
    exact mateMarked
  have mateAgeBound : mateRawAge < before.stack.nextAge :=
    invariant.stack_wellShaped.assigned_age_bound
      consumer.mate mateRawAge stackMarked
  rcases invariant.stack_wellShaped.sigma_partition.boundary_exists
      mateAgeBound with
    ⟨mateBoundary, mateBoundaryLookup⟩
  have mateRepresentative :
      before.core.representative mateRawAge = mateBoundary := by
    have realized :=
      invariant.realizesSigma.representative_eq_boundary mateAgeBound
    exact Option.some.inj (realized.symm.trans mateBoundaryLookup)
  have activeMembership : head.rawAge ∈ before.stack.sigma :=
    List.mem_of_getLast? head.sigma_top
  have activeAgeBound : head.rawAge < before.stack.nextAge :=
    invariant.stack_wellShaped.sigma_partition.boundary_lt
      head.rawAge activeMembership
  have activeBoundaryLookup :
      sigmaBoundary? before.stack.sigma head.rawAge = some head.rawAge :=
    invariant.stack_wellShaped.sigma_partition.sigmaBoundary?_eq_top
      head.sigma_top
  have activeRepresentative :
      before.core.representative head.rawAge = head.rawAge := by
    have realized :=
      invariant.realizesSigma.representative_eq_boundary activeAgeBound
    exact Option.some.inj (realized.symm.trans activeBoundaryLookup)
  have mateRepresentativeNe :=
    markedTensor_representative_ne_active correct invariant head consumer
      tensorKind mateMarked
  have mateBoundaryLeActive : mateBoundary ≤ head.rawAge := by
    apply Nat.le_of_not_gt
    intro activeLtMateBoundary
    have activeLeMateRawAge : head.rawAge ≤ mateRawAge :=
      Nat.le_trans (Nat.le_of_lt activeLtMateBoundary)
        (sigmaBoundary?_le mateBoundaryLookup)
    have activeLookup :
        sigmaBoundary? before.stack.sigma mateRawAge = some head.rawAge :=
      invariant.stack_wellShaped.sigma_partition.sigmaBoundary?_eq_top_of_le
        head.sigma_top activeLeMateRawAge mateAgeBound
    have boundaryEq : mateBoundary = head.rawAge :=
      Option.some.inj (mateBoundaryLookup.symm.trans activeLookup)
    apply mateRepresentativeNe
    rw [mateRepresentative, activeRepresentative, boundaryEq]
  have mateBoundaryNeActive : mateBoundary ≠ head.rawAge := by
    intro same
    apply mateRepresentativeNe
    rw [mateRepresentative, activeRepresentative, same]
  exact ⟨mateBoundary, mateBoundaryLookup,
    Nat.lt_of_le_of_ne mateBoundaryLeActive mateBoundaryNeActive⟩

private theorem exists_priorityEnabled_of_enabled_case
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (enabled :
      ConclEnabled certificate before ∨
        NopEnabled certificate before ∨
        NewEnabled certificate before ∨
        WaitEnabled certificate before ∨
        ForwardEnabled certificate before ∨
        UnifyPayloadEnabled certificate before) :
    ∃ kind, PriorityEnabled certificate before invariant kind := by
  classical
  by_cases concl : ConclEnabled certificate before
  · exact ⟨.concl, .concl concl⟩
  by_cases nop : NopEnabled certificate before
  · exact ⟨.nop, .nop concl nop⟩
  by_cases new : NewEnabled certificate before
  · exact ⟨.new, .new concl nop new⟩
  by_cases wait : WaitEnabled certificate before
  · exact ⟨.wait, .wait concl nop new wait⟩
  by_cases forward : ForwardEnabled certificate before
  · exact ⟨.forward, .forward concl nop new wait forward⟩
  rcases enabled with conclEnabled | nopEnabled | newEnabled |
      waitEnabled | forwardEnabled | unifyPayloadEnabled
  · exact (concl conclEnabled).elim
  · exact (nop nopEnabled).elim
  · exact (new newEnabled).elim
  · exact (wait waitEnabled).elim
  · exact (forward forwardEnabled).elim
  · exact ⟨.unifyPayload,
      .unifyPayload concl nop new wait forward unifyPayloadEnabled⟩

namespace CanonicalTagHistory

/-- Every canonical ready head has a priority-enabled branch or exposes an
exact strictly older, non-immediate marked-tensor sigma boundary. The
disjunction is inclusive. -/
theorem readyHead_priorityEnabled_or_markedTensorPredecessorGap
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (head : ReadyHeadInput before) :
    (∃ kind, PriorityEnabled certificate before invariant kind) ∨
      Nonempty
        (ReadyHeadMarkedTensorPredecessorGap certificate before head) := by
  rcases readyHead_enabled_or_tensor_mark_cases invariant head with
    concl | nop | wait | forward | unmarkedTensor | markedTensor
  · apply Or.inl
    apply exists_priorityEnabled_of_enabled_case invariant
    exact Or.inl concl
  · apply Or.inl
    apply exists_priorityEnabled_of_enabled_case invariant
    exact Or.inr (Or.inl nop)
  · apply Or.inl
    apply exists_priorityEnabled_of_enabled_case invariant
    exact Or.inr (Or.inr (Or.inr (Or.inl wait)))
  · apply Or.inl
    apply exists_priorityEnabled_of_enabled_case invariant
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl forward))))
  · rcases unmarkedTensor with ⟨consumer, tensorKind, mateUnmarked⟩
    let tensor : TensorBelow := {
      linkIndex := consumer.linkIndex
      storedLeft := consumer.storedLeft
      storedRight := consumer.storedRight
      conclusion := consumer.conclusion
      side := consumer.side }
    have tensorValid :
        tensor.Valid certificate certificate.consumerIndex head.vertex := by
      refine ⟨consumer.consumer_eq, ?_, ?_, ?_⟩
      · simpa [tensor, SequentialConnectiveKind.asLink, tensorKind] using
          consumer.link_eq
      · simpa [tensor, SequentialConnectiveKind.asLink, tensorKind] using
          consumer.wellFormed
      · simpa [tensor, TensorBelow.premise] using consumer.premise_eq
    let guard : NewGuard certificate before := {
      head := head
      tensor := tensor
      tensor_valid := tensorValid
      mate_unmarked := by
        simpa [tensor, TensorBelow.mate, ConnectiveBelow.mate] using
          mateUnmarked }
    have newEnabled : NewEnabled certificate before :=
      tagHistory.active_newEnabled correct invariant guard
    apply Or.inl
    apply exists_priorityEnabled_of_enabled_case invariant
    exact Or.inr (Or.inr (Or.inl newEnabled))
  · rcases markedTensor with
      ⟨consumer, mateRawAge, tensorKind, mateMarked⟩
    by_cases adjacency :
        ∃ previousBoundary : RawTokenAge,
          Nonempty
            (SigmaPredecessorInput before.stack.sigma head.rawAge
              mateRawAge previousBoundary)
    · rcases adjacency with ⟨previousBoundary, ⟨adjacency⟩⟩
      have unifyEnabled : UnifyPayloadEnabled certificate before :=
        markedTensor_unifyPayloadEnabled invariant head consumer tensorKind
          mateMarked adjacency
      apply Or.inl
      apply exists_priorityEnabled_of_enabled_case invariant
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr unifyEnabled))))
    · rcases markedTensor_strictOlderSigmaBoundary correct invariant head
          consumer tensorKind mateMarked with
        ⟨mateBoundary, mateBoundaryLookup, mateBoundaryLt⟩
      exact Or.inr ⟨{
        consumer := consumer
        mateRawAge := mateRawAge
        mateBoundary := mateBoundary
        tensor_kind := tensorKind
        mate_marked := mateMarked
        mate_boundary := mateBoundaryLookup
        mate_boundary_lt_active := mateBoundaryLt
        no_predecessor := adjacency }⟩

end CanonicalTagHistory

namespace ReachableByImplementedDispatcher

/-- A dispatcher-reachable ready head makes the canonical executable
dispatcher succeed or exposes the exact strictly older, non-immediate
marked-tensor gap. The disjunction is inclusive. -/
theorem readyHead_dispatch_or_markedTensorPredecessorGap
    {certificate : Certificate} {before : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate before)
    (correct : certificate.DeclarativelyCorrect)
    (head : ReadyHeadInput before) :
    let invariant := reachable.schedulerInvariant correct.1
    (∃ result : Figure7DispatchResult,
      dispatch? certificate before invariant = some result) ∨
        Nonempty
          (ReadyHeadMarkedTensorPredecessorGap certificate before head) := by
  let invariant := reachable.schedulerInvariant correct.1
  change
    (∃ result : Figure7DispatchResult,
      dispatch? certificate before invariant = some result) ∨
        Nonempty
          (ReadyHeadMarkedTensorPredecessorGap certificate before head)
  rcases reachable with ⟨history⟩
  rcases history.hasCanonicalTagHistory with ⟨tagHistory⟩
  rcases
      tagHistory.readyHead_priorityEnabled_or_markedTensorPredecessorGap
        correct invariant head with enabled | gap
  · rcases enabled with ⟨kind, enabled⟩
    rcases enabled.exists_dispatchStep with ⟨after, step⟩
    exact Or.inl ⟨⟨kind, after⟩, (dispatch?_some_iff invariant).mpr step⟩
  · exact Or.inr gap

end ReachableByImplementedDispatcher

end SequentialFigure7
end ProofNetIR
