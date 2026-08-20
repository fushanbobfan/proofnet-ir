/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtBranchResidual

/-!
# Active-top debt queue-tail normalization

The selected-away residual for `nop` and `wait` is exactly the presence of a
non-global vertex in the remaining ready tail. This module only normalizes the
existing branch-local boundary. It does not derive the tail witness from
canonical history, reachability, correctness, or a progress assumption.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

private theorem connectivePremiseMembershipForReadyTail
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    vertex ∈ consumer.submittedLink.premises := by
  rcases consumer with
    ⟨linkIndex, kind, storedLeft, storedRight, conclusion, side,
      consumerEq, linkEq, wellFormed, premiseEq⟩
  subst vertex
  cases kind <;> cases side <;>
    simp [ConnectiveBelow.submittedLink, SequentialConnectiveKind.asLink,
      Link.premises, TensorPremiseSide.premise]

private theorem connectivePremiseNotConclusionForReadyTail
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex)
    (structural : certificate.StructurallyWellFormed) :
    vertex ∉ certificate.conclusions := by
  have premiseMembership : vertex ∈ consumer.submittedLink.premises :=
    connectivePremiseMembershipForReadyTail consumer
  have vertexBound : vertex < certificate.formulas.size := by
    cases kindEquation : consumer.kind with
    | par =>
        have wellFormed :
            certificate.LinkWellFormed
              (.par consumer.storedLeft consumer.storedRight consumer.conclusion) := by
          simpa [SequentialConnectiveKind.asLink, kindEquation] using consumer.wellFormed
        cases sideEquation : consumer.side with
        | storedLeft =>
            have vertexEq : vertex = consumer.storedLeft := by
              simpa [TensorPremiseSide.premise, sideEquation] using consumer.premise_eq
            rw [vertexEq]
            exact wellFormed.2.2.2.1
        | storedRight =>
            have vertexEq : vertex = consumer.storedRight := by
              simpa [TensorPremiseSide.premise, sideEquation] using consumer.premise_eq
            rw [vertexEq]
            exact wellFormed.2.2.2.2.1
    | tensor =>
        have wellFormed :
            certificate.LinkWellFormed
              (.tensor consumer.storedLeft consumer.storedRight consumer.conclusion) := by
          simpa [SequentialConnectiveKind.asLink, kindEquation] using consumer.wellFormed
        cases sideEquation : consumer.side with
        | storedLeft =>
            have vertexEq : vertex = consumer.storedLeft := by
              simpa [TensorPremiseSide.premise, sideEquation] using consumer.premise_eq
            rw [vertexEq]
            exact wellFormed.2.2.2.1
        | storedRight =>
            have vertexEq : vertex = consumer.storedRight := by
              simpa [TensorPremiseSide.premise, sideEquation] using consumer.premise_eq
            rw [vertexEq]
            exact wellFormed.2.2.2.2.1
  intro boundary
  have node := structural.2.2.2.2.2 vertex vertexBound
  have parentZero : certificate.parentUseCount vertex = 0 := by
    simpa [boundary] using node.2
  have linkMembership : consumer.submittedLink ∈ certificate.links :=
    List.mem_of_getElem? consumer.link_eq
  have filtered :
      consumer.submittedLink ∈ certificate.links.filter (·.usesAsPremise vertex) := by
    apply List.mem_filter.mpr
    exact ⟨linkMembership, by simpa [Link.usesAsPremise] using premiseMembership⟩
  have positive : 0 < certificate.parentUseCount vertex := by
    unfold Certificate.parentUseCount
    exact List.length_pos_of_mem filtered
  omega

private theorem PreparedStep.selectedAway_iff_readyTailNonconclusion
    {certificate : Certificate} {before : ReservationState}
    (step : PreparedStep before)
    (invariant : SchedulerInvariant certificate before)
    (selectedNotConclusion : step.stackResult.vertex ∉ certificate.conclusions) :
    step.SelectedAwayRawNonconclusionWitness certificate ↔
      ∃ pending,
        pending ∈ step.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions := by
  let input := step.readyHeadInput
  rcases List.getLast?_eq_some_iff.mp input.top_ready with
    ⟨readyPrefix, readyEquation⟩
  rcases List.getLast?_eq_some_iff.mp input.sigma_top with
    ⟨sigmaPrefix, sigmaEquation⟩
  have prefixLengths : readyPrefix.length = sigmaPrefix.length := by
    have aligned := invariant.stack_wellShaped.ready_aligned
    rw [readyEquation, sigmaEquation] at aligned
    simp at aligned
    omega
  have sigmaLookup :
      before.stack.sigma[readyPrefix.length]? = some input.rawAge := by
    rw [sigmaEquation, prefixLengths]
    simp
  have readyLookup :
      before.stack.ready[readyPrefix.length]? =
        some (input.vertex :: input.readyTail) := by
    rw [readyEquation]
    simp
  rcases invariant.ready_bucket_frontier_exact sigmaLookup readyLookup with
    ⟨activeComponent, activeLookup, exactMembership⟩
  have selectedFrontier : input.vertex ∈ activeComponent.frontier :=
    (exactMembership input.vertex).mp (by simp) |>.1
  constructor
  · intro selectedAway
    rcases selectedAway activeLookup selectedFrontier selectedNotConclusion with
      ⟨pending, pendingFrontier, pendingNotConclusion, pendingDifferent,
        pendingUnmarked⟩
    have pendingBucket : pending ∈ input.vertex :: input.readyTail :=
      (exactMembership pending).mpr ⟨pendingFrontier, pendingUnmarked⟩
    have pendingTail : pending ∈ input.readyTail :=
      (List.mem_cons.mp pendingBucket).resolve_left pendingDifferent
    exact ⟨pending, pendingTail, pendingNotConclusion⟩
  · rintro ⟨pending, pendingTail, pendingNotConclusion⟩
    intro component componentLookup _selectedFrontier _selectedNotConclusion
    have componentEq : component = activeComponent :=
      Option.some.inj
        (Option.some.inj (componentLookup.symm.trans activeLookup))
    subst component
    have pendingFacts :=
      (exactMembership pending).mp
        (List.mem_cons_of_mem input.vertex pendingTail)
    have topMembership : input.vertex :: input.readyTail ∈ before.stack.ready :=
      List.mem_of_getElem? readyLookup
    have topNodup : (input.vertex :: input.readyTail).Nodup :=
      invariant.stack_wellShaped.ready_nodup _ topMembership
    have pendingDifferent : pending ≠ input.vertex := by
      intro same
      subst pending
      exact (List.nodup_cons.mp topNodup).1 pendingTail
    exact ⟨pending, pendingFacts.1, pendingNotConclusion,
      pendingDifferent, pendingFacts.2⟩

/-- Under prior debt, post-`nop` debt is exactly the existence of a non-global
vertex in the prepared step's remaining ready tail. -/
theorem NopStep.activeTopMarkedNonconclusionDebt_iff_readyTailNonconclusion
    {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (prior : ActiveTopMarkedNonconclusionDebt certificate before) :
    ActiveTopMarkedNonconclusionDebt certificate after ↔
      ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions := by
  exact (step.activeTopMarkedNonconclusionDebt_iff_selectedAway prior).trans
    (step.prepared.selectedAway_iff_readyTailNonconclusion invariant
      (connectivePremiseNotConclusionForReadyTail step.consumer invariant.structural))

/-- Under prior debt, post-`wait` debt is exactly the existence of a non-global
vertex in the prepared step's remaining ready tail. -/
theorem WaitStep.activeTopMarkedNonconclusionDebt_iff_readyTailNonconclusion
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (prior : ActiveTopMarkedNonconclusionDebt certificate before) :
    ActiveTopMarkedNonconclusionDebt certificate after ↔
      ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions := by
  exact (step.activeTopMarkedNonconclusionDebt_iff_selectedAway prior).trans
    (step.prepared.selectedAway_iff_readyTailNonconclusion invariant
      (connectivePremiseNotConclusionForReadyTail step.consumer invariant.structural))

end SequentialFigure7
end ProofNetIR
