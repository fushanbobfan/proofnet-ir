/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ContinuationExit

/-!
# Wait-output obstruction to unconditional endpoint locality

A successful `wait` refutes the exact unguarded predicate
`ActiveTopContinuationExitLocalized` at its output. Consequently, that predicate cannot be an
unconditional invariant of a full dispatcher history that contains a successful `wait`.

This result does not refute a different locality statement scoped to drained states, the direct
`ActiveTopMarkedNonconclusionDebt` route, or the existing conditional `allMarked` theorem. In
particular, implications which assume `ActiveTopContinuationExitLocalized` remain valid; this
module only shows that successful `wait` outputs cannot supply that assumption.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

private theorem connectiveBelow_conclusion_eq
    {certificate : Certificate} {vertex : Vertex}
    (left right : ConnectiveBelow certificate vertex) :
    left.conclusion = right.conclusion := by
  have sameIndex : left.linkIndex = right.linkIndex :=
    Option.some.inj (left.consumer_eq.symm.trans right.consumer_eq)
  have leftLookup := left.link_eq
  rw [sameIndex] at leftLookup
  have sameLink :
      left.kind.asLink left.storedLeft left.storedRight left.conclusion =
        right.kind.asLink right.storedLeft right.storedRight right.conclusion :=
    Option.some.inj (leftLookup.symm.trans right.link_eq)
  cases leftKind : left.kind <;> cases rightKind : right.kind <;>
    simp [SequentialConnectiveKind.asLink, leftKind, rightKind] at sameLink
  · exact sameLink.2.2
  · exact sameLink.2.2

private theorem connectiveBelow_mate_eq
    {certificate : Certificate} {vertex : Vertex}
    (left right : ConnectiveBelow certificate vertex) :
    left.mate = right.mate := by
  have sameIndex : left.linkIndex = right.linkIndex :=
    Option.some.inj (left.consumer_eq.symm.trans right.consumer_eq)
  have leftLookup := left.link_eq
  rw [sameIndex] at leftLookup
  have sameLink :
      left.kind.asLink left.storedLeft left.storedRight left.conclusion =
        right.kind.asLink right.storedLeft right.storedRight right.conclusion :=
    Option.some.inj (leftLookup.symm.trans right.link_eq)
  have leftPremise := left.premise_eq
  have rightPremise := right.premise_eq
  have leftDifferent := left.mate_ne
  cases leftKind : left.kind <;> cases rightKind : right.kind <;>
    cases leftSide : left.side <;> cases rightSide : right.side <;>
      simp_all [SequentialConnectiveKind.asLink, ConnectiveBelow.mate,
        TensorPremiseSide.mate, TensorPremiseSide.premise]

private theorem connectivePremiseMembership
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

private theorem connectivePremiseNotConclusion
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex)
    (structural : certificate.StructurallyWellFormed) :
    vertex ∉ certificate.conclusions := by
  have premiseMembership : vertex ∈ consumer.submittedLink.premises :=
    connectivePremiseMembership consumer
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

private theorem MarkedConclusionChain.terminal_eq_of_conclusion_unmarked
    {certificate : Certificate} {state : ReservationState}
    {origin terminal : Vertex}
    (chain : MarkedConclusionChain certificate state origin terminal)
    (consumer : ConnectiveBelow certificate origin)
    (unmarked : state.core.marks[consumer.conclusion]? = some none) :
    terminal = origin := by
  cases chain with
  | refl => rfl
  | step first marked _notConclusion _tail =>
      have sameConclusion : first.conclusion = consumer.conclusion :=
        connectiveBelow_conclusion_eq first consumer
      rw [sameConclusion, unmarked] at marked
      simp at marked

private theorem frontier_unmarked_mem_ready
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {index : Nat} {component : UnificationComponent} {vertex : Vertex}
    (componentLookup : state.core.components[index]? = some (some component))
    (frontier : vertex ∈ component.frontier)
    (unmarked : state.core.marks[vertex]? = some none) :
    vertex ∈ state.stack.ready.flatten := by
  have boundaryMembership : index ∈ state.stack.sigma :=
    (invariant.component_domain_exact index).mp ⟨component, componentLookup⟩
  rcases List.mem_iff_getElem.mp boundaryMembership with
    ⟨position, positionBound, positionEquation⟩
  have sigmaLookup : state.stack.sigma[position]? = some index := by
    rw [List.getElem?_eq_getElem positionBound, positionEquation]
  have readyPositionBound : position < state.stack.ready.length := by
    rw [invariant.stack_wellShaped.ready_aligned]
    exact positionBound
  let bucket := state.stack.ready[position]
  have readyLookup : state.stack.ready[position]? = some bucket :=
    List.getElem?_eq_getElem readyPositionBound
  rcases invariant.ready_bucket_frontier_exact sigmaLookup readyLookup with
    ⟨actualComponent, actualLookup, exactMembership⟩
  have componentEquation : actualComponent = component :=
    Option.some.inj (Option.some.inj (actualLookup.symm.trans componentLookup))
  subst actualComponent
  apply List.mem_flatten.mpr
  exact ⟨bucket, List.mem_of_getElem? readyLookup,
    (exactMembership vertex).mpr ⟨frontier, unmarked⟩⟩

private theorem WaitStep.createdConclusion_mem_waitingVertices
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after) :
    step.consumer.conclusion ∈ after.stack.waitingVertices := by
  rcases step.destination.exact with
    ⟨payload, _old, updated, _marks, _nextAge, _sigma, _ready, _core, _tags⟩
  unfold SequentialStackState.waitingVertices
  apply List.mem_flatMap.mpr
  refine ⟨.initialized (step.consumer.conclusion :: payload), ?_, ?_⟩
  · exact List.mem_of_getElem? (by simpa using updated)
  · simp [WaitingCell.vertices]

private theorem WaitStep.selected_active_frontier_after
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ∃ component,
      after.stack.sigma.getLast? = some step.prepared.stackResult.rawAge ∧
        after.core.components[step.prepared.stackResult.rawAge]? = some (some component) ∧
          step.prepared.stackResult.vertex ∈ component.frontier ∧
            after.core.marks[step.prepared.stackResult.vertex]? =
              some (some step.prepared.stackResult.rawAge) := by
  let input := step.prepared.readyHeadInput
  rcases input.activeComponent invariant with
    ⟨component, _usedLinks, owned, componentLookup, _witness,
      accounted, selectedOwned, _activeRoot⟩
  rcases UnificationState.markReadyRaw?_exact step.prepared.core_mark_eq with
    ⟨selectedUnmarked, _marksEq, _parentsEq, componentsEq, _started,
      _fired, selectedMarked⟩
  have selectedFrontier : step.prepared.stackResult.vertex ∈ component.frontier := by
    rcases accounted step.prepared.stackResult.vertex selectedOwned with
      ⟨markedAge, marked, _representative⟩ | ⟨_unmarked, frontier⟩
    · rw [selectedUnmarked] at marked
      simp at marked
    · exact frontier
  rcases SequentialStackState.popReadyMark?_exact step.prepared.stack_eq with
    ⟨_ready, beforeSigmaTop, _unmarked, _stackMarks, _nextAge,
      preparedSigmaEq, _preparedReady, _waiting, _stackMarked⟩
  rcases step.destination.exact with
    ⟨_payload, _old, _updated, _marks, _nextAge, afterSigmaEq,
      _ready, afterCoreEq, _tags⟩
  refine ⟨component, ?_, ?_, selectedFrontier, ?_⟩
  · rw [afterSigmaEq]
    change step.prepared.stackResult.after.sigma.getLast? = _
    rw [preparedSigmaEq]
    exact beforeSigmaTop
  · rw [afterCoreEq]
    change step.prepared.coreMarked.components[step.prepared.stackResult.rawAge]? =
      some (some component)
    rw [componentsEq]
    exact componentLookup
  · rw [afterCoreEq]
    exact selectedMarked

private theorem WaitStep.mate_marked_after
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after) :
    after.core.marks[step.consumer.mate]? = some (some step.mateRawAge) := by
  rcases step.destination.exact with
    ⟨_payload, _old, _updated, _marks, _nextAge, _sigma, _ready, coreEq, _tags⟩
  rw [coreEq]
  exact step.mate_marked

/-- A successful `wait` from a complete scheduler-invariant state refutes the exact
same-component endpoint-locality predicate at its output. -/
theorem WaitStep.not_activeTopContinuationExitLocalized
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ¬ ActiveTopContinuationExitLocalized certificate after := by
  intro localized
  have afterInvariant : SchedulerInvariant certificate after :=
    step.schedulerInvariant invariant
  rcases step.selected_active_frontier_after invariant with
    ⟨component, activeTop, componentLookup, selectedFrontier, selectedMarked⟩
  have selectedNotConclusion :
      step.prepared.stackResult.vertex ∉ certificate.conclusions :=
    connectivePremiseNotConclusion step.consumer invariant.structural
  have selectedLocalized :=
    localized activeTop componentLookup selectedFrontier selectedMarked selectedNotConclusion
  have conclusionWork :
      FutureWorkAt after step.destination.boundary step.consumer.conclusion :=
    step.createdConclusionFutureWorkAt
  have conclusionUnmarked :
      after.core.marks[step.consumer.conclusion]? = some none :=
    afterInvariant.queued_vertices_unmarked step.consumer.conclusion conclusionWork.mem_queued
  cases selectedLocalized with
  | @rawMate terminal chain terminalConsumer _mateFrontier mateUnmarked =>
      have terminalEq :=
        chain.terminal_eq_of_conclusion_unmarked step.consumer conclusionUnmarked
      subst terminal
      have mateEq : terminalConsumer.mate = step.consumer.mate :=
        connectiveBelow_mate_eq terminalConsumer step.consumer
      have mateMarked := step.mate_marked_after
      rw [mateEq, mateMarked] at mateUnmarked
      simp at mateUnmarked
  | @futureConclusion terminal chain terminalConsumer _boundary _work
      conclusionFrontier _conclusionNotGlobal =>
      have terminalEq :=
        chain.terminal_eq_of_conclusion_unmarked step.consumer conclusionUnmarked
      subst terminal
      have conclusionEq : terminalConsumer.conclusion = step.consumer.conclusion :=
        connectiveBelow_conclusion_eq terminalConsumer step.consumer
      rw [conclusionEq] at conclusionFrontier
      have readyMembership : step.consumer.conclusion ∈ after.stack.ready.flatten :=
        frontier_unmarked_mem_ready afterInvariant componentLookup
          conclusionFrontier conclusionUnmarked
      have waitingMembership : step.consumer.conclusion ∈ after.stack.waitingVertices :=
        step.createdConclusion_mem_waitingVertices
      have separated :=
        (List.nodup_append.mp afterInvariant.queued_vertices_nodup).2.2
      exact separated step.consumer.conclusion readyMembership
        step.consumer.conclusion waitingMembership rfl

end SequentialFigure7
end ProofNetIR
