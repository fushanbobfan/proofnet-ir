/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParGuardOutcome
import ProofNetIR.SequentialFigure7ActiveTopDebtParentExternalReentryTarget

/-!
# Figure-7 commitment-interval par-guard re-entry

Connects the strictly older external mate in the typed Nop and Wait interval
outcomes back into the active occurrence carrier through a supplied connected
reference switching and classifies the exact active-frontier re-entry target.
The raw or marked guard status is retained.

Equal-final selected/mate traces and the inclusive outer split remain. This
module does not eliminate the selected or marked re-entry targets, derive the
history-tail law, or prove progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState

namespace CanonicalTagHistory

private theorem CommitmentIntervalParTraceOutcome.mapOlderMateStatus
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state}
    {consumer : ConnectiveBelow certificate input.vertex}
    {position edgeCount : Nat} {first : RawTokenAge}
    {beforeStatus afterStatus : Prop}
    (outcome : tagHistory.CommitmentIntervalParTraceOutcome input consumer
      position edgeCount first beforeStatus)
    (mapStatus : beforeStatus → afterStatus) :
    tagHistory.CommitmentIntervalParTraceOutcome input consumer position
      edgeCount first afterStatus := by
  cases outcome with
  | avoiding path =>
      exact .avoiding path
  | equalSelected offset parent child event offsetLt parentAt childAt
      notAvoiding eventMem eventAge childEq side beforeTrace afterTrace trace =>
      exact .equalSelected offset parent child event offsetLt parentAt childAt
        notAvoiding eventMem eventAge childEq side beforeTrace afterTrace trace
  | equalMate offset parent child event offsetLt parentAt childAt notAvoiding
      eventMem eventAge childEq side beforeTrace afterTrace trace =>
      exact .equalMate offset parent child event offsetLt parentAt childAt
        notAvoiding eventMem eventAge childEq side beforeTrace afterTrace trace
  | olderMate offset parent child event offsetLt parentAt childAt notAvoiding
      eventMem eventAge childLt side beforeTrace afterTrace trace status =>
      exact .olderMate offset parent child event offsetLt parentAt childAt
        notAvoiding eventMem eventAge childLt side beforeTrace afterTrace trace
        (mapStatus status)

end CanonicalTagHistory

private theorem ReadyHeadInput.selected_owned_accounted
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned) :
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

private theorem ReadyHeadInput.externalEndpointReentry
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (connected : certificate.ReferenceSwitchingConnected)
    (invariant : SchedulerInvariant certificate state)
    {owned : List Vertex} (selectedOwned : input.vertex ∈ owned)
    {endpoint : Vertex} {mark : Option RawTokenAge}
    (endpointMarked : state.core.marks[endpoint]? = some mark)
    (endpointOutside : endpoint ∉ owned) :
    ActiveCarrierExternalEndpointReentry certificate owned endpoint := by
  have coreMarksSize :
      state.core.marks.size = certificate.formulas.size := by
    rw [invariant.realizesSigma.marks_eq]
    exact invariant.stack_wellShaped.marks_size
  have selectedMarked : state.core.marks[input.vertex]? = some none :=
    invariant.queued_vertices_unmarked input.vertex
      (input.futureWorkAt invariant).mem_queued
  have selectedBound : input.vertex < certificate.formulas.size := by
    rcases Array.getElem?_eq_some_iff.mp selectedMarked with
      ⟨markBound, _markValue⟩
    simpa [coreMarksSize] using markBound
  have endpointBound : endpoint < certificate.formulas.size := by
    rcases Array.getElem?_eq_some_iff.mp endpointMarked with
      ⟨markBound, _markValue⟩
    simpa [coreMarksSize] using markBound
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
  have endpointToSelected := zeroToEndpoint.symm.trans zeroToSelected
  rcases endpointToSelected.toSimple with ⟨_steps, _visited, simple⟩
  rcases simple.liftToEdgeSimplePathWithEdges
      (fun _ membership ↦ membership) with
    ⟨path, pathStarts, pathFinishes, _pathVertices, _pathEdges⟩
  have pathStartOutside : path.start ∉ owned := by
    simpa [pathStarts] using endpointOutside
  have pathFinishOwned : path.finish ∈ owned := by
    simpa [pathFinishes] using selectedOwned
  have finishMembership : path.finish ∈ path.vertices := by
    simpa [Graph.EdgeSimplePath.vertices] using
      path.walk.finish_mem_visitedVertices
  have finishInside : (!(owned.contains path.finish)) = false := by
    simp [pathFinishOwned]
  rcases path.exists_traversed_boundary_of_start_true
      (fun vertex ↦ !(owned.contains vertex))
      (by simpa using pathStartOutside)
      ⟨path.finish, finishMembership, finishInside⟩ with
    ⟨directed, directedMembership, sourceOutside, targetInside⟩
  exact ⟨path, directed, pathStarts, pathFinishOwned, directedMembership,
    by simpa using sourceOutside, by simpa using targetInside⟩

/-- For Nop, the older raw external mate additionally carries an exact
reference-switching re-entry into the active occurrence carrier. -/
theorem NopStep.commitmentInterval_parTraceReentryTargetOutcome
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (connected : certificate.ReferenceSwitchingConnected)
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (step : NopStep certificate before after)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      before.core.components[step.prepared.stackResult.rawAge]? =
        some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {position edgeCount : Nat} {first : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : before.stack.sigma[position]? = some first)
    (lastAt :
      before.stack.sigma[position + edgeCount]? =
        some step.prepared.stackResult.rawAge) :
    tagHistory.CommitmentIntervalParTraceOutcome
      step.prepared.readyHeadInput step.consumer position edgeCount first
        (step.consumer.mate ∉ owned ∧
          before.core.marks[step.consumer.mate]? = some none ∧
          ActiveCarrierExternalReentryTargetStatus certificate before
            step.prepared.readyHeadInput component owned step.consumer.mate) := by
  rcases step.prepared.readyHeadInput.selected_owned_accounted invariant
      componentLookup occurrence with ⟨selectedOwned, accounted⟩
  apply (step.commitmentInterval_parTraceOutcome tagHistory invariant
    componentLookup occurrence positive firstAt lastAt).mapOlderMateStatus
  rintro ⟨mateOutside, mateUnmarked⟩
  have reentry :=
    step.prepared.readyHeadInput.externalEndpointReentry connected invariant
      selectedOwned mateUnmarked mateOutside
  exact ⟨mateOutside, mateUnmarked,
    reentry.targetStatus step.prepared.readyHeadInput invariant componentLookup
      occurrence accounted⟩

/-- For Wait, the older marked external mate additionally carries an exact
reference-switching re-entry into the active occurrence carrier. -/
theorem WaitStep.commitmentInterval_parTraceReentryTargetOutcome
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (connected : certificate.ReferenceSwitchingConnected)
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (step : WaitStep certificate before after)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      before.core.components[step.prepared.stackResult.rawAge]? =
        some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {position edgeCount : Nat} {first : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : before.stack.sigma[position]? = some first)
    (lastAt :
      before.stack.sigma[position + edgeCount]? =
        some step.prepared.stackResult.rawAge) :
    tagHistory.CommitmentIntervalParTraceOutcome
      step.prepared.readyHeadInput step.consumer position edgeCount first
        (step.consumer.mate ∉ owned ∧
          before.core.marks[step.consumer.mate]? =
            some (some step.mateRawAge) ∧
          before.core.representative step.mateRawAge <
            step.prepared.stackResult.rawAge ∧
          ActiveCarrierExternalReentryTargetStatus certificate before
            step.prepared.readyHeadInput component owned step.consumer.mate) := by
  rcases step.prepared.readyHeadInput.selected_owned_accounted invariant
      componentLookup occurrence with ⟨selectedOwned, accounted⟩
  apply (step.commitmentInterval_parTraceOutcome tagHistory invariant
    componentLookup occurrence positive firstAt lastAt).mapOlderMateStatus
  rintro ⟨mateOutside, mateMarked, representativeOlder⟩
  have reentry :=
    step.prepared.readyHeadInput.externalEndpointReentry connected invariant
      selectedOwned mateMarked mateOutside
  exact ⟨mateOutside, mateMarked, representativeOlder,
    reentry.targetStatus step.prepared.readyHeadInput invariant componentLookup
      occurrence accounted⟩

end SequentialFigure7
end ProofNetIR
