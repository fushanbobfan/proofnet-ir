/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtParentExternalReentryTarget
import ProofNetIR.SequentialFigure7WaitingReentryContinuationProducerOrientation

/-!
# Figure-7 waiting continuation mate avoidance

Turns the exact older-mate producer orientation into a conclusion-avoiding
mate-to-target path and an aligned external re-entry witness.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

private theorem FutureWorkAtExactWaitingLocation.consumerKind_eq_par
    {certificate : Certificate} {state : ReservationState}
    {boundary : RawTokenAge} {target : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (consumer : ConnectiveBelow certificate target)
    (location :
      FutureWorkAtExactWaitingLocation certificate state boundary
        consumer.conclusion) :
    consumer.kind = .par := by
  rcases location with
    ⟨_payload, _linkIndex, _left, _right, _olderPremise, _youngerPremise,
      _olderAge, _youngerAge, _youngerBoundary, _waitingAt, _member,
      linkLookup, _sourceLookup, _unmarked, _premiseOrientation,
      _olderMarked, _youngerMarked, _olderBoundary, _youngerBoundaryLookup,
      _boundaryLt⟩
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
  cases kindEq : consumer.kind with
  | tensor =>
      simp [ConnectiveBelow.submittedLink, SequentialConnectiveKind.asLink,
        kindEq] at sameLink
  | par => rfl

/-- The opposite premise of a consumer of an exact waiting conclusion has an
exact reference-switching path to the consumed premise which avoids that
conclusion. No active-boundary or raw-mark orientation is needed. -/
theorem FutureWorkAtExactWaitingLocation.mateToTargetAvoidingPath
    {certificate : Certificate} {state : ReservationState}
    {boundary : RawTokenAge} {target : Vertex}
    (correct : certificate.DeclarativelyCorrect)
    (consumer : ConnectiveBelow certificate target)
    (location :
      FutureWorkAtExactWaitingLocation certificate state boundary
        consumer.conclusion) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = consumer.mate ∧
        path.finish = target ∧
        consumer.conclusion ∉ path.vertices := by
  have parEq := location.consumerKind_eq_par correct.1 consumer
  have parLookup :
      certificate.links[consumer.linkIndex]? =
        some (.par consumer.storedLeft consumer.storedRight consumer.conclusion) := by
    simpa [SequentialConnectiveKind.asLink, parEq] using consumer.link_eq
  rcases correct.parPremises_referencePath_avoids_conclusion
      (List.mem_of_getElem? parLookup) with
    ⟨path, pathStarts, pathFinishes, pathAvoids⟩
  cases sideEq : consumer.side with
  | storedLeft =>
      refine ⟨path.reverse, ?_, ?_, ?_⟩
      · change path.finish = consumer.mate
        exact pathFinishes.trans (by
          simp [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEq])
      · change path.start = target
        exact pathStarts.trans (by
          simpa [TensorPremiseSide.premise, sideEq] using
            consumer.premise_eq.symm)
      · simpa using pathAvoids
  | storedRight =>
      refine ⟨path, ?_, ?_, pathAvoids⟩
      · exact pathStarts.trans (by
          simp [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEq])
      · exact pathFinishes.trans (by
          simpa [TensorPremiseSide.premise, sideEq] using
            consumer.premise_eq.symm)

/-- When the consumed waiting premise represents the active carrier, its
opposite older mate is outside that carrier. The exact avoiding path therefore
retains both its target and an outside-to-inside directed re-entry occurrence. -/
theorem FutureWorkAtExactWaitingLocation.activeTargetMateAlignedAvoidingReentry
    {certificate : Certificate} {state : ReservationState}
    {active boundary targetAge : RawTokenAge} {target : Vertex}
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[active]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    (consumer : ConnectiveBelow certificate target)
    (location :
      FutureWorkAtExactWaitingLocation certificate state boundary
        consumer.conclusion)
    (targetMarked : state.core.marks[target]? = some (some targetAge))
    (targetRepresentative : state.core.representative targetAge = active)
    (boundaryOlder : boundary < active) :
    consumer.kind = .par ∧
      Certificate.OwnedOccurrenceAccounted state.core active component owned ∧
      target ∈ owned ∧
      consumer.mate ∉ owned ∧
      ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (directed : certificate.referenceSwitchingGraph.DirectedEdge),
        path.start = consumer.mate ∧
          path.finish = target ∧
          directed ∈ path.traversed ∧
          directed.source ∉ owned ∧
          directed.target ∈ owned ∧
          consumer.conclusion ∉ path.vertices := by
  have parEq := location.consumerKind_eq_par correct.1 consumer
  rcases SchedulerInvariant.exactMarkedOccurrenceOwner invariant targetMarked with
    ⟨ownerRawAge, ownerIndex, ownerComponent, _ownerUsed, ownerOwned,
      ownerMarked, ownerRepresentative, ownerLookup, ownerOccurrence,
      ownerAccounted, ownerMembership⟩
  have ownerRawAgeEq : ownerRawAge = targetAge := by
    exact Option.some.inj
      (Option.some.inj (ownerMarked.symm.trans targetMarked))
  subst ownerRawAge
  have ownerIndexEq : ownerIndex = active :=
    ownerRepresentative.symm.trans targetRepresentative
  have ownerLookupAtActive :
      state.core.components[active]? = some (some ownerComponent) := by
    simpa [ownerIndexEq] using ownerLookup
  have ownerComponentEq : ownerComponent = component := by
    exact Option.some.inj
      (Option.some.inj (ownerLookupAtActive.symm.trans componentLookup))
  subst ownerComponent
  have ownerOwnedEq : ownerOwned = owned :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      ownerOccurrence.derivation occurrence.derivation
  have activeAccounted :
      Certificate.OwnedOccurrenceAccounted state.core active component owned := by
    simpa [ownerIndexEq, ownerOwnedEq] using ownerAccounted
  have targetOwned : target ∈ owned := by
    simpa [ownerOwnedEq] using ownerMembership
  rcases location.activeTargetProducerOrientation invariant consumer targetMarked
      targetRepresentative boundaryOlder with
    ⟨_payload, _linkIndex, _left, _right, olderPremise, _youngerPremise,
      olderAge, _youngerAge, _youngerBoundary, _waitingAt, _member,
      _linkLookup, _sourceLookup, _unmarked, _premiseOrientation,
      olderMarked, _youngerMarked, _olderBoundary, _youngerBoundaryLookup,
      _boundaryLt, _targetYounger, mateOlder, _targetAgeEq,
      _youngerBoundaryActive, olderRepresentative,
      _youngerRepresentative⟩
  have mateMarked :
      state.core.marks[consumer.mate]? = some (some olderAge) := by
    rw [mateOlder]
    exact olderMarked
  have mateOutside : consumer.mate ∉ owned := by
    intro mateOwned
    rcases activeAccounted consumer.mate mateOwned with marked | unmarked
    · rcases marked with ⟨actualAge, actualMarked, actualRepresentative⟩
      have actualAgeEq : actualAge = olderAge := by
        exact Option.some.inj
          (Option.some.inj (actualMarked.symm.trans mateMarked))
      have boundaryEqActive : boundary = active := by
        rw [← olderRepresentative, ← actualAgeEq]
        exact actualRepresentative
      exact (Nat.ne_of_lt boundaryOlder) boundaryEqActive
    · rcases unmarked with ⟨mateUnmarked, _mateFrontier⟩
      rw [mateMarked] at mateUnmarked
      simp at mateUnmarked
  rcases location.mateToTargetAvoidingPath correct consumer with
    ⟨path, pathStarts, pathFinishes, pathAvoids⟩
  have finishOwned : path.finish ∈ owned := by
    simpa [pathFinishes] using targetOwned
  have startOutside : path.start ∉ owned := by
    simpa [pathStarts] using mateOutside
  have finishMembership : path.finish ∈ path.vertices := by
    simpa [Graph.EdgeSimplePath.vertices] using
      path.walk.finish_mem_visitedVertices
  have finishInside : (!(owned.contains path.finish)) = false := by
    simp [finishOwned]
  rcases path.exists_traversed_boundary_of_start_true
      (fun vertex ↦ !(owned.contains vertex))
      (by simpa using startOutside)
      ⟨path.finish, finishMembership, finishInside⟩ with
    ⟨directed, directedMembership, sourceOutside, targetInside⟩
  exact ⟨parEq, activeAccounted, targetOwned, mateOutside, path, directed,
    pathStarts, pathFinishes, directedMembership, by simpa using sourceOutside,
    by simpa using targetInside, pathAvoids⟩

/-- Wrapper-oriented form of `activeTargetMateAlignedAvoidingReentry`. The
packaged re-entry uses the exact mate-to-target path and directed boundary
occurrence retained by that stronger theorem. -/
theorem FutureWorkAtExactWaitingLocation.activeTargetMateAvoidingReentry
    {certificate : Certificate} {state : ReservationState}
    {active boundary targetAge : RawTokenAge} {target : Vertex}
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[active]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    (consumer : ConnectiveBelow certificate target)
    (location :
      FutureWorkAtExactWaitingLocation certificate state boundary
        consumer.conclusion)
    (targetMarked : state.core.marks[target]? = some (some targetAge))
    (targetRepresentative : state.core.representative targetAge = active)
    (boundaryOlder : boundary < active) :
    consumer.kind = .par ∧
      Certificate.OwnedOccurrenceAccounted state.core active component owned ∧
      target ∈ owned ∧
      consumer.mate ∉ owned ∧
      ActiveCarrierExternalEndpointReentryAvoiding certificate owned
        consumer.mate consumer.conclusion := by
  rcases location.activeTargetMateAlignedAvoidingReentry correct invariant
      componentLookup occurrence consumer targetMarked targetRepresentative
      boundaryOlder with
    ⟨parEq, activeAccounted, targetOwned, mateOutside, path, directed,
      pathStarts, pathFinishes, directedMembership, sourceOutside,
      targetInside, pathAvoids⟩
  have finishOwned : path.finish ∈ owned := by
    simpa [pathFinishes] using targetOwned
  exact ⟨parEq, activeAccounted, targetOwned, mateOutside, path, directed,
    pathStarts, finishOwned, directedMembership, sourceOutside, targetInside,
    pathAvoids⟩

end SequentialFigure7
end ProofNetIR
