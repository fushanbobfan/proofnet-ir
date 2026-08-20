/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtParentExternalCommitmentOutcome

/-!
# Active-top debt external parent commitment re-entry

Every positive interval of adjacent retained `sigma` commitments composes to
one reference-switching path between its endpoint reservation events. For the
external parent outcome, this path brings ready future work and concretely
marked older endpoints back into the active occurrence carrier and retains an
exact outside-to-inside edge. Waiting work keeps its exact waiting cell, and
the external raw branch remains unchanged.

This is a geometric return reduction. It does not classify the re-entry edge,
produce a distinct ready-tail payer, derive `ActiveTopDebtTailLaw`, or prove
progress, completion, termination, or totality.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

private theorem representative_eq_of_sigmaAt
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {position : Nat} {rawAge : RawTokenAge}
    (sigmaAt : state.stack.sigma[position]? = some rawAge) :
    state.core.representative rawAge = rawAge := by
  have rawAgeMembership : rawAge ∈ state.stack.sigma :=
    List.mem_of_getElem? sigmaAt
  have rawAgeBound : rawAge < state.stack.nextAge :=
    invariant.stack_wellShaped.sigma_partition.boundary_lt rawAge
      rawAgeMembership
  rcases invariant.stack_wellShaped.sigma_partition.boundary_exists
      rawAgeBound with ⟨boundary, boundaryLookup⟩
  have boundaryLeRawAge : boundary ≤ rawAge := sigmaBoundary?_le boundaryLookup
  have rawAgeLeBoundary : rawAge ≤ boundary :=
    sigmaBoundary?_greatest
      invariant.stack_wellShaped.sigma_partition.strictIncreasing
      boundaryLookup rawAge rawAgeMembership (Nat.le_refl _)
  have boundaryEq : boundary = rawAge :=
    Nat.le_antisymm boundaryLeRawAge rawAgeLeBoundary
  subst boundary
  have representativeLookup :=
    invariant.realizesSigma.representative_eq_boundary rawAgeBound
  exact Option.some.inj (representativeLookup.symm.trans boundaryLookup)

private theorem connectErasePaths
    {graph : Graph} (first second : graph.EdgeSimplePath)
    (meeting : first.finish = second.start) :
    ∃ path : graph.EdgeSimplePath,
      path.start = first.start ∧ path.finish = second.finish := by
  have secondWalk : graph.EdgeWalk first.finish second.traversed second.finish := by
    rw [meeting]
    exact second.walk
  have combined :
      graph.EdgeWalk first.start (first.traversed ++ second.traversed)
        second.finish :=
    first.walk.trans secondWalk
  rcases combined.toEdgeSimplePathWithVerticesSubset with
    ⟨path, pathStarts, pathFinishes, _subset⟩
  exact ⟨path, pathStarts, pathFinishes⟩

/-- A structured path from an external endpoint back into one active owned
carrier, retaining one exact outside-to-inside stored edge. -/
def ActiveCarrierExternalEndpointReentry
    (certificate : Certificate) (owned : List Vertex) (endpoint : Vertex) : Prop :=
  ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
      (directed : certificate.referenceSwitchingGraph.DirectedEdge),
    path.start = endpoint ∧
      path.finish ∈ owned ∧
      directed ∈ path.traversed ∧
      directed.source ∉ owned ∧
      directed.target ∈ owned

private theorem externalEndpointReentry
    {certificate : Certificate} {owned : List Vertex} {endpoint : Vertex}
    (endpointOutside : endpoint ∉ owned)
    (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (pathStarts : path.start = endpoint)
    (finishOwned : path.finish ∈ owned) :
    ActiveCarrierExternalEndpointReentry certificate owned endpoint := by
  have startOutside : path.start ∉ owned := by
    simpa [pathStarts] using endpointOutside
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
  exact ⟨path, directed, pathStarts, finishOwned, directedMembership,
    by simpa using sourceOutside, by simpa using targetInside⟩

namespace CanonicalTagHistory

/-- One exact reference-switching path between the reservation endpoints of a
positive retained commitment interval. -/
def CommitmentIntervalReferencePath
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (first last : RawTokenAge) : Prop :=
  ∃ (firstEvent lastEvent : ReservationEvent certificate)
      (path : certificate.referenceSwitchingGraph.EdgeSimplePath),
    tagHistory.reservationLedger[first]? = some firstEvent ∧
      tagHistory.reservationLedger[last]? = some lastEvent ∧
      path.start = firstEvent.search.result.left ∧
      path.finish = lastEvent.search.result.left

private theorem adjacentCommitmentIntervalReferencePath
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    {position : Nat} {parent child : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt : state.stack.sigma[position + 1]? = some child) :
    tagHistory.CommitmentIntervalReferencePath parent child := by
  rcases tagHistory.commitmentEdge_referencePath invariant parentAt childAt with
    ⟨before, after, step, parentEvent, parentComponent, childComponent,
      parentEventUsed, parentForestUsed, parentOwned, childEventUsed,
      childForestUsed, childOwned, parentAnchor, committedPath, childAnchor,
      canonicalPath, parentLookup, childLookup, parentRawAge, parentEq, childEq,
      selectedMarked, parentComponentLookup, parentDerivation, parentLink,
      parentWitness, parentAccounted, selectedOwned, parentLeftOwned,
      childComponentLookup, childDerivation, childLink, childWitness,
      childAccounted, reachedOwned, parentAnchorStarts, parentAnchorFinishes,
      parentAnchorWithin, committedStarts, committedFinishes, childAnchorStarts,
      childAnchorFinishes, childAnchorWithin, canonicalStarts,
      canonicalFinishes, reachedEndpoint⟩
  exact ⟨parentEvent, .new step, canonicalPath, parentLookup, childLookup,
    canonicalStarts, canonicalFinishes⟩

/-- Compose every adjacent commitment path in one supplied positive retained
`sigma` interval. Loop erasure preserves the exact endpoint events. -/
theorem commitmentInterval_referencePath
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    {position edgeCount : Nat} {first last : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : state.stack.sigma[position]? = some first)
    (lastAt : state.stack.sigma[position + edgeCount]? = some last) :
    tagHistory.CommitmentIntervalReferencePath first last := by
  induction edgeCount generalizing position first last with
  | zero => omega
  | succ remaining induction =>
      have endBound :
          position + Nat.succ remaining < state.stack.sigma.length :=
        (List.getElem?_eq_some_iff.mp lastAt).choose
      have nextBound : position + 1 < state.stack.sigma.length := by
        omega
      let middle := state.stack.sigma[position + 1]
      have middleAt :
          state.stack.sigma[position + 1]? = some middle :=
        List.getElem?_eq_getElem nextBound
      rcases adjacentCommitmentIntervalReferencePath tagHistory invariant
          firstAt middleAt with
        ⟨firstEvent, middleEvent, firstPath, firstEventAt, middleEventAt,
          firstStarts, firstFinishes⟩
      by_cases noTail : remaining = 0
      · subst remaining
        have sameAge : middle = last := by
          apply Option.some.inj
          exact middleAt.symm.trans (by simpa using lastAt)
        subst last
        exact ⟨firstEvent, middleEvent, firstPath, firstEventAt,
          middleEventAt, firstStarts, firstFinishes⟩
      · have indexEq :
            position + Nat.succ remaining = (position + 1) + remaining := by
          omega
        have tailLastAt :
            state.stack.sigma[(position + 1) + remaining]? = some last := by
          rw [← indexEq]
          exact lastAt
        rcases induction (Nat.zero_lt_of_ne_zero noTail) middleAt tailLastAt with
          ⟨tailFirstEvent, lastEvent, tailPath, tailFirstAt, lastEventAt,
            tailStarts, tailFinishes⟩
        have sameMiddleEvent : middleEvent = tailFirstEvent := by
          apply Option.some.inj
          exact middleEventAt.symm.trans tailFirstAt
        subst tailFirstEvent
        have meeting : firstPath.finish = tailPath.start :=
          firstFinishes.trans tailStarts.symm
        have tailWalk :
            certificate.referenceSwitchingGraph.EdgeWalk firstPath.finish
              tailPath.traversed tailPath.finish := by
          rw [meeting]
          exact tailPath.walk
        have combined :
            certificate.referenceSwitchingGraph.EdgeWalk firstPath.start
              (firstPath.traversed ++ tailPath.traversed) tailPath.finish :=
          firstPath.walk.trans tailWalk
        rcases combined.toEdgeSimplePathWithVerticesSubset with
          ⟨path, pathStarts, pathFinishes, _subset⟩
        exact ⟨firstEvent, lastEvent, path, firstEventAt, lastEventAt,
          pathStarts.trans firstStarts, pathFinishes.trans tailFinishes⟩

private theorem StrictOlderCommitmentSplit.intervalReferencePath
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {first active : RawTokenAge}
    (split : tagHistory.StrictOlderCommitmentSplit first active)
    (invariant : SchedulerInvariant certificate state) :
    tagHistory.CommitmentIntervalReferencePath first active := by
  rcases split with
    ⟨position, edgeCount, predecessor, firstAt, predecessorAt, activeAt,
      representativeOlder, finalCommitment⟩
  apply tagHistory.commitmentInterval_referencePath invariant
      (position := position) (edgeCount := edgeCount + 1) (by omega) firstAt
  simpa [Nat.add_assoc] using activeAt

private theorem event_rawAge_eq_of_lookup
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {rawAge : RawTokenAge} {event : ReservationEvent certificate}
    (lookup : tagHistory.reservationLedger[rawAge]? = some event) :
    event.rawAge = rawAge := by
  have bound : rawAge < state.stack.nextAge := by
    rw [← tagHistory.reservationLedger_length]
    exact (List.getElem?_eq_some_iff.mp lookup).1
  simpa [lookup] using
    (tagHistory.reservationLedger_getElem?_rawAge rawAge bound)

private theorem StrictOlderCommitmentSplit.markedEndpointReentry
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {active : RawTokenAge} {owned : List Vertex}
    (split : tagHistory.StrictOlderCommitmentSplit
      (state.core.representative conclusionAge) active)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks : List Nat}
    (componentLookup :
      state.core.components[active]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (marked : state.core.marks[conclusion]? = some (some conclusionAge))
    (outside : conclusion ∉ owned) :
    ActiveCarrierExternalEndpointReentry certificate owned conclusion := by
  rcases split with
    ⟨position, edgeCount, predecessor, firstAt, predecessorAt, activeAt,
      representativeOlder, finalCommitment⟩
  have splitAgain :
      tagHistory.StrictOlderCommitmentSplit
        (state.core.representative conclusionAge) active :=
    ⟨position, edgeCount, predecessor, firstAt, predecessorAt, activeAt,
      representativeOlder, finalCommitment⟩
  rcases splitAgain.intervalReferencePath invariant with
    ⟨firstEvent, lastEvent, intervalPath, firstEventAt, lastEventAt,
      intervalStarts, intervalFinishes⟩
  have firstEventMembership : firstEvent ∈ tagHistory.reservationLedger :=
    List.mem_of_getElem? firstEventAt
  rcases tagHistory.reservationLedger_axiomEndpoints_accounted
      invariant.structural firstEventMembership with
    ⟨firstComponent, firstEventUsed, firstForestUsed, firstOwned,
      firstComponentLookup, firstDerivation, firstLink, firstOccurrence,
      firstAccounted, firstLeftOwned, firstRightOwned⟩
  rcases SchedulerInvariant.exactMarkedOccurrenceOwner invariant marked with
    ⟨ownerRawAge, ownerIndex, ownerComponent, ownerUsed, ownerOwned,
      ownerMarked, ownerRepresentative, ownerLookup, ownerOccurrence,
      ownerAccounted, conclusionOwnerMembership⟩
  have ownerRawAgeEq : ownerRawAge = conclusionAge := by
    exact Option.some.inj (Option.some.inj (ownerMarked.symm.trans marked))
  subst ownerRawAge
  have firstEventRawAge :
      firstEvent.rawAge = state.core.representative conclusionAge :=
    event_rawAge_eq_of_lookup tagHistory firstEventAt
  have stackMarked :
      state.stack.marks[conclusion]? = some (some conclusionAge) := by
    rw [← invariant.realizesSigma.marks_eq]
    exact marked
  have conclusionAgeBound : conclusionAge < state.core.parents.size := by
    rw [invariant.realizesSigma.horizon_eq]
    exact invariant.stack_wellShaped.assigned_age_bound conclusion
      conclusionAge stackMarked
  have ownerRoot : state.core.representative ownerIndex = ownerIndex := by
    rw [← ownerRepresentative]
    exact UnificationState.OrderedParents.representative_idempotent
      invariant.core_orderedParents conclusionAgeBound
  have firstComponentLookupAtOwner :
      state.core.components[ownerIndex]? = some (some firstComponent) := by
    simpa [firstEventRawAge, ownerRepresentative, ownerRoot] using
      firstComponentLookup
  have firstComponentEq : firstComponent = ownerComponent := by
    exact Option.some.inj
      (Option.some.inj (firstComponentLookupAtOwner.symm.trans ownerLookup))
  subst firstComponent
  have firstOwnedEq : firstOwned = ownerOwned :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      firstOccurrence.derivation ownerOccurrence.derivation
  have conclusionFirstOwned : conclusion ∈ firstOwned := by
    simpa [firstOwnedEq] using conclusionOwnerMembership
  rcases firstOccurrence.referencePath_within_owned conclusionFirstOwned
      firstLeftOwned with
    ⟨firstPath, firstPathStarts, firstPathFinishes, firstPathWithin⟩
  have firstMeeting : firstPath.finish = intervalPath.start :=
    firstPathFinishes.trans intervalStarts.symm
  rcases connectErasePaths firstPath intervalPath firstMeeting with
    ⟨combinedPath, combinedStarts, combinedFinishes⟩
  have lastEventMembership : lastEvent ∈ tagHistory.reservationLedger :=
    List.mem_of_getElem? lastEventAt
  rcases tagHistory.reservationLedger_axiomEndpoints_accounted
      invariant.structural lastEventMembership with
    ⟨lastComponent, lastEventUsed, lastForestUsed, lastOwned,
      lastComponentLookup, lastDerivation, lastLink, lastOccurrence,
      lastAccounted, lastLeftOwned, lastRightOwned⟩
  have lastEventRawAge : lastEvent.rawAge = active :=
    event_rawAge_eq_of_lookup tagHistory lastEventAt
  have activeRoot : state.core.representative active = active :=
    representative_eq_of_sigmaAt invariant activeAt
  have lastComponentLookupAtActive :
      state.core.components[active]? = some (some lastComponent) := by
    simpa [lastEventRawAge, activeRoot] using lastComponentLookup
  have lastComponentEq : lastComponent = component := by
    exact Option.some.inj
      (Option.some.inj (lastComponentLookupAtActive.symm.trans componentLookup))
  subst lastComponent
  have lastOwnedEq : lastOwned = owned :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      lastOccurrence.derivation occurrence.derivation
  have finishOwned : combinedPath.finish ∈ owned := by
    rw [combinedFinishes, intervalFinishes]
    simpa [lastOwnedEq] using lastLeftOwned
  exact externalEndpointReentry outside combinedPath
    (combinedStarts.trans firstPathStarts) finishOwned

private theorem StrictOlderCommitmentSplit.readyEndpointReentry
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {first active : RawTokenAge} {owned : List Vertex}
    (split : tagHistory.StrictOlderCommitmentSplit first active)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks : List Nat}
    (componentLookup :
      state.core.components[active]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {position : Nat} {bucket : List Vertex}
    (sigmaAt : state.stack.sigma[position]? = some first)
    (readyAt : state.stack.ready[position]? = some bucket)
    (member : conclusion ∈ bucket)
    (outside : conclusion ∉ owned) :
    ActiveCarrierExternalEndpointReentry certificate owned conclusion := by
  rcases split with
    ⟨splitPosition, edgeCount, predecessor, firstAt, predecessorAt,
      activeAt, representativeOlder, finalCommitment⟩
  have splitAgain : tagHistory.StrictOlderCommitmentSplit first active :=
    ⟨splitPosition, edgeCount, predecessor, firstAt, predecessorAt,
      activeAt, representativeOlder, finalCommitment⟩
  rcases splitAgain.intervalReferencePath invariant with
    ⟨firstEvent, lastEvent, intervalPath, firstEventAt, lastEventAt,
      intervalStarts, intervalFinishes⟩
  have firstEventMembership : firstEvent ∈ tagHistory.reservationLedger :=
    List.mem_of_getElem? firstEventAt
  rcases tagHistory.reservationLedger_axiomEndpoints_accounted
      invariant.structural firstEventMembership with
    ⟨firstComponent, firstEventUsed, firstForestUsed, firstOwned,
      firstComponentLookup, firstDerivation, firstLink, firstOccurrence,
      firstAccounted, firstLeftOwned, firstRightOwned⟩
  rcases invariant.ready_bucket_frontier_exact sigmaAt readyAt with
    ⟨readyComponent, readyComponentLookup, readyExact⟩
  have firstEventRawAge : firstEvent.rawAge = first :=
    event_rawAge_eq_of_lookup tagHistory firstEventAt
  have firstRoot : state.core.representative first = first :=
    representative_eq_of_sigmaAt invariant sigmaAt
  have firstComponentLookupAtReady :
      state.core.components[first]? = some (some firstComponent) := by
    simpa [firstEventRawAge, firstRoot] using firstComponentLookup
  have firstComponentEq : firstComponent = readyComponent := by
    exact Option.some.inj
      (Option.some.inj
        (firstComponentLookupAtReady.symm.trans readyComponentLookup))
  subst firstComponent
  have conclusionFrontier : conclusion ∈ readyComponent.frontier :=
    ((readyExact conclusion).mp member).1
  have conclusionFirstOwned : conclusion ∈ firstOwned :=
    firstOccurrence.derivation.frontier_subset_owned conclusion
      conclusionFrontier
  rcases firstOccurrence.referencePath_within_owned conclusionFirstOwned
      firstLeftOwned with
    ⟨firstPath, firstPathStarts, firstPathFinishes, firstPathWithin⟩
  have firstMeeting : firstPath.finish = intervalPath.start :=
    firstPathFinishes.trans intervalStarts.symm
  rcases connectErasePaths firstPath intervalPath firstMeeting with
    ⟨combinedPath, combinedStarts, combinedFinishes⟩
  have lastEventMembership : lastEvent ∈ tagHistory.reservationLedger :=
    List.mem_of_getElem? lastEventAt
  rcases tagHistory.reservationLedger_axiomEndpoints_accounted
      invariant.structural lastEventMembership with
    ⟨lastComponent, lastEventUsed, lastForestUsed, lastOwned,
      lastComponentLookup, lastDerivation, lastLink, lastOccurrence,
      lastAccounted, lastLeftOwned, lastRightOwned⟩
  have lastEventRawAge : lastEvent.rawAge = active :=
    event_rawAge_eq_of_lookup tagHistory lastEventAt
  have activeRoot : state.core.representative active = active :=
    representative_eq_of_sigmaAt invariant activeAt
  have lastComponentLookupAtActive :
      state.core.components[active]? = some (some lastComponent) := by
    simpa [lastEventRawAge, activeRoot] using lastComponentLookup
  have lastComponentEq : lastComponent = component := by
    exact Option.some.inj
      (Option.some.inj
        (lastComponentLookupAtActive.symm.trans componentLookup))
  subst lastComponent
  have lastOwnedEq : lastOwned = owned :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      lastOccurrence.derivation occurrence.derivation
  have finishOwned : combinedPath.finish ∈ owned := by
    rw [combinedFinishes, intervalFinishes]
    simpa [lastOwnedEq] using lastLeftOwned
  exact externalEndpointReentry outside combinedPath
    (combinedStarts.trans firstPathStarts) finishOwned

end CanonicalTagHistory

/-- The external temporal outcome after the whole retained commitment interval
has been composed. Ready future work and marked endpoints re-enter the active
carrier; waiting work retains its exact cell. -/
inductive ActiveCarrierParentExternalCommitmentReentryOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (activeRawAge : RawTokenAge) (owned : List Vertex) : Prop where
  | rawOutside
      (sibling : Vertex)
      (unmarked : state.core.marks[sibling]? = some none)
      (outside : sibling ∉ owned) :
      ActiveCarrierParentExternalCommitmentReentryOutcome tagHistory
        activeRawAge owned
  | olderReady
      (conclusion : Vertex) (boundary : RawTokenAge)
      (position : Nat) (bucket : List Vertex)
      (sigmaAt : state.stack.sigma[position]? = some boundary)
      (readyAt : state.stack.ready[position]? = some bucket)
      (member : conclusion ∈ bucket)
      (older : boundary < activeRawAge)
      (commitmentSplit :
        tagHistory.StrictOlderCommitmentSplit boundary activeRawAge)
      (outside : conclusion ∉ owned)
      (reentry :
        ActiveCarrierExternalEndpointReentry certificate owned conclusion) :
      ActiveCarrierParentExternalCommitmentReentryOutcome tagHistory
        activeRawAge owned
  | olderWaiting
      (conclusion : Vertex) (boundary : RawTokenAge) (payload : List Vertex)
      (waitingAt : state.stack.waiting[boundary]? =
        some (.initialized payload))
      (member : conclusion ∈ payload)
      (older : boundary < activeRawAge)
      (commitmentSplit :
        tagHistory.StrictOlderCommitmentSplit boundary activeRawAge)
      (outside : conclusion ∉ owned) :
      ActiveCarrierParentExternalCommitmentReentryOutcome tagHistory
        activeRawAge owned
  | olderMarked
      (conclusion : Vertex) (conclusionAge : RawTokenAge)
      (marked : state.core.marks[conclusion]? = some (some conclusionAge))
      (olderRepresentative :
        state.core.representative conclusionAge < activeRawAge)
      (commitmentSplit : tagHistory.StrictOlderCommitmentSplit
        (state.core.representative conclusionAge) activeRawAge)
      (outside : conclusion ∉ owned)
      (reentry :
        ActiveCarrierExternalEndpointReentry certificate owned conclusion) :
      ActiveCarrierParentExternalCommitmentReentryOutcome tagHistory
        activeRawAge owned

namespace ActiveCarrierParentExternalCommitmentOutcome

/-- Compose the complete retained commitment interval for both older external
branches. Ready work and marked work return through an exact active-carrier
re-entry; waiting and raw work retain their precise unresolved forms. -/
theorem reentryOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {activeRawAge : RawTokenAge} {owned : List Vertex}
    (outcome : ActiveCarrierParentExternalCommitmentOutcome tagHistory
      activeRawAge owned)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks : List Nat}
    (componentLookup :
      state.core.components[activeRawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned) :
    ActiveCarrierParentExternalCommitmentReentryOutcome tagHistory
      activeRawAge owned := by
  cases outcome with
  | rawOutside sibling unmarked outside =>
      exact .rawOutside sibling unmarked outside
  | olderFuture conclusion boundary work older split outside =>
      cases work with
      | @ready position _ bucket _ sigmaAt readyAt member =>
          exact .olderReady conclusion boundary position bucket sigmaAt readyAt
            member older split outside
            (split.readyEndpointReentry invariant componentLookup occurrence
              sigmaAt readyAt member outside)
      | @waiting _ payload _ waitingAt member =>
          exact .olderWaiting conclusion boundary payload waitingAt member
            older split outside
  | olderMarked conclusion conclusionAge marked older split outside =>
      exact .olderMarked conclusion conclusionAge marked older split outside
        (split.markedEndpointReentry invariant componentLookup occurrence
          marked outside)

end ActiveCarrierParentExternalCommitmentOutcome

end SequentialFigure7
end ProofNetIR
