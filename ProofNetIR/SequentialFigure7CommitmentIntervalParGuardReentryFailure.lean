/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParGuardReentry

/-!
# Figure-7 commitment-interval par-guard re-entry failure target

Eliminates the selected-head target from the strictly older stored-right mate
branch of the Nop and Wait interval outcomes. The all-left reference switching,
parent uniqueness, and strict formula complexity make a stored-right selected
target impossible. Under exact failure of the non-global ready-tail obligation,
the remaining re-entry target is therefore a distinct authenticated mark at the
active representative.

The avoiding and equal-final selected/mate branches remain. This module does
not eliminate the marked target, derive the history-tail law, or prove progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState

private theorem connectiveSelectedMembership
    {certificate : Certificate} {selected : Vertex}
    (consumer : ConnectiveBelow certificate selected) :
    selected ∈ consumer.submittedLink.premises := by
  rcases consumer with
    ⟨linkIndex, kind, storedLeft, storedRight, conclusion, side,
      consumerEq, linkEq, wellFormed, premiseEq⟩
  subst selected
  cases kind <;> cases side <;>
    simp [ConnectiveBelow.submittedLink, SequentialConnectiveKind.asLink,
      Link.premises, TensorPremiseSide.premise]

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

private theorem inboundParentEdge_target_ne_selected_of_storedRight
    {certificate : Certificate} {state : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (input : ReadyHeadInput state)
    (consumer : ConnectiveBelow certificate input.vertex)
    (parEq : consumer.kind = .par)
    (sideRight : consumer.side = .storedRight)
    {component : UnificationComponent} {owned : List Vertex}
    (directed : certificate.referenceSwitchingGraph.DirectedEdge)
    (parentEdge :
      ActiveCarrierInboundParentEdge certificate component owned directed) :
    directed.target ≠ input.vertex := by
  intro targetSelected
  rcases parentEdge with
    ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
      targetFrontier, targetNotGlobal, linkLookup, targetPremise,
      conclusionOutside⟩
  have targetPremiseSelected :
      input.vertex ∈
        (kind.asLink storedLeft storedRight conclusion).premises := by
    simpa [targetSelected] using targetPremise
  have sameLink :
      kind.asLink storedLeft storedRight conclusion = consumer.submittedLink :=
    UnificationState.StructurallyWellFormed.parentLink_unique structural
      (List.mem_of_getElem? linkLookup) targetPremiseSelected
      (List.mem_of_getElem? consumer.link_eq)
      (connectiveSelectedMembership consumer)
  have sourceCurrent : directed.source = consumer.conclusion := by
    rw [sourceEq]
    cases kindEq : kind <;>
      simp [ConnectiveBelow.submittedLink, SequentialConnectiveKind.asLink,
        kindEq, parEq] at sameLink
    exact sameLink.2.2
  have currentStrict :
      certificate.formulaComplexityAt input.vertex <
        certificate.formulaComplexityAt consumer.conclusion := by
    have strict := consumer.wellFormed.premise_complexity_lt_conclusion
      (connectiveSelectedMembership consumer)
    simpa [ConnectiveBelow.submittedLink, SequentialConnectiveKind.asLink, parEq,
      Certificate.linkConclusionComplexity] using strict
  rcases directed with ⟨edgeIndex, edge, edgeLookup, forward⟩
  have originLookup := edgeLookup
  rw [UnificationMarking.referenceSwitchingGraph_edges_eq_leftRetained] at originLookup
  rcases Certificate.linkLeftRetainedEdges_lookup_origin originLookup with
    axiomOrigin | connectiveOrigin
  · rcases axiomOrigin with ⟨originIndex, left, right, originLink, edgeEq⟩
    cases forward <;>
      simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target, edgeEq]
        at sourceCurrent targetSelected
    · exact structural.axiomEndpoint_ne_connectiveConclusion
        (endpoint := consumer.conclusion)
        (List.mem_of_getElem? originLink) (.inr sourceCurrent.symm)
        (List.mem_of_getElem? consumer.link_eq)
        (by simp [SequentialConnectiveKind.asLink, parEq, Link.produces])
    · exact structural.axiomEndpoint_ne_connectiveConclusion
        (endpoint := consumer.conclusion)
        (List.mem_of_getElem? originLink) (.inl sourceCurrent.symm)
        (List.mem_of_getElem? consumer.link_eq)
        (by simp [SequentialConnectiveKind.asLink, parEq, Link.produces])
  · rcases connectiveOrigin with tensorOrigin | parOrigin
    · rcases tensorOrigin with
        ⟨originIndex, left, right, originConclusion, originLink,
          leftEdge | rightEdge⟩
      · cases forward <;>
          simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target, leftEdge]
            at sourceCurrent targetSelected
        · have same :=
            UnificationState.StructurallyWellFormed.parentLink_unique structural
              (List.mem_of_getElem? originLink)
              (by simp [Link.premises, targetSelected])
              (List.mem_of_getElem? consumer.link_eq)
              (connectiveSelectedMembership consumer)
          simp [SequentialConnectiveKind.asLink, parEq] at same
        · have originPremise :
              consumer.conclusion ∈
                (Link.tensor left right originConclusion).premises := by
            simp [Link.premises, ← sourceCurrent]
          have originStrict :=
            (structural.2.2.2.2.1 _ (List.mem_of_getElem? originLink))
              |>.premise_complexity_lt_conclusion originPremise
          have reverseStrict :
              certificate.formulaComplexityAt consumer.conclusion <
                certificate.formulaComplexityAt input.vertex := by
            simpa [Certificate.linkConclusionComplexity, targetSelected] using
              originStrict
          omega
      · cases forward <;>
          simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target, rightEdge]
            at sourceCurrent targetSelected
        · have same :=
            UnificationState.StructurallyWellFormed.parentLink_unique structural
              (List.mem_of_getElem? originLink)
              (by simp [Link.premises, targetSelected])
              (List.mem_of_getElem? consumer.link_eq)
              (connectiveSelectedMembership consumer)
          simp [SequentialConnectiveKind.asLink, parEq] at same
        · have originPremise :
              consumer.conclusion ∈
                (Link.tensor left right originConclusion).premises := by
            simp [Link.premises, ← sourceCurrent]
          have originStrict :=
            (structural.2.2.2.2.1 _ (List.mem_of_getElem? originLink))
              |>.premise_complexity_lt_conclusion originPremise
          have reverseStrict :
              certificate.formulaComplexityAt consumer.conclusion <
                certificate.formulaComplexityAt input.vertex := by
            simpa [Certificate.linkConclusionComplexity, targetSelected] using
              originStrict
          omega
    · rcases parOrigin with
        ⟨originIndex, left, right, originConclusion, originLink, edgeEq⟩
      cases forward <;>
        simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target, edgeEq]
          at sourceCurrent targetSelected
      · have same :=
          UnificationState.StructurallyWellFormed.parentLink_unique structural
            (List.mem_of_getElem? originLink)
            (by simp [Link.premises, targetSelected])
            (List.mem_of_getElem? consumer.link_eq)
            (connectiveSelectedMembership consumer)
        have selectedRight : input.vertex = consumer.storedRight := by
          simpa [TensorPremiseSide.premise, sideRight] using consumer.premise_eq
        have samePar :
            Link.par left right originConclusion =
              Link.par consumer.storedLeft consumer.storedRight
                consumer.conclusion := by
          simpa [ConnectiveBelow.submittedLink,
            SequentialConnectiveKind.asLink, parEq] using same
        injection samePar with leftEq rightEq conclusionEq
        have consumerWellFormed :
            certificate.LinkWellFormed
              (.par consumer.storedLeft consumer.storedRight
                consumer.conclusion) := by
          simpa [SequentialConnectiveKind.asLink, parEq] using
            consumer.wellFormed
        exact consumerWellFormed.1
          (leftEq.symm.trans (targetSelected.trans selectedRight))
      · have originPremise :
            consumer.conclusion ∈
              (Link.par left right originConclusion).premises := by
          simp [Link.premises, ← sourceCurrent]
        have originStrict :=
          (structural.2.2.2.2.1 _ (List.mem_of_getElem? originLink))
            |>.premise_complexity_lt_conclusion originPremise
        have reverseStrict :
            certificate.formulaComplexityAt consumer.conclusion <
              certificate.formulaComplexityAt input.vertex := by
          simpa [Certificate.linkConclusionComplexity, targetSelected] using
            originStrict
        omega

private theorem ActiveCarrierExternalReentryTargetStatus.markedHistoricalTarget_of_storedRight
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    (consumer : ConnectiveBelow certificate input.vertex)
    (parEq : consumer.kind = .par)
    (sideRight : consumer.side = .storedRight)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned)
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core input.rawAge component owned)
    {endpoint : Vertex}
    (status :
      ActiveCarrierExternalReentryTargetStatus certificate state input component
        owned endpoint)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryMarkedHistoricalTarget tagHistory input component
      owned endpoint := by
  rcases status with
    ⟨path, directed, pathStarts, finishOwned, directedMembership,
      parentEdge, selected | tail | marked⟩
  · have targetNeSelected :=
      inboundParentEdge_target_ne_selected_of_storedRight invariant.structural
        input consumer parEq sideRight directed parentEdge
    exact False.elim (targetNeSelected selected.1)
  · rcases parentEdge with
      ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
        targetFrontier, targetNotGlobal, linkLookup, targetPremise,
        conclusionOutside⟩
    exact False.elim (noTail ⟨directed.target, tail.1, targetNotGlobal⟩)
  · rcases marked with ⟨markedAge, targetMarked⟩
    have targetNeSelected :=
      inboundParentEdge_target_ne_selected_of_storedRight invariant.structural
        input consumer parEq sideRight directed parentEdge
    rcases parentEdge with
      ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
        targetFrontier, targetNotGlobal, linkLookup, targetPremise,
        conclusionOutside⟩
    have targetOwned : directed.target ∈ owned :=
      occurrence.derivation.frontier_subset_owned directed.target targetFrontier
    rcases accounted directed.target targetOwned with markedCase | rawCase
    · rcases markedCase with
        ⟨actualAge, actualMarked, actualRepresentative⟩
      have actualAgeEq : actualAge = markedAge := by
        exact Option.some.inj
          (Option.some.inj (actualMarked.symm.trans targetMarked))
      have targetRepresentative :
          state.core.representative markedAge = input.rawAge := by
        simpa [actualAgeEq] using actualRepresentative
      exact ⟨path, directed, markedAge, pathStarts, finishOwned,
        directedMembership,
        ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
          targetFrontier, targetNotGlobal, linkLookup, targetPremise,
          conclusionOutside⟩,
        targetNeSelected, targetMarked,
        tagHistory.final_rawMarked_iff.mp targetMarked, targetRepresentative⟩
    · rw [rawCase.1] at targetMarked
      simp at targetMarked

namespace CanonicalTagHistory

private theorem CommitmentIntervalParTraceOutcome.mapOlderMateStatusOfStoredRight
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state}
    {consumer : ConnectiveBelow certificate input.vertex}
    {position edgeCount : Nat} {first : RawTokenAge}
    {beforeStatus afterStatus : Prop}
    (outcome : tagHistory.CommitmentIntervalParTraceOutcome input consumer
      position edgeCount first beforeStatus)
    (mapStatus :
      consumer.side = .storedRight → beforeStatus → afterStatus) :
    tagHistory.CommitmentIntervalParTraceOutcome input consumer position
      edgeCount first afterStatus := by
  cases outcome with
  | avoiding path => exact .avoiding path
  | equalSelected offset parent child event offsetLt parentAt childAt
      notAvoiding membership eventAge childEq side beforeTrace afterTrace trace =>
      exact .equalSelected offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childEq side beforeTrace afterTrace trace
  | equalMate offset parent child event offsetLt parentAt childAt notAvoiding
      membership eventAge childEq side beforeTrace afterTrace trace =>
      exact .equalMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childEq side beforeTrace afterTrace trace
  | olderMate offset parent child event offsetLt parentAt childAt notAvoiding
      membership eventAge childLt side beforeTrace afterTrace trace status =>
      exact .olderMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childLt side beforeTrace afterTrace trace
        (mapStatus side status)

end CanonicalTagHistory

/-- Under exact failure of the non-global ready-tail obligation, the strictly
older Nop mate re-enters the active carrier at a distinct authenticated marked
target represented by the active boundary. -/
theorem NopStep.commitmentInterval_parTraceReentryMarkedOutcome
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
        some step.prepared.stackResult.rawAge)
    (noTail :
      ¬ ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) :
    tagHistory.CommitmentIntervalParTraceOutcome
      step.prepared.readyHeadInput step.consumer position edgeCount first
        (step.consumer.mate ∉ owned ∧
          before.core.marks[step.consumer.mate]? = some none ∧
          ActiveCarrierExternalReentryMarkedHistoricalTarget tagHistory
            step.prepared.readyHeadInput component owned step.consumer.mate) := by
  apply (step.commitmentInterval_parTraceReentryTargetOutcome connected tagHistory
    invariant componentLookup occurrence positive firstAt lastAt)
      |>.mapOlderMateStatusOfStoredRight
  intro side status
  rcases status with ⟨mateOutside, mateUnmarked, targetStatus⟩
  exact ⟨mateOutside, mateUnmarked,
    targetStatus.markedHistoricalTarget_of_storedRight tagHistory
      step.prepared.readyHeadInput invariant step.consumer step.par_eq side
      occurrence (step.prepared.readyHeadInput.selected_owned_accounted invariant
        componentLookup occurrence).2 noTail⟩

/-- Under exact failure of the non-global ready-tail obligation, the strictly
older Wait mate re-enters the active carrier at a distinct authenticated marked
target represented by the active boundary. -/
theorem WaitStep.commitmentInterval_parTraceReentryMarkedOutcome
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
        some step.prepared.stackResult.rawAge)
    (noTail :
      ¬ ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) :
    tagHistory.CommitmentIntervalParTraceOutcome
      step.prepared.readyHeadInput step.consumer position edgeCount first
        (step.consumer.mate ∉ owned ∧
          before.core.marks[step.consumer.mate]? =
            some (some step.mateRawAge) ∧
          before.core.representative step.mateRawAge <
            step.prepared.stackResult.rawAge ∧
          ActiveCarrierExternalReentryMarkedHistoricalTarget tagHistory
            step.prepared.readyHeadInput component owned step.consumer.mate) := by
  apply (step.commitmentInterval_parTraceReentryTargetOutcome connected tagHistory
    invariant componentLookup occurrence positive firstAt lastAt)
      |>.mapOlderMateStatusOfStoredRight
  intro side status
  rcases status with
    ⟨mateOutside, mateMarked, representativeOlder, targetStatus⟩
  exact ⟨mateOutside, mateMarked, representativeOlder,
    targetStatus.markedHistoricalTarget_of_storedRight tagHistory
      step.prepared.readyHeadInput invariant step.consumer step.par_eq side
      occurrence (step.prepared.readyHeadInput.selected_owned_accounted invariant
        componentLookup occurrence).2 noTail⟩

end SequentialFigure7
end ProofNetIR
