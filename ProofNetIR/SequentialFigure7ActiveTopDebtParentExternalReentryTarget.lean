/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtParentExternalCommitmentReentry
import ProofNetIR.SequentialFigure7RawMarkHistory

/-!
# Active-top debt external-parent re-entry target

An outside-to-inside reference-switching edge of one occurrence carrier is the
reverse of a submitted connective-parent edge. At an active ready boundary,
its premise target is therefore the selected head, a genuine ready-tail
occurrence, or an already marked active-frontier premise.

This is an exact target classification. It does not eliminate the selected or
marked alternatives for an arbitrary re-entry. Under ready-tail failure, a
re-entry path that additionally avoids the current par conclusion does exclude
the selected target and authenticates the remaining mark at the active
representative. This module does not derive that path-avoidance premise,
produce `ActiveTopDebtTailLaw`, or prove progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge
open Certificate.OccurrenceDerivation

/-- Exact connective-parent origin of an outside-to-inside edge of one
occurrence carrier. -/
def ActiveCarrierInboundParentEdge
    (certificate : Certificate) (component : UnificationComponent)
    (owned : List Vertex)
    (directed : certificate.referenceSwitchingGraph.DirectedEdge) : Prop :=
  ∃ (linkIndex : Nat) (kind : SequentialConnectiveKind)
      (storedLeft storedRight conclusion : Vertex),
    directed.source = conclusion ∧
      directed.target ∈ component.frontier ∧
      directed.target ∉ certificate.conclusions ∧
      certificate.links[linkIndex]? =
        some (kind.asLink storedLeft storedRight conclusion) ∧
      directed.target ∈
        (kind.asLink storedLeft storedRight conclusion).premises ∧
      conclusion ∉ owned

/-- One exact re-entry edge together with the scheduler status of its active
frontier target. -/
def ActiveCarrierExternalReentryTargetStatus
    (certificate : Certificate) (state : ReservationState)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) (endpoint : Vertex) : Prop :=
  ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
      (directed : certificate.referenceSwitchingGraph.DirectedEdge),
    path.start = endpoint ∧
      path.finish ∈ owned ∧
      directed ∈ path.traversed ∧
      ActiveCarrierInboundParentEdge certificate component owned directed ∧
      ((directed.target = input.vertex ∧
          state.core.marks[directed.target]? = some none) ∨
        (directed.target ∈ input.readyTail ∧
          state.core.marks[directed.target]? = some none) ∨
        ∃ markedAge,
          state.core.marks[directed.target]? = some (some markedAge))

/-- Failure-conditioned re-entry status after the non-global ready-tail case
has been excluded. The target is the selected raw head or a prior mark. -/
def ActiveCarrierExternalReentryFailureTargetStatus
    (certificate : Certificate) (state : ReservationState)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) (endpoint : Vertex) : Prop :=
  ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
      (directed : certificate.referenceSwitchingGraph.DirectedEdge),
    path.start = endpoint ∧
      path.finish ∈ owned ∧
      directed ∈ path.traversed ∧
      ActiveCarrierInboundParentEdge certificate component owned directed ∧
      ((directed.target = input.vertex ∧
          state.core.marks[directed.target]? = some none) ∨
        ∃ markedAge,
          state.core.marks[directed.target]? = some (some markedAge))

/-- One external endpoint path whose retained re-entry avoids a specified
forbidden vertex. -/
def ActiveCarrierExternalEndpointReentryAvoiding
    (certificate : Certificate) (owned : List Vertex)
    (endpoint forbidden : Vertex) : Prop :=
  ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
      (directed : certificate.referenceSwitchingGraph.DirectedEdge),
    path.start = endpoint ∧
      path.finish ∈ owned ∧
      directed ∈ path.traversed ∧
      directed.source ∉ owned ∧
      directed.target ∈ owned ∧
      forbidden ∉ path.vertices

/-- Failure-conditioned external re-entry status with exact raw-mark history
for the marked alternative. -/
def ActiveCarrierExternalReentryFailureHistoricalStatus
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) (endpoint : Vertex) : Prop :=
  ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
      (directed : certificate.referenceSwitchingGraph.DirectedEdge),
    path.start = endpoint ∧
      path.finish ∈ owned ∧
      directed ∈ path.traversed ∧
      ActiveCarrierInboundParentEdge certificate component owned directed ∧
      ((directed.target = input.vertex ∧
          state.core.marks[directed.target]? = some none) ∨
        ∃ markedAge,
          directed.target ≠ input.vertex ∧
            state.core.marks[directed.target]? = some (some markedAge) ∧
            tagHistory.RawMarked markedAge directed.target ∧
            state.core.representative markedAge = input.rawAge)

/-- Exact marked alternative once the non-global ready tail is absent and the
external endpoint re-entry avoids the current par conclusion. -/
def ActiveCarrierExternalReentryMarkedHistoricalTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) (endpoint : Vertex) : Prop :=
  ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
      (directed : certificate.referenceSwitchingGraph.DirectedEdge)
      (markedAge : RawTokenAge),
    path.start = endpoint ∧
      path.finish ∈ owned ∧
      directed ∈ path.traversed ∧
      ActiveCarrierInboundParentEdge certificate component owned directed ∧
      directed.target ≠ input.vertex ∧
      state.core.marks[directed.target]? = some (some markedAge) ∧
      tagHistory.RawMarked markedAge directed.target ∧
      state.core.representative markedAge = input.rawAge

private theorem inboundParentEdge_of_boundary
    {certificate : Certificate} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (structural : certificate.StructurallyWellFormed)
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned)
    (directed : certificate.referenceSwitchingGraph.DirectedEdge)
    (sourceOutside : directed.source ∉ owned)
    (targetOwned : directed.target ∈ owned) :
    ActiveCarrierInboundParentEdge certificate component owned directed := by
  rcases directed with ⟨edgeIndex, edge, edgeLookup, forward⟩
  have originLookup := edgeLookup
  rw [UnificationMarking.referenceSwitchingGraph_edges_eq_leftRetained] at originLookup
  rcases Certificate.linkLeftRetainedEdges_lookup_origin originLookup with
    axiomOrigin | tensorOrigin | parOrigin
  · rcases axiomOrigin with ⟨linkIndex, left, right, linkLookup, edgeEq⟩
    subst edge
    cases forward
    · simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target]
        at sourceOutside targetOwned
      exact False.elim
        (sourceOutside
          (occurrence.derivation.sourceLeftRegion_owned structural targetOwned
            (.terminalPartner (.refl left) (.inl linkLookup))))
    · simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target]
        at sourceOutside targetOwned
      exact False.elim
        (sourceOutside
          (occurrence.derivation.sourceLeftRegion_owned structural targetOwned
            (.terminalPartner (.refl right) (.inr linkLookup))))
  · rcases tensorOrigin with
      ⟨linkIndex, left, right, conclusion, linkLookup, leftEdge | rightEdge⟩
    · subst edge
      cases forward
      · simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target]
          at sourceOutside targetOwned
        have targetFrontier : left ∈ component.frontier :=
          Classical.byContradiction fun notFrontier ↦ sourceOutside
            (connectiveConclusion_owned_of_premise_owned_not_frontier
              structural occurrence.derivation (.inl linkLookup) (by simp)
              targetOwned notFrontier)
        exact ⟨linkIndex, .tensor, left, right, conclusion, rfl,
          targetFrontier,
          by
            have notConclusion := submittedPremise_not_conclusion
              (premise := left) structural linkLookup
              (by simp [Link.premises])
            simpa [Graph.DirectedEdge.target] using notConclusion,
          by simpa [SequentialConnectiveKind.asLink] using linkLookup,
          by
            change left ∈ (Link.tensor left right conclusion).premises
            simp [Link.premises],
          sourceOutside⟩
      · simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target]
          at sourceOutside targetOwned
        exact False.elim
          (sourceOutside
            (connectivePremises_owned_of_conclusion_owned structural
              occurrence.derivation targetOwned (.inl linkLookup)).1)
    · subst edge
      cases forward
      · simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target]
          at sourceOutside targetOwned
        have targetFrontier : right ∈ component.frontier :=
          Classical.byContradiction fun notFrontier ↦ sourceOutside
            (connectiveConclusion_owned_of_premise_owned_not_frontier
              structural occurrence.derivation (.inl linkLookup) (by simp)
              targetOwned notFrontier)
        exact ⟨linkIndex, .tensor, left, right, conclusion, rfl,
          targetFrontier,
          by
            have notConclusion := submittedPremise_not_conclusion
              (premise := right) structural linkLookup
              (by simp [Link.premises])
            simpa [Graph.DirectedEdge.target] using notConclusion,
          by simpa [SequentialConnectiveKind.asLink] using linkLookup,
          by
            change right ∈ (Link.tensor left right conclusion).premises
            simp [Link.premises],
          sourceOutside⟩
      · simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target]
          at sourceOutside targetOwned
        exact False.elim
          (sourceOutside
            (connectivePremises_owned_of_conclusion_owned structural
              occurrence.derivation targetOwned (.inl linkLookup)).2)
  · rcases parOrigin with ⟨linkIndex, left, right, conclusion, linkLookup, edgeEq⟩
    subst edge
    cases forward
    · simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target]
        at sourceOutside targetOwned
      have targetFrontier : left ∈ component.frontier :=
        Classical.byContradiction fun notFrontier ↦ sourceOutside
          (connectiveConclusion_owned_of_premise_owned_not_frontier
            structural occurrence.derivation (.inr linkLookup) (by simp)
            targetOwned notFrontier)
      exact ⟨linkIndex, .par, left, right, conclusion, rfl,
        targetFrontier,
        by
          have notConclusion := submittedPremise_not_conclusion
            (premise := left) structural linkLookup
            (by simp [Link.premises])
          simpa [Graph.DirectedEdge.target] using notConclusion,
        by simpa [SequentialConnectiveKind.asLink] using linkLookup,
        by
          change left ∈ (Link.par left right conclusion).premises
          simp [Link.premises],
        sourceOutside⟩
    · simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target]
        at sourceOutside targetOwned
      exact False.elim
        (sourceOutside
          (connectivePremises_owned_of_conclusion_owned structural
            occurrence.derivation targetOwned (.inr linkLookup)).1)

private theorem ReadyHeadInput.readyExactForComponent
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component)) :
    ∀ pending,
      pending ∈ input.vertex :: input.readyTail ↔
        pending ∈ component.frontier ∧
          state.core.marks[pending]? = some none := by
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
      state.stack.sigma[readyPrefix.length]? = some input.rawAge := by
    rw [sigmaEquation, prefixLengths]
    simp
  have readyLookup :
      state.stack.ready[readyPrefix.length]? =
        some (input.vertex :: input.readyTail) := by
    rw [readyEquation]
    simp
  rcases invariant.ready_bucket_frontier_exact sigmaLookup readyLookup with
    ⟨actual, actualLookup, exactMembership⟩
  have actualEq : actual = component :=
    Option.some.inj
      (Option.some.inj (actualLookup.symm.trans componentLookup))
  subst actual
  exact exactMembership

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

/-- Classify the exact active-frontier target of an external endpoint
re-entry as the selected head, a genuine ready-tail occurrence, or a concrete
prior mark. -/
theorem ActiveCarrierExternalEndpointReentry.targetStatus
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned)
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core input.rawAge component owned)
    {endpoint : Vertex}
    (reentry :
      ActiveCarrierExternalEndpointReentry certificate owned endpoint) :
    ActiveCarrierExternalReentryTargetStatus certificate state input component
      owned endpoint := by
  rcases reentry with
    ⟨path, directed, pathStarts, finishOwned, directedMembership,
      sourceOutside, targetOwned⟩
  have parentEdge :=
    inboundParentEdge_of_boundary invariant.structural occurrence directed
      sourceOutside targetOwned
  rcases parentEdge with
    ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
      targetFrontier, targetNotGlobal, linkLookup, targetPremise,
      conclusionOutside⟩
  have targetCarrierOwned : directed.target ∈ owned :=
    occurrence.derivation.frontier_subset_owned directed.target targetFrontier
  have rebuiltParentEdge :
      ActiveCarrierInboundParentEdge certificate component owned directed :=
    ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
      targetFrontier, targetNotGlobal, linkLookup, targetPremise,
      conclusionOutside⟩
  refine ⟨path, directed, pathStarts, finishOwned, directedMembership,
    rebuiltParentEdge, ?_⟩
  rcases accounted directed.target targetCarrierOwned with marked | raw
  · exact Or.inr (Or.inr ⟨marked.choose, marked.choose_spec.1⟩)
  · have readyMembership :
        directed.target ∈ input.vertex :: input.readyTail :=
      (input.readyExactForComponent invariant componentLookup
        directed.target).mpr ⟨targetFrontier, raw.1⟩
    rcases List.mem_cons.mp readyMembership with targetSelected | targetTail
    · exact Or.inl ⟨targetSelected, by simpa [targetSelected] using raw.1⟩
    · exact Or.inr (Or.inl ⟨targetTail, raw.1⟩)

/-- Under explicit failure of the non-global ready-tail obligation, the exact
re-entry target is the selected raw head or a concretely marked active-frontier
premise. -/
theorem ActiveCarrierExternalEndpointReentry.targetFailureStatus
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned)
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core input.rawAge component owned)
    {endpoint : Vertex}
    (reentry :
      ActiveCarrierExternalEndpointReentry certificate owned endpoint)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryFailureTargetStatus certificate state input
      component owned endpoint := by
  rcases reentry.targetStatus input invariant componentLookup occurrence
      accounted with
    ⟨path, directed, pathStarts, finishOwned, directedMembership,
      parentEdge, selected | tail | marked⟩
  · exact ⟨path, directed, pathStarts, finishOwned, directedMembership,
      parentEdge, Or.inl selected⟩
  · rcases parentEdge with
      ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
        targetFrontier, targetNotGlobal, linkLookup, targetPremise,
        conclusionOutside⟩
    exact False.elim
      (noTail ⟨directed.target, tail.1, targetNotGlobal⟩)
  · exact ⟨path, directed, pathStarts, finishOwned, directedMembership,
      parentEdge, Or.inr marked⟩

/-- The selected-or-marked failure classification can be sharpened so that
every marked target is distinct from the selected head, authentic in the
canonical raw-mark history, and represented at the active boundary. -/
theorem ActiveCarrierExternalEndpointReentry.targetFailureHistoricalStatus
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned)
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core input.rawAge component owned)
    {endpoint : Vertex}
    (reentry :
      ActiveCarrierExternalEndpointReentry certificate owned endpoint)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryFailureHistoricalStatus tagHistory input component
      owned endpoint := by
  rcases reentry.targetFailureStatus input invariant componentLookup occurrence
      accounted noTail with
    ⟨path, directed, pathStarts, finishOwned, directedMembership,
      parentEdge, selected | marked⟩
  · exact ⟨path, directed, pathStarts, finishOwned, directedMembership,
      parentEdge, Or.inl selected⟩
  · rcases marked with ⟨markedAge, targetMarked⟩
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
      have selectedUnmarked :
          state.core.marks[input.vertex]? = some none :=
        invariant.queued_vertices_unmarked input.vertex
          (input.futureWorkAt invariant).mem_queued
      have targetNeSelected : directed.target ≠ input.vertex := by
        intro targetEq
        rw [targetEq, selectedUnmarked] at targetMarked
        simp at targetMarked
      have rebuiltParentEdge :
          ActiveCarrierInboundParentEdge certificate component owned directed :=
        ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
          targetFrontier, targetNotGlobal, linkLookup, targetPremise,
          conclusionOutside⟩
      exact ⟨path, directed, pathStarts, finishOwned, directedMembership,
        rebuiltParentEdge, Or.inr ⟨markedAge, targetNeSelected, targetMarked,
          tagHistory.final_rawMarked_iff.mp targetMarked,
          targetRepresentative⟩⟩
    · rw [rawCase.1] at targetMarked
      simp at targetMarked

/-- If the retained re-entry path avoids the current par conclusion, explicit
ready-tail failure leaves only a distinct authentic marked target at the active
representative. This theorem does not derive the path-avoidance premise. -/
theorem ActiveCarrierExternalEndpointReentryAvoiding.markedHistoricalTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    (consumer : ConnectiveBelow certificate input.vertex)
    (parEq : consumer.kind = .par)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned)
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core input.rawAge component owned)
    {endpoint : Vertex}
    (reentry :
      ActiveCarrierExternalEndpointReentryAvoiding certificate owned endpoint
        consumer.conclusion)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryMarkedHistoricalTarget tagHistory input component
      owned endpoint := by
  rcases reentry with
    ⟨path, directed, pathStarts, finishOwned, directedMembership,
      sourceOutside, targetOwned, currentConclusionAvoided⟩
  have parentEdge := inboundParentEdge_of_boundary invariant.structural
    occurrence directed sourceOutside targetOwned
  rcases parentEdge with
    ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
      targetFrontier, targetNotGlobal, linkLookup, targetPremise,
      conclusionOutside⟩
  have targetNeSelected : directed.target ≠ input.vertex := by
    intro targetEq
    have currentPremise : input.vertex ∈ consumer.submittedLink.premises :=
      connectiveSelectedMembership consumer
    have targetPremiseSelected :
        input.vertex ∈ (kind.asLink storedLeft storedRight conclusion).premises := by
      simpa [targetEq] using targetPremise
    have sameLink :
        kind.asLink storedLeft storedRight conclusion = consumer.submittedLink :=
      UnificationState.StructurallyWellFormed.parentLink_unique
        invariant.structural (List.mem_of_getElem? linkLookup) targetPremiseSelected
        (List.mem_of_getElem? consumer.link_eq) currentPremise
    have conclusionEq : conclusion = consumer.conclusion := by
      cases kindEq : kind <;>
        simp [SequentialConnectiveKind.asLink, ConnectiveBelow.submittedLink,
          parEq, kindEq] at sameLink
      exact sameLink.2.2
    have sourceInPath : directed.source ∈ path.vertices :=
      (path.directed_endpoints_mem_vertices directedMembership).1
    apply currentConclusionAvoided
    rw [← conclusionEq, ← sourceEq]
    exact sourceInPath
  rcases accounted directed.target targetOwned with markedCase | rawCase
  · rcases markedCase with
      ⟨markedAge, targetMarked, targetRepresentative⟩
    exact ⟨path, directed, markedAge, pathStarts, finishOwned,
      directedMembership,
      ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
        targetFrontier, targetNotGlobal, linkLookup, targetPremise,
        conclusionOutside⟩,
      targetNeSelected, targetMarked,
      tagHistory.final_rawMarked_iff.mp targetMarked, targetRepresentative⟩
  · have targetReady : directed.target ∈ input.vertex :: input.readyTail :=
      (input.readyExactForComponent invariant componentLookup
        directed.target).mpr ⟨targetFrontier, rawCase.1⟩
    have targetTail : directed.target ∈ input.readyTail :=
      (List.mem_cons.mp targetReady).resolve_left targetNeSelected
    exact False.elim (noTail ⟨directed.target, targetTail, targetNotGlobal⟩)

end SequentialFigure7
end ProofNetIR
