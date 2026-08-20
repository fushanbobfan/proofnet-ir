/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtParentExternalCommitmentReentry

/-!
# Active-top debt external-parent re-entry target

An outside-to-inside reference-switching edge of one occurrence carrier is the
reverse of a submitted connective-parent edge. At an active ready boundary,
its premise target is therefore the selected head, a genuine ready-tail
occurrence, or an already marked active-frontier premise.

This is an exact target classification. It does not eliminate the selected or
marked alternatives, produce `ActiveTopDebtTailLaw`, or prove progress.
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

end SequentialFigure7
end ProofNetIR
