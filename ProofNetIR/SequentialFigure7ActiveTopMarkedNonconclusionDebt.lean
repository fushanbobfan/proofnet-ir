/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopResidual
import ProofNetIR.SequentialComponentSourceLeftGeometry

/-!
# Active-top marked non-conclusion debt

A branch-local debt predicate for closing a drained active scheduler
component. Supporting occurrence geometry and static closure are private.

The results below cover only the listed branches and do not establish a
full canonical-history invariant.

This module intentionally does not claim preservation for nop, wait, or the
global-created forward / unifyPayload branches.
-/

namespace ProofNetIR
namespace Certificate
namespace OccurrenceDerivation

/-- Both premises of a recorded connective belong to its exact owned carrier. -/
private theorem usedConnectivePremises_owned
    {certificate : Certificate}
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned)
    {linkIndex left right conclusion : Nat}
    (membership : linkIndex ∈ usedLinks)
    (submitted :
      certificate.links[linkIndex]? =
          some (.tensor left right conclusion) ∨
        certificate.links[linkIndex]? =
          some (.par left right conclusion)) :
    left ∈ owned ∧ right ∈ owned := by
  induction witness generalizing linkIndex left right conclusion with
  | «axiom» submittedIndex axiomLeft axiomRight name positive
      linkLookup leftFormula =>
      simp only [List.mem_singleton] at membership
      subst linkIndex
      rw [linkLookup] at submitted
      simp at submitted
  | par premiseWitness submittedIndex parLeft parRight parConclusion
      leftFocus rightFocus afterLeft context linkLookup leftPick rightPick
      induction =>
      simp only [List.mem_cons] at membership ⊢
      rcases membership with rfl | oldMembership
      · rcases submitted with tensorLookup | parLookup
        · rw [linkLookup] at tensorLookup
          simp at tensorLookup
        · have linkEquation :
              Link.par parLeft parRight parConclusion =
                .par left right conclusion :=
            Option.some.inj (linkLookup.symm.trans parLookup)
          injection linkEquation with leftEquation rightEquation
              conclusionEquation
          subst left
          subst right
          have leftFrontier : parLeft ∈ _ :=
            (CutFreeDerivation.pick?_perm
              leftPick.positional).mem_iff.mpr (by simp)
          have rightAfterLeft : parRight ∈ afterLeft :=
            (CutFreeDerivation.pick?_perm
              rightPick.positional).mem_iff.mpr (by simp)
          have rightFrontier : parRight ∈ _ :=
            (CutFreeDerivation.pick?_perm
              leftPick.positional).mem_iff.mpr
                (List.mem_cons_of_mem _ rightAfterLeft)
          exact ⟨.inr
            (premiseWitness.frontier_subset_owned parLeft leftFrontier),
            .inr
              (premiseWitness.frontier_subset_owned parRight
                rightFrontier)⟩
      · have oldOwned := induction oldMembership submitted
        exact ⟨.inr oldOwned.1, .inr oldOwned.2⟩
  | tensor leftWitness rightWitness submittedIndex tensorLeft tensorRight
      tensorConclusion leftFocus rightFocus leftContext rightContext
      linkLookup leftPick rightPick leftInduction rightInduction =>
      simp only [List.mem_cons, List.mem_append] at membership ⊢
      rcases membership with rfl | leftMembership | rightMembership
      · rcases submitted with tensorLookup | parLookup
        · have linkEquation :
              Link.tensor tensorLeft tensorRight tensorConclusion =
                .tensor left right conclusion :=
            Option.some.inj (linkLookup.symm.trans tensorLookup)
          injection linkEquation with leftEquation rightEquation
              conclusionEquation
          subst left
          subst right
          have leftFrontier : tensorLeft ∈ _ :=
            (CutFreeDerivation.pick?_perm
              leftPick.positional).mem_iff.mpr (by simp)
          have rightFrontier : tensorRight ∈ _ :=
            (CutFreeDerivation.pick?_perm
              rightPick.positional).mem_iff.mpr (by simp)
          exact ⟨.inr (.inl
            (leftWitness.frontier_subset_owned tensorLeft leftFrontier)),
            .inr (.inr
              (rightWitness.frontier_subset_owned tensorRight
                rightFrontier))⟩
        · rw [linkLookup] at parLookup
          simp at parLookup
      · have oldOwned := leftInduction leftMembership submitted
        exact ⟨.inr (.inl oldOwned.1), .inr (.inl oldOwned.2)⟩
      · have oldOwned := rightInduction rightMembership submitted
        exact ⟨.inr (.inr oldOwned.1), .inr (.inr oldOwned.2)⟩
  | exchange premiseWitness order reordered reorderEquation induction =>
      exact induction membership submitted

/-- Internal structural origin witness for one owned occurrence. -/
private theorem owned_usedSource
    {certificate : Certificate}
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned)
    {vertex : Vertex}
    (membership : vertex ∈ owned) :
    ∃ linkIndex link,
      linkIndex ∈ usedLinks ∧
        certificate.links[linkIndex]? = some link ∧
          (link.containsAxiomEndpoint vertex = true ∨
            link.produces vertex = true) := by
  induction witness with
  | «axiom» linkIndex left right name positive linkLookup leftFormula =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl | rfl
      · exact ⟨linkIndex, .axiom vertex right, by simp, linkLookup,
          .inl (by simp [Link.containsAxiomEndpoint])⟩
      · exact ⟨linkIndex, .axiom left vertex, by simp, linkLookup,
          .inl (by simp [Link.containsAxiomEndpoint])⟩
  | par premiseWitness linkIndex left right conclusion leftFocus
      rightFocus afterLeft context linkLookup leftPick rightPick induction =>
      simp only [List.mem_cons] at membership
      rcases membership with rfl | oldMembership
      · exact ⟨linkIndex, .par left right vertex, by simp, linkLookup,
          .inr (by simp [Link.produces])⟩
      · rcases induction oldMembership with
          ⟨oldIndex, oldLink, oldUsed, oldLookup, oldOrigin⟩
        exact ⟨oldIndex, oldLink, List.mem_cons_of_mem _ oldUsed,
          oldLookup, oldOrigin⟩
  | tensor leftWitness rightWitness linkIndex left right conclusion
      leftFocus rightFocus leftContext rightContext linkLookup
      leftPick rightPick leftInduction rightInduction =>
      simp only [List.mem_cons, List.mem_append] at membership
      rcases membership with rfl | leftMembership | rightMembership
      · exact ⟨linkIndex, .tensor left right vertex, by simp, linkLookup,
          .inr (by simp [Link.produces])⟩
      · rcases leftInduction leftMembership with
          ⟨oldIndex, oldLink, oldUsed, oldLookup, oldOrigin⟩
        exact ⟨oldIndex, oldLink,
          List.mem_cons_of_mem _ (List.mem_append_left _ oldUsed),
          oldLookup, oldOrigin⟩
      · rcases rightInduction rightMembership with
          ⟨oldIndex, oldLink, oldUsed, oldLookup, oldOrigin⟩
        exact ⟨oldIndex, oldLink,
          List.mem_cons_of_mem _ (List.mem_append_right _ oldUsed),
          oldLookup, oldOrigin⟩
  | exchange premiseWitness order reordered reorderEquation induction =>
      exact induction membership

/-- Internal bridge from owned connective conclusions to exact used producer indices. -/
private theorem producer_used_of_conclusion_owned
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned)
    {linkIndex : Nat} {link : Link} {conclusion : Vertex}
    (conclusionOwned : conclusion ∈ owned)
    (exactLink : certificate.links[linkIndex]? = some link)
    (produces : link.produces conclusion = true) :
    linkIndex ∈ usedLinks := by
  rcases owned_usedSource witness conclusionOwned with
    ⟨sourceIndex, sourceLink, sourceUsed, sourceLookup, sourceOrigin⟩
  have sourceMembership : sourceLink ∈ certificate.links :=
    List.mem_of_getElem? sourceLookup
  have sourceProduces : sourceLink.produces conclusion = true := by
    rcases sourceOrigin with sourceAxiom | sourceProduces
    · cases sourceLink with
      | «axiom» sourceLeft sourceRight =>
          have endpointAt :
              conclusion = sourceLeft ∨ conclusion = sourceRight := by
            have reversed :
                sourceLeft = conclusion ∨ sourceRight = conclusion := by
              simpa [Link.containsAxiomEndpoint] using sourceAxiom
            exact reversed.imp Eq.symm Eq.symm
          exact False.elim
            (structural.axiomEndpoint_ne_connectiveConclusion
              sourceMembership endpointAt
              (List.mem_of_getElem? exactLink) produces)
      | tensor sourceLeft sourceRight sourceConclusion =>
          simp [Link.containsAxiomEndpoint] at sourceAxiom
      | «par» sourceLeft sourceRight sourceConclusion =>
          simp [Link.containsAxiomEndpoint] at sourceAxiom
    · exact sourceProduces
  have sameLink : sourceLink = link :=
    UnificationState.StructurallyWellFormed.producerLink_unique
      structural sourceMembership sourceProduces
        (List.mem_of_getElem? exactLink) produces
  have sourceIndexBound : sourceIndex < certificate.links.length :=
    (List.getElem?_eq_some_iff.mp sourceLookup).1
  have sameIndex : sourceIndex = linkIndex := by
    apply (List.getElem?_inj sourceIndexBound structural.links_nodup).mp
    rw [sourceLookup, exactLink, sameLink]
  simpa [sameIndex] using sourceUsed

/-- The premises of any submitted connective whose conclusion is owned stay in the same exact
owned-occurrence carrier. -/
private theorem connectivePremises_owned_of_conclusion_owned
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned)
    {linkIndex left right conclusion : Nat}
    (conclusionOwned : conclusion ∈ owned)
    (submitted :
      certificate.links[linkIndex]? =
          some (.tensor left right conclusion) ∨
        certificate.links[linkIndex]? =
          some (.par left right conclusion)) :
    left ∈ owned ∧ right ∈ owned := by
  have producerUsed : linkIndex ∈ usedLinks := by
    rcases submitted with tensorLookup | parLookup
    · exact producer_used_of_conclusion_owned structural witness
        conclusionOwned tensorLookup (by simp [Link.produces])
    · exact producer_used_of_conclusion_owned structural witness
        conclusionOwned parLookup (by simp [Link.produces])
  exact usedConnectivePremises_owned witness producerUsed submitted


end OccurrenceDerivation
end Certificate
end ProofNetIR

namespace ProofNetIR
namespace Certificate
namespace OccurrenceDerivation

/-- Every owned occurrence removed from the exposed frontier was consumed by
one exact submitted link recorded in the component derivation. -/
private theorem usedConsumer_of_owned_not_frontier
    {certificate : Certificate}
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned)
    {vertex : Vertex}
    (vertexOwned : vertex ∈ owned)
    (notFrontier : vertex ∉ frontier) :
    ∃ linkIndex link,
      linkIndex ∈ usedLinks ∧
        certificate.links[linkIndex]? = some link ∧
          vertex ∈ link.premises := by
  induction witness with
  | «axiom» linkIndex left right name positive linkLookup leftFormula =>
      exact False.elim (notFrontier (by simpa using vertexOwned))
  | @par premise priorFrontier priorUsed priorOwned premiseWitness
      linkIndex left right conclusion leftFocus
      rightFocus afterLeft context linkLookup leftPick rightPick induction =>
      simp only [List.mem_cons] at vertexOwned
      rcases vertexOwned with same | oldOwned
      · subst vertex
        exact False.elim (notFrontier (by simp))
      · by_cases inPriorFrontier : vertex ∈ priorFrontier
        · have inLeftOrAfter : vertex = left ∨ vertex ∈ afterLeft := by
            simpa only [List.mem_cons] using
              (CutFreeDerivation.pick?_perm leftPick.positional).mem_iff.mp
                inPriorFrontier
          rcases inLeftOrAfter with same | inAfterLeft
          · subst vertex
            exact ⟨linkIndex, .par left right conclusion, by simp,
              linkLookup, by simp [Link.premises]⟩
          · have inRightOrContext : vertex = right ∨ vertex ∈ context := by
              simpa only [List.mem_cons] using
                (CutFreeDerivation.pick?_perm rightPick.positional).mem_iff.mp
                  inAfterLeft
            rcases inRightOrContext with same | inContext
            · subst vertex
              exact ⟨linkIndex, .par left right conclusion, by simp,
                linkLookup, by simp [Link.premises]⟩
            · exact False.elim (notFrontier (by simp [inContext]))
        · rcases induction oldOwned inPriorFrontier with
            ⟨oldIndex, oldLink, oldUsed, oldLookup, oldPremise⟩
          exact ⟨oldIndex, oldLink, List.mem_cons_of_mem _ oldUsed,
            oldLookup, oldPremise⟩
  | @tensor leftTree rightTree leftFrontierVertices rightFrontierVertices
      leftUsed rightUsed leftOwnedVertices rightOwnedVertices
      leftWitness rightWitness linkIndex left right conclusion
      leftFocus rightFocus leftContext rightContext linkLookup
      leftPick rightPick leftInduction rightInduction =>
      simp only [List.mem_cons, List.mem_append] at vertexOwned
      rcases vertexOwned with same | leftOwned | rightOwned
      · subst vertex
        exact False.elim (notFrontier (by simp))
      · by_cases leftFrontier : vertex ∈ leftFrontierVertices
        · have inLeftOrContext : vertex = left ∨ vertex ∈ leftContext := by
            simpa only [List.mem_cons] using
              (CutFreeDerivation.pick?_perm leftPick.positional).mem_iff.mp
                leftFrontier
          rcases inLeftOrContext with same | inContext
          · subst vertex
            exact ⟨linkIndex, .tensor left right conclusion, by simp,
              linkLookup, by simp [Link.premises]⟩
          · exact False.elim (notFrontier (by simp [inContext]))
        · rcases leftInduction leftOwned leftFrontier with
            ⟨oldIndex, oldLink, oldUsed, oldLookup, oldPremise⟩
          exact ⟨oldIndex, oldLink,
            List.mem_cons_of_mem _ (List.mem_append_left _ oldUsed),
            oldLookup, oldPremise⟩
      · by_cases rightFrontier : vertex ∈ rightFrontierVertices
        · have inRightOrContext : vertex = right ∨ vertex ∈ rightContext := by
            simpa only [List.mem_cons] using
              (CutFreeDerivation.pick?_perm rightPick.positional).mem_iff.mp
                rightFrontier
          rcases inRightOrContext with same | inContext
          · subst vertex
            exact ⟨linkIndex, .tensor left right conclusion, by simp,
              linkLookup, by simp [Link.premises]⟩
          · exact False.elim (notFrontier (by simp [inContext]))
        · rcases rightInduction rightOwned rightFrontier with
            ⟨oldIndex, oldLink, oldUsed, oldLookup, oldPremise⟩
          exact ⟨oldIndex, oldLink,
            List.mem_cons_of_mem _ (List.mem_append_right _ oldUsed),
            oldLookup, oldPremise⟩
  | @exchange premise priorFrontier priorUsed priorOwned premiseWitness
      order reordered reorderEquation induction =>
      have oldNotFrontier : vertex ∉ priorFrontier := by
        intro oldFrontier
        exact notFrontier
          ((CutFreeDerivation.reorder?_perm reorderEquation).mem_iff.mp
            oldFrontier)
      exact induction vertexOwned oldNotFrontier

/-- If an owned occurrence has left the frontier, its submitted consumer's
conclusion belongs to the same exact owned carrier. -/
private theorem connectiveConclusion_owned_of_premise_owned_not_frontier
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned)
    {linkIndex left right conclusion premise : Nat}
    (submitted :
      certificate.links[linkIndex]? =
          some (.tensor left right conclusion) ∨
        certificate.links[linkIndex]? =
          some (.par left right conclusion))
    (premiseMembership : premise ∈ [left, right])
    (premiseOwned : premise ∈ owned)
    (premiseNotFrontier : premise ∉ frontier) :
    conclusion ∈ owned := by
  rcases witness.usedConsumer_of_owned_not_frontier
      premiseOwned premiseNotFrontier with
    ⟨usedIndex, usedLink, usedMembership, usedLookup, usedPremise⟩
  rcases submitted with tensorLookup | parLookup
  · have sameLink : usedLink = .tensor left right conclusion :=
      UnificationState.StructurallyWellFormed.parentLink_unique structural
        (List.mem_of_getElem? usedLookup) usedPremise
        (List.mem_of_getElem? tensorLookup) (by
          simpa [Link.premises] using premiseMembership)
    subst usedLink
    exact witness.usedConnectiveConclusion_owned usedMembership
      (.inl usedLookup)
  · have sameLink : usedLink = .par left right conclusion :=
      UnificationState.StructurallyWellFormed.parentLink_unique structural
        (List.mem_of_getElem? usedLookup) usedPremise
        (List.mem_of_getElem? parLookup) (by
          simpa [Link.premises] using premiseMembership)
    subst usedLink
    exact witness.usedConnectiveConclusion_owned usedMembership
      (.inr usedLookup)


end OccurrenceDerivation
end Certificate
end ProofNetIR

namespace ProofNetIR

open SequentialUnification

namespace Certificate
namespace OccurrenceDerivation

private theorem submittedPremise_not_conclusion
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {linkIndex : Nat} {link : Link} {premise : Vertex}
    (lookup : certificate.links[linkIndex]? = some link)
    (premiseMembership : premise ∈ link.premises) :
    premise ∉ certificate.conclusions := by
  have wellFormed :=
    structural.2.2.2.2.1 link (List.mem_of_getElem? lookup)
  have premiseBound : premise < certificate.formulas.size := by
    cases link with
    | «axiom» left right => simp [Link.premises] at premiseMembership
    | tensor left right conclusion =>
        simp [Link.premises] at premiseMembership
        rcases premiseMembership with rfl | rfl
        · exact wellFormed.2.2.2.1
        · exact wellFormed.2.2.2.2.1
    | «par» left right conclusion =>
        simp [Link.premises] at premiseMembership
        rcases premiseMembership with rfl | rfl
        · exact wellFormed.2.2.2.1
        · exact wellFormed.2.2.2.2.1
  intro boundary
  have node := structural.2.2.2.2.2 premise premiseBound
  have parentZero : certificate.parentUseCount premise = 0 := by
    simpa [boundary] using node.2
  have filtered :
      link ∈ certificate.links.filter (·.usesAsPremise premise) := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_of_getElem? lookup, by
      simpa [Link.usesAsPremise] using premiseMembership⟩
  have positive : 0 < certificate.parentUseCount premise := by
    unfold Certificate.parentUseCount
    exact List.length_pos_of_mem filtered
  omega

/-- An owned carrier whose exposed frontier consists only of certificate
conclusions is closed under every reference-switching adjacency. -/
private theorem referenceAdjacent_owned_of_frontier_conclusions
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned)
    (frontierConclusions :
      ∀ vertex ∈ frontier, vertex ∈ certificate.conclusions)
    {source target : Vertex}
    (sourceOwned : source ∈ owned)
    (adjacent : certificate.referenceSwitchingGraph.Adjacent source target) :
    target ∈ owned := by
  rcases adjacent with ⟨edge, edgeMembership, direction⟩
  rw [UnificationMarking.referenceSwitchingGraph_edges_eq_leftRetained]
      at edgeMembership
  rcases List.getElem?_of_mem edgeMembership with ⟨edgeIndex, edgeLookup⟩
  rcases Certificate.linkLeftRetainedEdges_lookup_origin edgeLookup with
    axiomOrigin | tensorOrigin | parOrigin
  · rcases axiomOrigin with
      ⟨linkIndex, left, right, linkLookup, edgeEquation⟩
    rcases direction with forward | backward
    · rw [edgeEquation] at forward
      have sourceEquation : source = left := forward.1.symm
      have targetEquation : target = right := forward.2.symm
      subst source
      subst target
      exact witness.sourceLeftRegion_owned structural sourceOwned
        (.terminalPartner (.refl left) (.inl linkLookup))
    · rw [edgeEquation] at backward
      have targetEquation : target = left := backward.1.symm
      have sourceEquation : source = right := backward.2.symm
      subst source
      subst target
      exact witness.sourceLeftRegion_owned structural sourceOwned
        (.terminalPartner (.refl right) (.inr linkLookup))
  · rcases tensorOrigin with
      ⟨linkIndex, left, right, conclusion, linkLookup,
        leftEdge | rightEdge⟩
    · rcases direction with forward | backward
      · rw [leftEdge] at forward
        have sourceEquation : source = left := forward.1.symm
        have targetEquation : target = conclusion := forward.2.symm
        subst source
        subst target
        apply witness.connectiveConclusion_owned_of_premise_owned_not_frontier
            structural (.inl linkLookup) (by simp) sourceOwned
        intro leftFrontier
        exact
          (submittedPremise_not_conclusion structural linkLookup
            (by simp [Link.premises]))
            (frontierConclusions left leftFrontier)
      · rw [leftEdge] at backward
        have targetEquation : target = left := backward.1.symm
        have sourceEquation : source = conclusion := backward.2.symm
        subst source
        subst target
        exact
          (witness.connectivePremises_owned_of_conclusion_owned structural
            sourceOwned (.inl linkLookup)).1
    · rcases direction with forward | backward
      · rw [rightEdge] at forward
        have sourceEquation : source = right := forward.1.symm
        have targetEquation : target = conclusion := forward.2.symm
        subst source
        subst target
        apply witness.connectiveConclusion_owned_of_premise_owned_not_frontier
            structural (.inl linkLookup) (by simp) sourceOwned
        intro rightFrontier
        exact
          (submittedPremise_not_conclusion structural linkLookup
            (by simp [Link.premises]))
            (frontierConclusions right rightFrontier)
      · rw [rightEdge] at backward
        have targetEquation : target = right := backward.1.symm
        have sourceEquation : source = conclusion := backward.2.symm
        subst source
        subst target
        exact
          (witness.connectivePremises_owned_of_conclusion_owned structural
            sourceOwned (.inl linkLookup)).2
  · rcases parOrigin with
      ⟨linkIndex, left, right, conclusion, linkLookup, edgeEquation⟩
    rcases direction with forward | backward
    · rw [edgeEquation] at forward
      have sourceEquation : source = left := forward.1.symm
      have targetEquation : target = conclusion := forward.2.symm
      subst source
      subst target
      apply witness.connectiveConclusion_owned_of_premise_owned_not_frontier
          structural (.inr linkLookup) (by simp) sourceOwned
      intro leftFrontier
      exact
        (submittedPremise_not_conclusion structural linkLookup
          (by simp [Link.premises]))
          (frontierConclusions left leftFrontier)
    · rw [edgeEquation] at backward
      have targetEquation : target = left := backward.1.symm
      have sourceEquation : source = conclusion := backward.2.symm
      subst source
      subst target
      exact
        (witness.connectivePremises_owned_of_conclusion_owned structural
          sourceOwned (.inr linkLookup)).1

/-- In a connected reference switching, a nonempty owned carrier with no
non-conclusion boundary owns every certificate occurrence. -/
private theorem allVertices_owned_of_frontier_conclusions
    {certificate : Certificate}
    (correct : certificate.DeclarativelyCorrect)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned)
    (frontierConclusions :
      ∀ vertex ∈ frontier, vertex ∈ certificate.conclusions)
    {seed : Vertex} (seedOwned : seed ∈ owned) :
    ∀ vertex, vertex < certificate.formulas.size → vertex ∈ owned := by
  intro vertex vertexBound
  have seedBound : seed < certificate.formulas.size :=
    witness.owned_inBounds correct.1 seed seedOwned
  have connected := correct.referenceSwitchingConnected
  have zeroToSeed : certificate.referenceSwitchingGraph.Walk 0 seed :=
    connected.2 seed (by
      simpa [Certificate.referenceSwitchingGraph, Certificate.fullGraph,
        Graph.retainEdges] using seedBound)
  have zeroToVertex : certificate.referenceSwitchingGraph.Walk 0 vertex :=
    connected.2 vertex (by
      simpa [Certificate.referenceSwitchingGraph, Certificate.fullGraph,
        Graph.retainEdges] using vertexBound)
  have seedToVertex := zeroToSeed.symm.trans zeroToVertex
  have walkClosed :
      ∀ {start finish : Vertex},
        certificate.referenceSwitchingGraph.Walk start finish →
          start ∈ owned → finish ∈ owned := by
    intro start finish walk startOwned
    induction walk with
    | refl => exact startOwned
    | step prior adjacency induction =>
        exact witness.referenceAdjacent_owned_of_frontier_conclusions
          correct.1 frontierConclusions induction adjacency
  exact walkClosed seedToVertex seedOwned

/-- Connected carrier closure plus concrete marks on every exposed frontier
forces the entire occurrence array to be marked. -/
private theorem allMarked_of_frontier_conclusions
    {certificate : Certificate}
    (correct : certificate.DeclarativelyCorrect)
    {state : UnificationState} {index : Nat}
    {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (witness :
      ComponentOccurrenceWitness certificate component usedLinks owned)
    (accounted : OwnedOccurrenceAccounted state index component owned)
    (marksSize : state.marks.size = certificate.formulas.size)
    (frontierConclusions :
      ∀ vertex ∈ component.frontier, vertex ∈ certificate.conclusions)
    (frontierMarked :
      ∀ vertex ∈ component.frontier,
        ∃ rawAge, state.marks[vertex]? = some (some rawAge))
    {seed : Vertex} (seedOwned : seed ∈ owned) :
    state.allMarked = true := by
  unfold UnificationState.allMarked
  apply Array.all_eq_true.mpr
  intro vertex vertexBound
  have certificateBound : vertex < certificate.formulas.size := by
    rw [← marksSize]
    exact vertexBound
  have vertexOwned : vertex ∈ owned :=
    witness.derivation.allVertices_owned_of_frontier_conclusions correct
      frontierConclusions seedOwned vertex certificateBound
  rcases accounted vertex vertexOwned with
    ⟨rawAge, marked, representative⟩ | ⟨unmarked, frontier⟩
  · have exactMark : state.marks[vertex] = some rawAge := by
      simpa [Array.getElem?_eq_getElem vertexBound] using marked
    simp [exactMark]
  · rcases frontierMarked vertex frontier with ⟨rawAge, marked⟩
    rw [unmarked] at marked
    simp at marked


end OccurrenceDerivation
end Certificate
end ProofNetIR

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- A marked non-conclusion on the active live frontier is backed by a
raw-unmarked non-conclusion on that same frontier. -/
def ActiveTopMarkedNonconclusionDebt
    (certificate : Certificate) (state : ReservationState) : Prop :=
  ∀ {rawAge markedAge : RawTokenAge}
      {component : UnificationComponent} {markedVertex : Vertex},
    state.stack.sigma.getLast? = some rawAge →
      state.core.components[rawAge]? = some (some component) →
        markedVertex ∈ component.frontier →
          state.core.marks[markedVertex]? = some (some markedAge) →
            markedVertex ∉ certificate.conclusions →
              ∃ pending,
                pending ∈ component.frontier ∧
                  pending ∉ certificate.conclusions ∧
                    state.core.marks[pending]? = some none

/-- The empty scheduler has no active sigma boundary, so the debt is vacuous. -/
theorem empty_activeTopMarkedNonconclusionDebt
    (certificate : Certificate) :
    ActiveTopMarkedNonconclusionDebt certificate
      (ReservationState.empty certificate) := by
  intro rawAge _markedAge _component _markedVertex sigmaTop
    _componentLookup _frontier _marked _notConclusion
  simp [ReservationState.empty, SequentialStackState.empty] at sigmaTop

/-- The exact initial reservation has no concrete raw mark, so the debt holds
vacuously. -/
theorem InitialReservationStep.activeTopMarkedNonconclusionDebt
    {certificate : Certificate} {after : ReservationState} {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    ActiveTopMarkedNonconclusionDebt certificate after := by
  intro rawAge markedAge component markedVertex _sigmaTop _componentLookup
    _markedFrontier marked _notConclusion
  rcases certificate.reserveAxiomAt?_exact step.core_eq with
    ⟨_left, _right, _component, _linkLookup, _ready, _componentLookup,
      _frontier, marksEq, _parents, _components, _started, _fired⟩
  rw [step.output_eq] at marked
  change step.coreAfter.marks[markedVertex]? = some (some markedAge) at marked
  rw [marksEq] at marked
  change (Array.replicate certificate.formulas.size none)[markedVertex]? =
    some (some markedAge) at marked
  rw [Array.getElem?_replicate] at marked
  split at marked <;> simp at marked

/-- A successful `new` installs a fresh active axiom component whose two
frontier endpoints are both raw-unmarked. -/
theorem NewStep.activeTopMarkedNonconclusionDebt
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    ActiveTopMarkedNonconclusionDebt certificate after := by
  intro rawAge markedAge component markedVertex sigmaTop componentLookup
    markedFrontier marked _notConclusion
  have middleInvariant := step.markedMiddle_reservationInvariant
  rcases SequentialStackState.operationalNewEnqueue?_exact
      step.stack_enqueue_eq with
    ⟨_active, _activeTop, _activeLt, _stackMarks, _nextAge,
      sigmaEq, _readyEq, _waitingEq, _activeWaiting, _freshWaiting⟩
  rcases certificate.reserveAxiomAt?_exact step.core_reserve_eq with
    ⟨left, right, freshComponent, _linkLookup, ready, _componentLookup,
      frontierEq, marksEq, _parents, componentsEq, _started, _fired⟩
  have freshIndex :
      step.coreMarked.components.size = step.stackResult.after.nextAge := by
    calc
      step.coreMarked.components.size = step.coreMarked.parents.size :=
        middleInvariant.core_carriers_aligned
      _ = step.stackResult.after.nextAge :=
        middleInvariant.realizesSigma.horizon_eq
  rw [step.output_eq] at sigmaTop componentLookup marked
  have outputTop :
      step.stackAfter.sigma.getLast? =
        some step.stackResult.after.nextAge := by
    rw [sigmaEq]
    simp
  have rawAgeEq : rawAge = step.stackResult.after.nextAge :=
    Option.some.inj (sigmaTop.symm.trans outputTop)
  subst rawAge
  have freshLookup :
      step.coreAfter.components[step.stackResult.after.nextAge]? =
        some (some freshComponent) := by
    rw [componentsEq, ← freshIndex]
    exact Array.getElem?_push_size
  have componentEq : component = freshComponent :=
    Option.some.inj (Option.some.inj
      (componentLookup.symm.trans freshLookup))
  subst component
  rw [frontierEq] at markedFrontier
  simp only [List.mem_cons, List.not_mem_nil, or_false] at markedFrontier
  rw [marksEq] at marked
  rcases markedFrontier with rfl | rfl
  · rw [ready.2.1] at marked
    simp at marked
  · rw [ready.2.2.1] at marked
    simp at marked

/-- Marking and popping a selected global conclusion preserves the active
non-conclusion frontier debt. -/
private theorem PreparedStep.activeTopMarkedNonconclusionDebt_of_selectedConclusion
    {certificate : Certificate} {before : ReservationState}
    (step : PreparedStep before)
    (prior : ActiveTopMarkedNonconclusionDebt certificate before)
    (selectedConclusion :
      step.stackResult.vertex ∈ certificate.conclusions) :
    ActiveTopMarkedNonconclusionDebt certificate step.after := by
  intro rawAge markedAge component markedVertex sigmaTop componentLookup
    markedFrontier marked notConclusion
  rcases SequentialStackState.popReadyMark?_exact step.stack_eq with
    ⟨_beforeReady, _beforeSigma, _selectedUnmarked, _stackMarks,
      _nextAge, sigmaEq, _afterReady, _waiting, _selectedMarked⟩
  rcases UnificationState.markReadyRaw?_exact step.core_mark_eq with
    ⟨selectedUnmarked, marksEq, _parents, componentsEq,
      _started, _fired, _selectedMarked⟩
  have beforeSigmaTop : before.stack.sigma.getLast? = some rawAge := by
    change step.stackResult.after.sigma.getLast? = some rawAge at sigmaTop
    rw [sigmaEq] at sigmaTop
    exact sigmaTop
  have beforeComponentLookup :
      before.core.components[rawAge]? = some (some component) := by
    change step.coreMarked.components[rawAge]? = some (some component)
      at componentLookup
    rw [componentsEq] at componentLookup
    exact componentLookup
  have markedDifferent :
      markedVertex ≠ step.stackResult.vertex := by
    intro same
    apply notConclusion
    simpa [same] using selectedConclusion
  have beforeMarked :
      before.core.marks[markedVertex]? = some (some markedAge) := by
    change step.coreMarked.marks[markedVertex]? = some (some markedAge)
      at marked
    rw [marksEq] at marked
    simpa [Array.getElem?_setIfInBounds, Ne.symm markedDifferent] using marked
  rcases prior beforeSigmaTop beforeComponentLookup markedFrontier
      beforeMarked notConclusion with
    ⟨pending, pendingFrontier, pendingNotConclusion, pendingUnmarked⟩
  have pendingDifferent : pending ≠ step.stackResult.vertex := by
    intro same
    apply pendingNotConclusion
    simpa [same] using selectedConclusion
  refine ⟨pending, pendingFrontier, pendingNotConclusion, ?_⟩
  change step.coreMarked.marks[pending]? = some none
  rw [marksEq]
  simpa [Array.getElem?_setIfInBounds, Ne.symm pendingDifferent] using
    pendingUnmarked

/-- The conclusion branch is the selected-conclusion specialization of the
common-prefix preservation theorem. -/
theorem ConclStep.activeTopMarkedNonconclusionDebt
    {certificate : Certificate} {before after : ReservationState}
    (step : ConclStep certificate before after)
    (prior : ActiveTopMarkedNonconclusionDebt certificate before) :
    ActiveTopMarkedNonconclusionDebt certificate after := by
  rw [step.output_eq]
  exact step.prepared.activeTopMarkedNonconclusionDebt_of_selectedConclusion
    prior step.boundary.boundary

/-- Exact active-frontier interpretation of a ready head. -/
private theorem ReadyHeadInput.activeFrontierUnmarked_forDebt
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state) :
    ∃ component,
      state.core.components[input.rawAge]? = some (some component) ∧
        input.vertex ∈ component.frontier ∧
          state.core.marks[input.vertex]? = some none := by
  rcases input.activeComponent invariant with
    ⟨component, _usedLinks, owned, componentLookup, _witness,
      accounted, headOwned, _activeRoot⟩
  have queued : input.vertex ∈ state.stack.queuedVertices :=
    (input.futureWorkAt invariant).mem_queued
  have unmarked : state.core.marks[input.vertex]? = some none :=
    invariant.queued_vertices_unmarked input.vertex queued
  have frontier : input.vertex ∈ component.frontier := by
    rcases accounted input.vertex headOwned with marked | raw
    · rcases marked with ⟨_rawAge, marked, _representative⟩
      rw [unmarked] at marked
      simp at marked
    · exact raw.2
  exact ⟨component, componentLookup, frontier, unmarked⟩

/-- A raw-unmarked non-conclusion on the active frontier is a common witness
for every active marked non-conclusion. -/
private theorem ReadyHeadInput.activeTopMarkedNonconclusionDebt_of_vertex_not_conclusion
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    (notConclusion : input.vertex ∉ certificate.conclusions) :
    ActiveTopMarkedNonconclusionDebt certificate state := by
  rcases input.activeFrontierUnmarked_forDebt invariant with
    ⟨inputComponent, inputComponentLookup, inputFrontier, inputUnmarked⟩
  intro rawAge _markedAge component _markedVertex sigmaTop componentLookup
    _markedFrontier _marked _markedNotConclusion
  have rawAgeEq : rawAge = input.rawAge :=
    Option.some.inj (sigmaTop.symm.trans input.sigma_top)
  subst rawAge
  have componentEq : component = inputComponent :=
    Option.some.inj
      (Option.some.inj (componentLookup.symm.trans inputComponentLookup))
  subst component
  exact ⟨input.vertex, inputFrontier, notConclusion, inputUnmarked⟩

private theorem ForwardStep.createdReadyHead_forDebt
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) :
    ∃ input : ReadyHeadInput after,
      input.vertex = step.consumer.conclusion := by
  rcases SequentialStackState.prependReadyTop?_exact step.stack_prepend_eq with
    ⟨_readyPrefix, activeReady, _beforeReady, afterReady,
      _marks, _nextAge, afterSigma, _waiting⟩
  rcases SequentialStackState.popReadyMark?_exact step.prepared.stack_eq with
    ⟨_beforeReady, beforeSigma, _unmarked, _marks, _nextAge,
      preparedSigma, _preparedReady, _waiting, _selectedMarked⟩
  have stackEq : after.stack = step.stackAfter :=
    congrArg ReservationState.stack step.output_eq
  refine ⟨{
    vertex := step.consumer.conclusion
    readyTail := activeReady
    rawAge := step.prepared.stackResult.rawAge
    top_ready := by
      rw [stackEq, afterReady]
      simp
    sigma_top := by
      rw [stackEq, afterSigma, preparedSigma]
      exact beforeSigma }, rfl⟩

private theorem UnifyPayloadStep.createdReadyHead_forDebt
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    ∃ input : ReadyHeadInput after,
      input.vertex = step.consumer.conclusion := by
  rcases SequentialStackState.mergeTopReadyWaiting?_exact
      step.stack_merge_eq with
    ⟨_sigmaPrefix, _activeBoundary, _readyPrefix, previousReady,
      activeReady, payload, _beforeSigma, _beforeReady,
      _initialized, afterSigma, afterReady, _waiting, _undefined,
      _marks, _nextAge⟩
  have stackEq : after.stack = step.stackAfter :=
    congrArg ReservationState.stack step.output_eq
  refine ⟨{
    vertex := step.consumer.conclusion
    readyTail := payload ++ previousReady ++ activeReady
    rawAge := step.previousBoundary
    top_ready := by
      rw [stackEq, afterReady]
      simp
    sigma_top := by
      rw [stackEq, afterSigma]
      simp }, rfl⟩

/-- If `forward` creates a non-global conclusion, that new raw ready head
immediately pays every active marked non-conclusion debt. -/
theorem ForwardStep.activeTopMarkedNonconclusionDebt_of_created_not_conclusion
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (notConclusion : step.consumer.conclusion ∉ certificate.conclusions) :
    ActiveTopMarkedNonconclusionDebt certificate after := by
  rcases step.createdReadyHead_forDebt with ⟨input, inputVertex⟩
  apply input.activeTopMarkedNonconclusionDebt_of_vertex_not_conclusion
    (step.schedulerInvariant invariant)
  simpa [inputVertex] using notConclusion

/-- If payload unification creates a non-global tensor conclusion, that new
raw ready head immediately pays every active marked non-conclusion debt. -/
theorem UnifyPayloadStep.activeTopMarkedNonconclusionDebt_of_created_not_conclusion
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (notConclusion : step.consumer.conclusion ∉ certificate.conclusions) :
    ActiveTopMarkedNonconclusionDebt certificate after := by
  rcases step.createdReadyHead_forDebt with ⟨input, inputVertex⟩
  apply input.activeTopMarkedNonconclusionDebt_of_vertex_not_conclusion
    (step.schedulerInvariant invariant)
  simpa [inputVertex] using notConclusion

/-- Draining an in-bounds active provenance frontier forces every frontier
occurrence to carry a concrete raw-age mark. -/
private theorem SchedulerInvariant.activeTopFrontierMarked_of_drained
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    (drained : ActiveTopDrained state) :
    ∃ rawAge component,
      state.stack.sigma.getLast? = some rawAge ∧
        state.core.components[rawAge]? = some (some component) ∧
          ∀ vertex ∈ component.frontier,
            ∃ markedAge,
              state.core.marks[vertex]? = some (some markedAge) := by
  rcases drained with
    ⟨rawAge, component, sigmaTop, componentLookup, frontierDrained⟩
  rcases invariant.component_forest_provenance with
    ⟨_usedAt, ownedAt, live, _disjoint, _markedOwned⟩
  rcases live componentLookup with ⟨witness, _accounted⟩
  refine ⟨rawAge, component, sigmaTop, componentLookup, ?_⟩
  intro vertex frontier
  have owned : vertex ∈ ownedAt rawAge :=
    witness.derivation.frontier_subset_owned vertex frontier
  have certificateBound : vertex < certificate.formulas.size :=
    witness.derivation.owned_inBounds invariant.structural vertex owned
  have marksSize : state.core.marks.size = certificate.formulas.size :=
    invariant.core_abstractable.markArraySize
  have markBound : vertex < state.core.marks.size := by
    rw [marksSize]
    exact certificateBound
  cases marked : state.core.marks[vertex]? with
  | none =>
      rw [Array.getElem?_eq_getElem markBound] at marked
      simp at marked
  | some mark =>
      cases mark with
      | none =>
          exact (frontierDrained vertex frontier marked).elim
      | some markedAge =>
          exact ⟨markedAge, rfl⟩

/-- Debt plus draining rules out every non-global active frontier occurrence. -/
private theorem SchedulerInvariant.activeTopFrontierConclusions_of_drained_of_debt
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    (drained : ActiveTopDrained state)
    (debt : ActiveTopMarkedNonconclusionDebt certificate state) :
    ∃ rawAge component,
      state.stack.sigma.getLast? = some rawAge ∧
        state.core.components[rawAge]? = some (some component) ∧
          (∀ vertex ∈ component.frontier,
            ∃ markedAge,
              state.core.marks[vertex]? = some (some markedAge)) ∧
            ∀ vertex ∈ component.frontier,
              vertex ∈ certificate.conclusions := by
  rcases ProofNetIR.SequentialFigure7.SchedulerInvariant.activeTopFrontierMarked_of_drained
      invariant drained with
    ⟨rawAge, component, sigmaTop, componentLookup, frontierMarked⟩
  refine ⟨rawAge, component, sigmaTop, componentLookup, frontierMarked, ?_⟩
  intro vertex frontier
  by_cases conclusion : vertex ∈ certificate.conclusions
  · exact conclusion
  · rcases frontierMarked vertex frontier with ⟨markedAge, marked⟩
    rcases debt sigmaTop componentLookup frontier marked conclusion with
      ⟨pending, pendingFrontier, _pendingNotConclusion, pendingUnmarked⟩
    rcases drained with
      ⟨drainedAge, drainedComponent, drainedSigmaTop,
        drainedComponentLookup, frontierDrained⟩
    have rawAgeEq : rawAge = drainedAge :=
      Option.some.inj (sigmaTop.symm.trans drainedSigmaTop)
    subst drainedAge
    have componentEq : component = drainedComponent :=
      Option.some.inj
        (Option.some.inj
          (componentLookup.symm.trans drainedComponentLookup))
    subst drainedComponent
    exact (frontierDrained pending pendingFrontier pendingUnmarked).elim

private theorem owned_ne_nil_for_activeTopClosure
    {certificate : Certificate}
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      Certificate.OccurrenceDerivation certificate tree frontier
        usedLinks owned) :
    owned ≠ [] := by
  induction witness <;> simp_all

open ProofNetIR.SequentialFigure7.SchedulerInvariant

/-- Declarative correctness, the scheduler invariant, active draining, and the
history debt force the complete production mark array to be concrete. -/
theorem SchedulerInvariant.allMarked_of_activeTopDrained_of_nonconclusionDebt
    {certificate : Certificate} {state : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (drained : ActiveTopDrained state)
    (debt : ActiveTopMarkedNonconclusionDebt certificate state) :
    state.core.allMarked = true := by
  rcases activeTopFrontierConclusions_of_drained_of_debt
      invariant drained debt with
    ⟨rawAge, component, _sigmaTop, componentLookup,
      frontierMarked, frontierConclusions⟩
  rcases invariant.component_forest_provenance with
    ⟨_usedAt, ownedAt, live, _disjoint, _markedOwned⟩
  rcases live componentLookup with ⟨witness, accounted⟩
  have marksSize :
      state.core.marks.size = certificate.formulas.size :=
    invariant.core_abstractable.markArraySize
  have ownedNonempty :
      ownedAt rawAge ≠ [] :=
    owned_ne_nil_for_activeTopClosure witness.derivation
  cases ownedEq : ownedAt rawAge with
  | nil =>
      exact (ownedNonempty ownedEq).elim
  | cons seed tail =>
      have seedOwned : seed ∈ ownedAt rawAge := by
        rw [ownedEq]
        simp
      exact
        Certificate.OccurrenceDerivation.allMarked_of_frontier_conclusions
          correct witness accounted marksSize frontierConclusions
          frontierMarked seedOwned

end SequentialFigure7
end ProofNetIR
