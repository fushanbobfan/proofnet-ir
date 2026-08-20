/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtQueueTail
import ProofNetIR.SequentialFigure7RawMarkHistory

/-!
# Active-top debt parent escape

For a correct selected `par`, the active ready tail either already contains a
non-global raw occurrence or the selected-to-mate reference path exposes a
marked non-global frontier premise whose submitted parent conclusion lies
outside the active occurrence carrier.

The two outcomes are not asserted to be exclusive. The existing history tail
law does not eliminate this residual, and this module neither requires nor
derives that law.
-/

namespace ProofNetIR
namespace Certificate
namespace OccurrenceDerivation

private theorem usedConnectivePremises_owned
    {certificate : Certificate}
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness : OccurrenceDerivation certificate tree frontier usedLinks owned)
    {linkIndex left right conclusion : Nat}
    (membership : linkIndex ∈ usedLinks)
    (submitted :
      certificate.links[linkIndex]? = some (.tensor left right conclusion) ∨
        certificate.links[linkIndex]? = some (.par left right conclusion)) :
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
          injection linkEquation with leftEquation rightEquation conclusionEquation
          subst left
          subst right
          have leftFrontier : parLeft ∈ _ :=
            (CutFreeDerivation.pick?_perm leftPick.positional).mem_iff.mpr (by simp)
          have rightAfterLeft : parRight ∈ afterLeft :=
            (CutFreeDerivation.pick?_perm rightPick.positional).mem_iff.mpr (by simp)
          have rightFrontier : parRight ∈ _ :=
            (CutFreeDerivation.pick?_perm leftPick.positional).mem_iff.mpr
              (List.mem_cons_of_mem _ rightAfterLeft)
          exact ⟨.inr (premiseWitness.frontier_subset_owned parLeft leftFrontier),
            .inr (premiseWitness.frontier_subset_owned parRight rightFrontier)⟩
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
          injection linkEquation with leftEquation rightEquation conclusionEquation
          subst left
          subst right
          have leftFrontier : tensorLeft ∈ _ :=
            (CutFreeDerivation.pick?_perm leftPick.positional).mem_iff.mpr (by simp)
          have rightFrontier : tensorRight ∈ _ :=
            (CutFreeDerivation.pick?_perm rightPick.positional).mem_iff.mpr (by simp)
          exact ⟨.inr (.inl
              (leftWitness.frontier_subset_owned tensorLeft leftFrontier)),
            .inr (.inr
              (rightWitness.frontier_subset_owned tensorRight rightFrontier))⟩
        · rw [linkLookup] at parLookup
          simp at parLookup
      · have oldOwned := leftInduction leftMembership submitted
        exact ⟨.inr (.inl oldOwned.1), .inr (.inl oldOwned.2)⟩
      · have oldOwned := rightInduction rightMembership submitted
        exact ⟨.inr (.inr oldOwned.1), .inr (.inr oldOwned.2)⟩
  | exchange premiseWitness order reordered reorderEquation induction =>
      exact induction membership submitted

private theorem owned_usedSource
    {certificate : Certificate}
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness : OccurrenceDerivation certificate tree frontier usedLinks owned)
    {vertex : Vertex} (membership : vertex ∈ owned) :
    ∃ linkIndex link,
      linkIndex ∈ usedLinks ∧ certificate.links[linkIndex]? = some link ∧
        (link.containsAxiomEndpoint vertex = true ∨ link.produces vertex = true) := by
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

private theorem producer_used_of_conclusion_owned
    {certificate : Certificate} (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness : OccurrenceDerivation certificate tree frontier usedLinks owned)
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
          have endpointAt : conclusion = sourceLeft ∨ conclusion = sourceRight := by
            have reversed : sourceLeft = conclusion ∨ sourceRight = conclusion := by
              simpa [Link.containsAxiomEndpoint] using sourceAxiom
            exact reversed.imp Eq.symm Eq.symm
          exact False.elim
            (structural.axiomEndpoint_ne_connectiveConclusion
              sourceMembership endpointAt (List.mem_of_getElem? exactLink) produces)
      | tensor sourceLeft sourceRight sourceConclusion =>
          simp [Link.containsAxiomEndpoint] at sourceAxiom
      | «par» sourceLeft sourceRight sourceConclusion =>
          simp [Link.containsAxiomEndpoint] at sourceAxiom
    · exact sourceProduces
  have sameLink : sourceLink = link :=
    UnificationState.StructurallyWellFormed.producerLink_unique structural
      sourceMembership sourceProduces (List.mem_of_getElem? exactLink) produces
  have sourceIndexBound : sourceIndex < certificate.links.length :=
    (List.getElem?_eq_some_iff.mp sourceLookup).1
  have sameIndex : sourceIndex = linkIndex := by
    apply (List.getElem?_inj sourceIndexBound structural.links_nodup).mp
    rw [sourceLookup, exactLink, sameLink]
  simpa [sameIndex] using sourceUsed

/-- If an occurrence carrier owns a submitted connective conclusion, it owns
both premises of that connective. -/
theorem connectivePremises_owned_of_conclusion_owned
    {certificate : Certificate} (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness : OccurrenceDerivation certificate tree frontier usedLinks owned)
    {linkIndex left right conclusion : Nat}
    (conclusionOwned : conclusion ∈ owned)
    (submitted :
      certificate.links[linkIndex]? = some (.tensor left right conclusion) ∨
        certificate.links[linkIndex]? = some (.par left right conclusion)) :
    left ∈ owned ∧ right ∈ owned := by
  have producerUsed : linkIndex ∈ usedLinks := by
    rcases submitted with tensorLookup | parLookup
    · exact producer_used_of_conclusion_owned structural witness
        conclusionOwned tensorLookup (by simp [Link.produces])
    · exact producer_used_of_conclusion_owned structural witness
        conclusionOwned parLookup (by simp [Link.produces])
  exact usedConnectivePremises_owned witness producerUsed submitted

private theorem usedConsumer_of_owned_not_frontier
    {certificate : Certificate}
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness : OccurrenceDerivation certificate tree frontier usedLinks owned)
    {vertex : Vertex} (vertexOwned : vertex ∈ owned)
    (notFrontier : vertex ∉ frontier) :
    ∃ linkIndex link,
      linkIndex ∈ usedLinks ∧ certificate.links[linkIndex]? = some link ∧
        vertex ∈ link.premises := by
  induction witness with
  | «axiom» linkIndex left right name positive linkLookup leftFormula =>
      exact False.elim (notFrontier (by simpa using vertexOwned))
  | @par premise priorFrontier priorUsed priorOwned premiseWitness
      linkIndex left right conclusion leftFocus rightFocus afterLeft context
      linkLookup leftPick rightPick induction =>
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
      leftWitness rightWitness linkIndex left right conclusion leftFocus
      rightFocus leftContext rightContext linkLookup leftPick rightPick
      leftInduction rightInduction =>
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
          ((CutFreeDerivation.reorder?_perm reorderEquation).mem_iff.mp oldFrontier)
      exact induction vertexOwned oldNotFrontier

/-- An owned submitted premise that is internal rather than frontier keeps its
connective conclusion in the same occurrence carrier. -/
theorem connectiveConclusion_owned_of_premise_owned_not_frontier
    {certificate : Certificate} (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness : OccurrenceDerivation certificate tree frontier usedLinks owned)
    {linkIndex left right conclusion premise : Nat}
    (submitted :
      certificate.links[linkIndex]? = some (.tensor left right conclusion) ∨
        certificate.links[linkIndex]? = some (.par left right conclusion))
    (premiseMembership : premise ∈ [left, right])
    (premiseOwned : premise ∈ owned)
    (premiseNotFrontier : premise ∉ frontier) :
    conclusion ∈ owned := by
  rcases usedConsumer_of_owned_not_frontier witness premiseOwned
      premiseNotFrontier with
    ⟨usedIndex, usedLink, usedMembership, usedLookup, usedPremise⟩
  rcases submitted with tensorLookup | parLookup
  · have sameLink : usedLink = .tensor left right conclusion :=
      UnificationState.StructurallyWellFormed.parentLink_unique structural
        (List.mem_of_getElem? usedLookup) usedPremise
        (List.mem_of_getElem? tensorLookup) (by
          simpa [Link.premises] using premiseMembership)
    subst usedLink
    exact witness.usedConnectiveConclusion_owned usedMembership (.inl usedLookup)
  · have sameLink : usedLink = .par left right conclusion :=
      UnificationState.StructurallyWellFormed.parentLink_unique structural
        (List.mem_of_getElem? usedLookup) usedPremise
        (List.mem_of_getElem? parLookup) (by
          simpa [Link.premises] using premiseMembership)
    subst usedLink
    exact witness.usedConnectiveConclusion_owned usedMembership (.inr usedLookup)

end OccurrenceDerivation
end Certificate
end ProofNetIR

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open Certificate.OccurrenceDerivation

/-- A marked non-global frontier premise whose submitted connective parent
leaves the active occurrence carrier. No incompatibility with a valid
ready-tail witness is asserted. -/
def ActiveCarrierParentEscape
    (certificate : Certificate) (state : ReservationState)
    (component : UnificationComponent) (owned : List Vertex)
    (selected : Vertex) : Prop :=
  ∃ (premise : Vertex) (markedAge : RawTokenAge) (linkIndex : Nat)
      (kind : SequentialConnectiveKind) (storedLeft storedRight conclusion : Vertex),
    premise ≠ selected ∧
      premise ∈ component.frontier ∧
      state.core.marks[premise]? = some (some markedAge) ∧
      premise ∉ certificate.conclusions ∧
      certificate.links[linkIndex]? =
        some (kind.asLink storedLeft storedRight conclusion) ∧
      premise ∈ (kind.asLink storedLeft storedRight conclusion).premises ∧
      conclusion ∉ owned

/-- A concrete mark in the carrier escape is an authentic earlier
prepared-selection event in any supplied canonical history for the state.
This provenance statement does not make the escape incompatible with a tail. -/
theorem ActiveCarrierParentEscape.authenticMarkedPremise
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {component : UnificationComponent} {owned : List Vertex}
    {selected : Vertex}
    (escape :
      ActiveCarrierParentEscape certificate state component owned selected) :
    ∃ (premise : Vertex) (markedAge : RawTokenAge) (linkIndex : Nat)
        (kind : SequentialConnectiveKind)
        (storedLeft storedRight conclusion : Vertex),
      premise ≠ selected ∧
        premise ∈ component.frontier ∧
        state.core.marks[premise]? = some (some markedAge) ∧
        tagHistory.RawMarked markedAge premise ∧
        premise ∉ certificate.conclusions ∧
        certificate.links[linkIndex]? =
          some (kind.asLink storedLeft storedRight conclusion) ∧
        premise ∈ (kind.asLink storedLeft storedRight conclusion).premises ∧
        conclusion ∉ owned := by
  rcases escape with
    ⟨premise, markedAge, linkIndex, kind, storedLeft, storedRight,
      conclusion, premiseNeSelected, premiseFrontier, premiseMarked,
      premiseNotGlobal, linkLookup, premiseMembership, conclusionNotOwned⟩
  exact ⟨premise, markedAge, linkIndex, kind, storedLeft, storedRight,
    conclusion, premiseNeSelected, premiseFrontier, premiseMarked,
    tagHistory.final_rawMarked_iff.mp premiseMarked, premiseNotGlobal,
    linkLookup, premiseMembership, conclusionNotOwned⟩

/-- A premise of a structurally well-formed submitted connective is not a
global certificate conclusion. -/
theorem submittedPremise_not_conclusion
    {certificate : Certificate} (structural : certificate.StructurallyWellFormed)
    {linkIndex : Nat} {link : Link} {premise : Vertex}
    (lookup : certificate.links[linkIndex]? = some link)
    (premiseMembership : premise ∈ link.premises) :
    premise ∉ certificate.conclusions := by
  have wellFormed := structural.2.2.2.2.1 link (List.mem_of_getElem? lookup)
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
  have filtered : link ∈ certificate.links.filter (·.usesAsPremise premise) := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_of_getElem? lookup, by
      simpa [Link.usesAsPremise] using premiseMembership⟩
  have positive : 0 < certificate.parentUseCount premise := by
    unfold Certificate.parentUseCount
    exact List.length_pos_of_mem filtered
  omega

private theorem mem_liveFrontierVertices
    {state : ReservationState} {index : Nat}
    {component : UnificationComponent} {vertex : Vertex}
    (componentLookup : state.core.components[index]? = some (some component))
    (frontier : vertex ∈ component.frontier) :
    vertex ∈ state.core.liveFrontierVertices := by
  unfold UnificationState.liveFrontierVertices
  apply List.mem_flatMap.mpr
  refine ⟨some component, ?_, ?_⟩
  · exact List.mem_of_getElem? (by simpa using componentLookup)
  · simpa using frontier

private theorem selectedToMate_referencePath_avoids_conclusion
    {certificate : Certificate} {selected : Vertex}
    (consumer : ConnectiveBelow certificate selected)
    (correct : certificate.DeclarativelyCorrect)
    (parEq : consumer.kind = .par) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = selected ∧ path.finish = consumer.mate ∧
        consumer.conclusion ∉ path.vertices := by
  have parLookup :
      certificate.links[consumer.linkIndex]? =
        some (.par consumer.storedLeft consumer.storedRight consumer.conclusion) := by
    simpa [SequentialConnectiveKind.asLink, parEq] using consumer.link_eq
  rcases correct.parPremises_referencePath_avoids_conclusion
      (List.mem_of_getElem? parLookup) with
    ⟨path, pathStarts, pathFinishes, pathAvoids⟩
  cases sideEq : consumer.side with
  | storedLeft =>
      refine ⟨path, pathStarts.trans ?_, pathFinishes.trans ?_, pathAvoids⟩
      · simpa [TensorPremiseSide.premise, sideEq] using consumer.premise_eq.symm
      · simp [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEq]
  | storedRight =>
      refine ⟨path.reverse, ?_, ?_, ?_⟩
      · change path.finish = selected
        exact pathFinishes.trans (by
          simpa [TensorPremiseSide.premise, sideEq] using consumer.premise_eq.symm)
      · change path.start = consumer.mate
        exact pathStarts.trans (by
          simp [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEq])
      · simpa using pathAvoids

private theorem ReadyHeadInput.consumerConclusion_not_owned
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    (consumer : ConnectiveBelow certificate input.vertex)
    (parEq : consumer.kind = .par)
    {component : UnificationComponent} {owned : List Vertex}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core input.rawAge component owned) :
    consumer.conclusion ∉ owned := by
  have parLookup :
      certificate.links[consumer.linkIndex]? =
        some (.par consumer.storedLeft consumer.storedRight consumer.conclusion) := by
    simpa [SequentialConnectiveKind.asLink, parEq] using consumer.link_eq
  have selectedUnmarked : state.core.marks[input.vertex]? = some none :=
    invariant.queued_vertices_unmarked input.vertex
      (input.futureWorkAt invariant).mem_queued
  have conclusionNotProduced : ¬ Produced state consumer.conclusion := by
    intro produced
    rcases invariant.produced_premises_marked
        (List.mem_of_getElem? parLookup) produced with
      ⟨⟨leftAge, leftMarked⟩, rightAge, rightMarked⟩
    cases sideEq : consumer.side with
    | storedLeft =>
        have selectedEq : input.vertex = consumer.storedLeft := by
          simpa [TensorPremiseSide.premise, sideEq] using consumer.premise_eq
        have leftUnmarked :
            state.core.marks[consumer.storedLeft]? = some none :=
          (congrArg (fun vertex ↦ state.core.marks[vertex]?) selectedEq).symm.trans
            selectedUnmarked
        rw [leftUnmarked] at leftMarked
        simp at leftMarked
    | storedRight =>
        have selectedEq : input.vertex = consumer.storedRight := by
          simpa [TensorPremiseSide.premise, sideEq] using consumer.premise_eq
        have rightUnmarked :
            state.core.marks[consumer.storedRight]? = some none :=
          (congrArg (fun vertex ↦ state.core.marks[vertex]?) selectedEq).symm.trans
            selectedUnmarked
        rw [rightUnmarked] at rightMarked
        simp at rightMarked
  intro conclusionOwned
  apply conclusionNotProduced
  rcases accounted consumer.conclusion conclusionOwned with marked | raw
  · exact .inl ⟨marked.choose, marked.choose_spec.1⟩
  · exact .inr (mem_liveFrontierVertices componentLookup raw.2)

private def ActiveCarrierParentBoundary
    (certificate : Certificate) (component : UnificationComponent)
    (owned : List Vertex) (forbiddenConclusion : Vertex) : Prop :=
  ∃ (premise : Vertex) (linkIndex : Nat) (kind : SequentialConnectiveKind)
      (storedLeft storedRight conclusion : Vertex),
    premise ∈ component.frontier ∧
      premise ∉ certificate.conclusions ∧
      certificate.links[linkIndex]? =
        some (kind.asLink storedLeft storedRight conclusion) ∧
      premise ∈ (kind.asLink storedLeft storedRight conclusion).premises ∧
      conclusion ∉ owned ∧ conclusion ≠ forbiddenConclusion

private theorem activeCarrierParentBoundary_of_directedEscape
    {certificate : Certificate} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (structural : certificate.StructurallyWellFormed)
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned)
    {forbiddenConclusion : Vertex}
    (directed : certificate.referenceSwitchingGraph.DirectedEdge)
    (sourceOwned : directed.source ∈ owned)
    (targetNotOwned : directed.target ∉ owned)
    (targetNeForbidden : directed.target ≠ forbiddenConclusion) :
    ActiveCarrierParentBoundary certificate component owned forbiddenConclusion := by
  rcases directed with ⟨edgeIndex, edge, edgeLookup, forward⟩
  have originLookup := edgeLookup
  rw [UnificationMarking.referenceSwitchingGraph_edges_eq_leftRetained] at originLookup
  rcases Certificate.linkLeftRetainedEdges_lookup_origin originLookup with
    axiomOrigin | tensorOrigin | parOrigin
  · rcases axiomOrigin with ⟨linkIndex, left, right, linkLookup, edgeEq⟩
    cases forward
    · simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target, edgeEq]
        at sourceOwned targetNotOwned targetNeForbidden
      exact False.elim
        (targetNotOwned
          (occurrence.derivation.sourceLeftRegion_owned structural sourceOwned
            (.terminalPartner (.refl right) (.inr linkLookup))))
    · simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target, edgeEq]
        at sourceOwned targetNotOwned targetNeForbidden
      exact False.elim
        (targetNotOwned
          (occurrence.derivation.sourceLeftRegion_owned structural sourceOwned
            (.terminalPartner (.refl left) (.inl linkLookup))))
  · rcases tensorOrigin with
      ⟨linkIndex, left, right, conclusion, linkLookup, leftEdge | rightEdge⟩
    · cases forward
      · simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target, leftEdge]
          at sourceOwned targetNotOwned targetNeForbidden
        exact False.elim
          (targetNotOwned
            (connectivePremises_owned_of_conclusion_owned structural
              occurrence.derivation sourceOwned (.inl linkLookup)).1)
      · simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target, leftEdge]
          at sourceOwned targetNotOwned targetNeForbidden
        have sourceFrontier : left ∈ component.frontier :=
          Classical.byContradiction fun notFrontier ↦ targetNotOwned
            (connectiveConclusion_owned_of_premise_owned_not_frontier
              structural occurrence.derivation (.inl linkLookup) (by simp)
              sourceOwned notFrontier)
        exact ⟨left, linkIndex, .tensor, left, right, conclusion,
          sourceFrontier,
          submittedPremise_not_conclusion structural linkLookup
            (by simp [Link.premises]),
          by simpa [SequentialConnectiveKind.asLink] using linkLookup,
          by simp [SequentialConnectiveKind.asLink, Link.premises],
          targetNotOwned, targetNeForbidden⟩
    · cases forward
      · simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target, rightEdge]
          at sourceOwned targetNotOwned targetNeForbidden
        exact False.elim
          (targetNotOwned
            (connectivePremises_owned_of_conclusion_owned structural
              occurrence.derivation sourceOwned (.inl linkLookup)).2)
      · simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target, rightEdge]
          at sourceOwned targetNotOwned targetNeForbidden
        have sourceFrontier : right ∈ component.frontier :=
          Classical.byContradiction fun notFrontier ↦ targetNotOwned
            (connectiveConclusion_owned_of_premise_owned_not_frontier
              structural occurrence.derivation (.inl linkLookup) (by simp)
              sourceOwned notFrontier)
        exact ⟨right, linkIndex, .tensor, left, right, conclusion,
          sourceFrontier,
          submittedPremise_not_conclusion structural linkLookup
            (by simp [Link.premises]),
          by simpa [SequentialConnectiveKind.asLink] using linkLookup,
          by simp [SequentialConnectiveKind.asLink, Link.premises],
          targetNotOwned, targetNeForbidden⟩
  · rcases parOrigin with ⟨linkIndex, left, right, conclusion, linkLookup, edgeEq⟩
    cases forward
    · simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target, edgeEq]
        at sourceOwned targetNotOwned targetNeForbidden
      exact False.elim
        (targetNotOwned
          (connectivePremises_owned_of_conclusion_owned structural
            occurrence.derivation sourceOwned (.inr linkLookup)).1)
    · simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target, edgeEq]
        at sourceOwned targetNotOwned targetNeForbidden
      have sourceFrontier : left ∈ component.frontier :=
        Classical.byContradiction fun notFrontier ↦ targetNotOwned
          (connectiveConclusion_owned_of_premise_owned_not_frontier
            structural occurrence.derivation (.inr linkLookup) (by simp)
            sourceOwned notFrontier)
      exact ⟨left, linkIndex, .par, left, right, conclusion,
        sourceFrontier,
        submittedPremise_not_conclusion structural linkLookup
          (by simp [Link.premises]),
        by simpa [SequentialConnectiveKind.asLink] using linkLookup,
        by simp [SequentialConnectiveKind.asLink, Link.premises],
        targetNotOwned, targetNeForbidden⟩

private theorem ReadyHeadInput.readyExact
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

private theorem connectiveMateMembership
    {certificate : Certificate} {selected : Vertex}
    (consumer : ConnectiveBelow certificate selected) :
    consumer.mate ∈ consumer.submittedLink.premises := by
  cases kindEq : consumer.kind <;> cases sideEq : consumer.side <;>
    simp [ConnectiveBelow.mate, ConnectiveBelow.submittedLink,
      SequentialConnectiveKind.asLink, Link.premises, TensorPremiseSide.mate,
      kindEq, sideEq]

/-- Kernelized first-boundary reduction for a correct selected par. Either
the active ready bucket already contains another non-global raw occurrence, or
the selected-to-mate path exposes a previously marked non-global frontier
premise whose exact submitted parent conclusion lies outside the active owned
carrier. The two outcomes are not asserted to be exclusive. -/
theorem ReadyHeadInput.readyTail_nonconclusion_or_parentEscape
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (consumer : ConnectiveBelow certificate input.vertex)
    (parEq : consumer.kind = .par) :
    ∃ (component : UnificationComponent) (usedLinks owned : List Nat),
      state.core.components[input.rawAge]? = some (some component) ∧
        Certificate.ComponentOccurrenceWitness certificate component
          usedLinks owned ∧
        Certificate.OwnedOccurrenceAccounted state.core input.rawAge component owned ∧
        ((∃ pending,
            pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) ∨
          ActiveCarrierParentEscape certificate state component owned
            input.vertex) := by
  let selected := input.vertex
  rcases input.activeComponent invariant with
    ⟨component, usedLinks, owned, componentLookup, occurrence,
      accounted, selectedOwned, _activeRoot⟩
  refine ⟨component, usedLinks, owned, componentLookup, occurrence, accounted, ?_⟩
  have exactMembership := input.readyExact invariant componentLookup
  have parLookup :
      certificate.links[consumer.linkIndex]? =
        some (.par consumer.storedLeft consumer.storedRight consumer.conclusion) := by
    simpa [SequentialConnectiveKind.asLink, parEq] using consumer.link_eq
  have conclusionNotOwned : consumer.conclusion ∉ owned :=
    input.consumerConclusion_not_owned invariant consumer parEq
      componentLookup accounted
  have mateNotGlobal : consumer.mate ∉ certificate.conclusions :=
    submittedPremise_not_conclusion invariant.structural parLookup (by
      simpa [ConnectiveBelow.submittedLink, SequentialConnectiveKind.asLink,
        parEq] using connectiveMateMembership consumer)
  have matePremise : consumer.mate ∈
      (Link.par consumer.storedLeft consumer.storedRight
        consumer.conclusion).premises := by
    simpa [ConnectiveBelow.submittedLink, SequentialConnectiveKind.asLink,
      parEq] using connectiveMateMembership consumer
  by_cases mateOwned : consumer.mate ∈ owned
  · have mateFrontier : consumer.mate ∈ component.frontier :=
      Classical.byContradiction fun mateNotFrontier ↦ conclusionNotOwned
        (connectiveConclusion_owned_of_premise_owned_not_frontier
          invariant.structural occurrence.derivation (.inr parLookup)
          matePremise mateOwned mateNotFrontier)
    rcases accounted consumer.mate mateOwned with marked | raw
    · right
      rcases marked with ⟨markedAge, mateMarked, _representative⟩
      exact ⟨consumer.mate, markedAge, consumer.linkIndex, .par,
        consumer.storedLeft, consumer.storedRight, consumer.conclusion,
        consumer.mate_ne, mateFrontier, mateMarked, mateNotGlobal,
        by simpa [SequentialConnectiveKind.asLink] using parLookup,
        by simpa [SequentialConnectiveKind.asLink] using matePremise,
        conclusionNotOwned⟩
    · left
      have mateBucket : consumer.mate ∈ input.vertex :: input.readyTail :=
        (exactMembership consumer.mate).mpr ⟨mateFrontier, raw.1⟩
      have mateTail : consumer.mate ∈ input.readyTail :=
        (List.mem_cons.mp mateBucket).resolve_left consumer.mate_ne
      exact ⟨consumer.mate, mateTail, mateNotGlobal⟩
  · rcases selectedToMate_referencePath_avoids_conclusion
        consumer correct parEq with
      ⟨path, pathStarts, pathFinishes, conclusionAvoided⟩
    have startAccepted : owned.contains path.start = true := by
      simpa [pathStarts] using selectedOwned
    have finishMembership : path.finish ∈ path.vertices := by
      simpa [Graph.EdgeSimplePath.vertices] using
        path.walk.finish_mem_visitedVertices
    have finishRejected : owned.contains path.finish = false := by
      simpa [pathFinishes] using mateOwned
    rcases path.exists_traversed_boundary_of_start_true
        (fun vertex ↦ owned.contains vertex) startAccepted
        ⟨path.finish, finishMembership, finishRejected⟩ with
      ⟨directed, directedMembership, sourceAccepted, targetRejected⟩
    have sourceOwned : directed.source ∈ owned := by
      simpa using sourceAccepted
    have targetNotOwned : directed.target ∉ owned := by
      simpa using targetRejected
    have targetInPath : directed.target ∈ path.vertices :=
      (path.directed_endpoints_mem_vertices directedMembership).2
    have targetNeConclusion : directed.target ≠ consumer.conclusion := by
      intro same
      exact conclusionAvoided (same ▸ targetInPath)
    rcases activeCarrierParentBoundary_of_directedEscape
        invariant.structural occurrence directed sourceOwned targetNotOwned
        targetNeConclusion with
      ⟨premise, linkIndex, kind, storedLeft, storedRight, conclusion,
        premiseFrontier, premiseNotGlobal, linkLookup, premiseMembership,
        escapedConclusion, conclusionNeCurrent⟩
    have premiseOwned : premise ∈ owned :=
      occurrence.derivation.frontier_subset_owned premise premiseFrontier
    have premiseNeSelected : premise ≠ input.vertex := by
      intro same
      subst premise
      have currentPremise : input.vertex ∈
          (Link.par consumer.storedLeft consumer.storedRight
            consumer.conclusion).premises := by
        simpa [ConnectiveBelow.submittedLink, SequentialConnectiveKind.asLink,
          parEq] using connectiveSelectedMembership consumer
      have sameLink :
          kind.asLink storedLeft storedRight conclusion =
            .par consumer.storedLeft consumer.storedRight consumer.conclusion :=
        UnificationState.StructurallyWellFormed.parentLink_unique
          invariant.structural (List.mem_of_getElem? linkLookup)
          premiseMembership (List.mem_of_getElem? parLookup) currentPremise
      cases kindEq : kind with
      | par =>
          have conclusionEq : conclusion = consumer.conclusion := by
            have optionEq := congrArg
              (fun link ↦ match link with
                | .par _ _ value => some value
                | _ => none)
              sameLink
            exact Option.some.inj (by
              simpa [SequentialConnectiveKind.asLink, kindEq] using optionEq)
          exact conclusionNeCurrent conclusionEq
      | tensor =>
          simp [SequentialConnectiveKind.asLink, kindEq] at sameLink
    rcases accounted premise premiseOwned with marked | raw
    · right
      rcases marked with ⟨markedAge, premiseMarked, _representative⟩
      exact ⟨premise, markedAge, linkIndex, kind, storedLeft, storedRight,
        conclusion, premiseNeSelected, premiseFrontier, premiseMarked,
        premiseNotGlobal, linkLookup, premiseMembership, escapedConclusion⟩
    · left
      have premiseBucket : premise ∈ input.vertex :: input.readyTail :=
        (exactMembership premise).mpr ⟨premiseFrontier, raw.1⟩
      have premiseTail : premise ∈ input.readyTail :=
        (List.mem_cons.mp premiseBucket).resolve_left premiseNeSelected
      exact ⟨premise, premiseTail, premiseNotGlobal⟩

/-- Failure-conditioned form of the exact reduction. If the requested
non-global ready tail is absent, correctness and the scheduler invariant force
an exact marked-parent carrier escape. This theorem neither assumes a history
tail law nor concludes that the escape is impossible. -/
theorem ReadyHeadInput.parentEscape_of_no_readyTail
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (consumer : ConnectiveBelow certificate input.vertex)
    (parEq : consumer.kind = .par)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ∃ (component : UnificationComponent) (usedLinks owned : List Nat),
      state.core.components[input.rawAge]? = some (some component) ∧
        Certificate.ComponentOccurrenceWitness certificate component
          usedLinks owned ∧
        Certificate.OwnedOccurrenceAccounted state.core input.rawAge component owned ∧
        ActiveCarrierParentEscape certificate state component owned
          input.vertex := by
  rcases input.readyTail_nonconclusion_or_parentEscape
      correct invariant consumer parEq with
    ⟨component, usedLinks, owned, componentLookup, occurrence,
      accounted, tail | escape⟩
  · exact False.elim (noTail tail)
  · exact ⟨component, usedLinks, owned, componentLookup, occurrence,
      accounted, escape⟩

end SequentialFigure7
end ProofNetIR
