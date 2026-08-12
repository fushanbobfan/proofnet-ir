/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFreshSourceBlocker

/-!
# Source-left geometry inside an occurrence derivation

A source-left walk that begins in the owned occurrence carrier of a concrete
derivation stays inside that carrier. The terminal axiom partner is included
as part of the same closed region.

This is a structural ownership result only. It does not identify a scheduler
component, establish chronological separation, or prove progress.
-/

namespace ProofNetIR

open SequentialUnification

namespace Certificate
namespace OccurrenceDerivation

private theorem sourceLeftStep_owned
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned)
    {source next : Vertex}
    (sourceOwned : source ∈ owned)
    (step : SourceLeftStep certificate source next) :
    next ∈ owned := by
  induction witness with
  | «axiom» linkIndex left right name positive linkLookup leftFormula =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at sourceOwned
      rcases sourceOwned with rfl | rfl
      · cases step with
        | tensor exactConnective =>
            exact False.elim (structural.axiomEndpoint_ne_connectiveConclusion
              (List.mem_of_getElem? linkLookup) (Or.inl rfl)
              (List.mem_of_getElem? exactConnective) (by simp [Link.produces]))
        | «par» exactConnective =>
            exact False.elim (structural.axiomEndpoint_ne_connectiveConclusion
              (List.mem_of_getElem? linkLookup) (Or.inl rfl)
              (List.mem_of_getElem? exactConnective) (by simp [Link.produces]))
      · cases step with
        | tensor exactConnective =>
            exact False.elim (structural.axiomEndpoint_ne_connectiveConclusion
              (List.mem_of_getElem? linkLookup) (Or.inr rfl)
              (List.mem_of_getElem? exactConnective) (by simp [Link.produces]))
        | «par» exactConnective =>
            exact False.elim (structural.axiomEndpoint_ne_connectiveConclusion
              (List.mem_of_getElem? linkLookup) (Or.inr rfl)
              (List.mem_of_getElem? exactConnective) (by simp [Link.produces]))
  | @par premise frontier usedLinks owned premiseWitness
      linkIndex left right conclusion leftFocus rightFocus afterLeft context
      linkLookup leftPick rightPick induction =>
      simp only [List.mem_cons] at sourceOwned ⊢
      rcases sourceOwned with rfl | oldOwned
      · cases step with
        | @tensor otherIndex otherLeft otherRight _ exactOther =>
            have same :
                Link.par left right source =
                  Link.tensor next otherRight source :=
              UnificationState.StructurallyWellFormed.producerLink_unique
                (conclusion := source) structural
                (List.mem_of_getElem? linkLookup) (by simp [Link.produces])
                (List.mem_of_getElem? exactOther) (by simp [Link.produces])
            contradiction
        | @par otherIndex otherLeft otherRight _ exactOther =>
            have same :
                Link.par left right source =
                  Link.par next otherRight source :=
              UnificationState.StructurallyWellFormed.producerLink_unique
                (conclusion := source) structural
                (List.mem_of_getElem? linkLookup) (by simp [Link.produces])
                (List.mem_of_getElem? exactOther) (by simp [Link.produces])
            have leftEq : left = next := Link.par.inj same |>.1
            right
            have leftFrontier : left ∈ frontier :=
              (CutFreeDerivation.pick?_perm leftPick.positional).mem_iff.mpr
                (by simp)
            simpa [leftEq] using
              premiseWitness.frontier_subset_owned left leftFrontier
      · exact Or.inr (induction oldOwned)
  | @tensor leftTree rightTree leftFrontier rightFrontier
      leftUsed rightUsed leftOwned rightOwned leftWitness rightWitness
      linkIndex left right conclusion leftFocus rightFocus
      leftContext rightContext linkLookup leftPick rightPick
      leftInduction rightInduction =>
      simp only [List.mem_cons, List.mem_append] at sourceOwned ⊢
      rcases sourceOwned with rfl | inLeft | inRight
      · cases step with
        | @tensor otherIndex otherLeft otherRight _ exactOther =>
            have same :
                Link.tensor left right source =
                  Link.tensor next otherRight source :=
              UnificationState.StructurallyWellFormed.producerLink_unique
                (conclusion := source) structural
                (List.mem_of_getElem? linkLookup) (by simp [Link.produces])
                (List.mem_of_getElem? exactOther) (by simp [Link.produces])
            have leftEq : left = next := Link.tensor.inj same |>.1
            right
            left
            have leftFrontierMem : left ∈ leftFrontier :=
              (CutFreeDerivation.pick?_perm leftPick.positional).mem_iff.mpr
                (by simp)
            simpa [leftEq] using
              leftWitness.frontier_subset_owned left leftFrontierMem
        | @par otherIndex otherLeft otherRight _ exactOther =>
            have same :
                Link.tensor left right source =
                  Link.par next otherRight source :=
              UnificationState.StructurallyWellFormed.producerLink_unique
                (conclusion := source) structural
                (List.mem_of_getElem? linkLookup) (by simp [Link.produces])
                (List.mem_of_getElem? exactOther) (by simp [Link.produces])
            contradiction
      · exact Or.inr (Or.inl (leftInduction inLeft))
      · exact Or.inr (Or.inr (rightInduction inRight))
  | @exchange premise frontier usedLinks owned premiseWitness
      order reordered reorderEquation induction =>
      exact induction sourceOwned

private theorem axiom_eq_of_shared_endpoint
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {firstLeft firstRight secondLeft secondRight endpoint : Vertex}
    (firstMembership :
      Link.axiom firstLeft firstRight ∈ certificate.links)
    (firstEndpoint : endpoint = firstLeft ∨ endpoint = firstRight)
    (secondMembership :
      Link.axiom secondLeft secondRight ∈ certificate.links)
    (secondEndpoint : endpoint = secondLeft ∨ endpoint = secondRight) :
    Link.axiom firstLeft firstRight =
      Link.axiom secondLeft secondRight := by
  have firstWellFormed := structural.2.2.2.2.1 _ firstMembership
  rcases firstWellFormed.axiom_endpointFormula firstEndpoint with
    ⟨name, positive, formulaLookup⟩
  have endpointBound : endpoint < certificate.formulas.size := by
    rcases firstEndpoint with rfl | rfl
    · exact firstWellFormed.2.1
    · exact firstWellFormed.2.2.1
  have node := structural.2.2.2.2.2 endpoint endpointBound
  have count : certificate.axiomCount endpoint = 1 := by
    simpa [Certificate.NodeWellFormed, formulaLookup] using node.1
  unfold Certificate.axiomCount at count
  have firstFiltered :
      Link.axiom firstLeft firstRight ∈
        certificate.links.filter (·.containsAxiomEndpoint endpoint) := by
    apply List.mem_filter.mpr
    refine ⟨firstMembership, ?_⟩
    rcases firstEndpoint with rfl | rfl <;>
      simp [Link.containsAxiomEndpoint]
  have secondFiltered :
      Link.axiom secondLeft secondRight ∈
        certificate.links.filter (·.containsAxiomEndpoint endpoint) := by
    apply List.mem_filter.mpr
    refine ⟨secondMembership, ?_⟩
    rcases secondEndpoint with rfl | rfl <;>
      simp [Link.containsAxiomEndpoint]
  rcases List.length_eq_one_iff.mp count with ⟨only, filterEquation⟩
  rw [filterEquation] at firstFiltered secondFiltered
  simp at firstFiltered secondFiltered
  exact firstFiltered.trans secondFiltered.symm

private theorem axiomPartner_owned
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned)
    {reached partner : Vertex} {axiomIndex : Nat}
    (reachedOwned : reached ∈ owned)
    (exactAxiom :
      certificate.links[axiomIndex]? = some (.axiom reached partner) ∨
        certificate.links[axiomIndex]? = some (.axiom partner reached)) :
    partner ∈ owned := by
  induction witness with
  | «axiom» linkIndex left right name positive linkLookup leftFormula =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at reachedOwned ⊢
      rcases reachedOwned with rfl | rfl
      · rcases exactAxiom with storedForward | storedBackward
        · have same := axiom_eq_of_shared_endpoint structural
            (List.mem_of_getElem? linkLookup) (Or.inl rfl)
            (List.mem_of_getElem? storedForward) (Or.inl rfl)
          injection same with firstEq secondEq
          simp_all
        · have same := axiom_eq_of_shared_endpoint structural
            (List.mem_of_getElem? linkLookup) (Or.inl rfl)
            (List.mem_of_getElem? storedBackward) (Or.inr rfl)
          injection same with firstEq secondEq
          simp_all
      · rcases exactAxiom with storedForward | storedBackward
        · have same := axiom_eq_of_shared_endpoint structural
            (List.mem_of_getElem? linkLookup) (Or.inr rfl)
            (List.mem_of_getElem? storedForward) (Or.inl rfl)
          injection same with firstEq secondEq
          simp_all
        · have same := axiom_eq_of_shared_endpoint structural
            (List.mem_of_getElem? linkLookup) (Or.inr rfl)
            (List.mem_of_getElem? storedBackward) (Or.inr rfl)
          injection same with firstEq secondEq
          simp_all
  | @par premise frontier usedLinks owned premiseWitness
      linkIndex left right conclusion leftFocus rightFocus afterLeft context
      linkLookup leftPick rightPick induction =>
      simp only [List.mem_cons] at reachedOwned ⊢
      rcases reachedOwned with rfl | oldOwned
      · rcases exactAxiom with storedForward | storedBackward
        · exact False.elim
            (structural.axiomEndpoint_ne_connectiveConclusion
              (List.mem_of_getElem? storedForward) (Or.inl rfl)
              (List.mem_of_getElem? linkLookup) (by simp [Link.produces]))
        · exact False.elim
            (structural.axiomEndpoint_ne_connectiveConclusion
              (List.mem_of_getElem? storedBackward) (Or.inr rfl)
              (List.mem_of_getElem? linkLookup) (by simp [Link.produces]))
      · exact Or.inr (induction oldOwned)
  | @tensor leftTree rightTree leftFrontier rightFrontier
      leftUsed rightUsed leftOwned rightOwned leftWitness rightWitness
      linkIndex left right conclusion leftFocus rightFocus
      leftContext rightContext linkLookup leftPick rightPick
      leftInduction rightInduction =>
      simp only [List.mem_cons, List.mem_append] at reachedOwned ⊢
      rcases reachedOwned with rfl | inLeft | inRight
      · rcases exactAxiom with storedForward | storedBackward
        · exact False.elim
            (structural.axiomEndpoint_ne_connectiveConclusion
              (List.mem_of_getElem? storedForward) (Or.inl rfl)
              (List.mem_of_getElem? linkLookup) (by simp [Link.produces]))
        · exact False.elim
            (structural.axiomEndpoint_ne_connectiveConclusion
              (List.mem_of_getElem? storedBackward) (Or.inr rfl)
              (List.mem_of_getElem? linkLookup) (by simp [Link.produces]))
      · exact Or.inr (Or.inl (leftInduction inLeft))
      · exact Or.inr (Or.inr (rightInduction inRight))
  | @exchange premise frontier usedLinks owned premiseWitness
      order reordered reorderEquation induction =>
      exact induction reachedOwned

private theorem sourceLeftReachable_owned
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned)
    {source target : Vertex}
    (sourceOwned : source ∈ owned)
    (reachable : SourceLeftReachable certificate source target) :
    target ∈ owned := by
  induction reachable with
  | refl => exact sourceOwned
  | step head tail induction =>
      exact induction
        (witness.sourceLeftStep_owned structural sourceOwned head)

/-- Every vertex in the source-left region of an owned occurrence remains in
the same occurrence-derivation carrier. -/
theorem sourceLeftRegion_owned
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned)
    {source vertex : Vertex}
    (sourceOwned : source ∈ owned)
    (region : SourceLeftRegionVertex certificate source vertex) :
    vertex ∈ owned := by
  cases region with
  | visited reachable =>
      exact witness.sourceLeftReachable_owned structural
        sourceOwned reachable
  | terminalPartner reachable exactAxiom =>
      have reachedOwned :=
        witness.sourceLeftReachable_owned structural
          sourceOwned reachable
      exact witness.axiomPartner_owned structural
        reachedOwned exactAxiom

end OccurrenceDerivation
end Certificate
end ProofNetIR
