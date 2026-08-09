import ProofNetIR.SequentialFigure7ReservationLedger

/-!
# Figure-7 reservation-event touch completeness

This module proves structural reverse completeness for source-left regions of exact fresh runs,
then lifts it to already successful initial and `new` reservation events.  It does not prove that
another executor call succeeds, scheduler progress, totality, or worklist completeness.
-/

namespace ProofNetIR.SequentialUnification

private theorem slStepNextUnique
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {source firstNext secondNext : Vertex}
    (first : SourceLeftStep certificate source firstNext)
    (second : SourceLeftStep certificate source secondNext) :
    firstNext = secondNext := by
  cases first with
  | @tensor _ _ firstRight _ firstLink =>
      cases second with
      | @tensor _ _ secondRight _ secondLink =>
          have linkEq :=
            _root_.ProofNetIR.UnificationState.StructurallyWellFormed.producerLink_unique
              (conclusion := source)
              (first := .tensor firstNext firstRight source)
              (second := .tensor secondNext secondRight source)
              structural
              (List.mem_of_getElem? firstLink) (by simp [Link.produces])
              (List.mem_of_getElem? secondLink) (by simp [Link.produces])
          exact Link.tensor.inj linkEq |>.1
      | @par _ _ secondRight _ secondLink =>
          have linkEq :=
            _root_.ProofNetIR.UnificationState.StructurallyWellFormed.producerLink_unique
              (conclusion := source)
              (first := .tensor firstNext firstRight source)
              (second := .par secondNext secondRight source)
              structural
              (List.mem_of_getElem? firstLink) (by simp [Link.produces])
              (List.mem_of_getElem? secondLink) (by simp [Link.produces])
          contradiction
  | @par _ _ firstRight _ firstLink =>
      cases second with
      | @tensor _ _ secondRight _ secondLink =>
          have linkEq :=
            _root_.ProofNetIR.UnificationState.StructurallyWellFormed.producerLink_unique
              (conclusion := source)
              (first := .par firstNext firstRight source)
              (second := .tensor secondNext secondRight source)
              structural
              (List.mem_of_getElem? firstLink) (by simp [Link.produces])
              (List.mem_of_getElem? secondLink) (by simp [Link.produces])
          contradiction
      | @par _ _ secondRight _ secondLink =>
          have linkEq :=
            _root_.ProofNetIR.UnificationState.StructurallyWellFormed.producerLink_unique
              (conclusion := source)
              (first := .par firstNext firstRight source)
              (second := .par secondNext secondRight source)
              structural
              (List.mem_of_getElem? firstLink) (by simp [Link.produces])
              (List.mem_of_getElem? secondLink) (by simp [Link.produces])
          exact Link.par.inj linkEq |>.1

private theorem connectiveConclusionNeAxiomEndpoint
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {producerIndex axiomIndex : Nat} {link : Link}
    {left right conclusion endpoint : Vertex}
    (exactConnective : certificate.links[producerIndex]? = some link)
    (produces : link.produces conclusion = true)
    (connective : link.isConnective = true)
    (exactAxiom :
      certificate.links[axiomIndex]? = some (.axiom left right))
    (endpointAt : endpoint = left ∨ endpoint = right) :
    conclusion ≠ endpoint := by
  intro same
  subst endpoint
  have connectiveWellFormed :=
    structural.2.2.2.2.1 _ (List.mem_of_getElem? exactConnective)
  have axiomWellFormed :=
    structural.2.2.2.2.1 _ (List.mem_of_getElem? exactAxiom)
  rcases axiomWellFormed.axiom_endpointFormula endpointAt with
    ⟨name, positive, atomLookup⟩
  cases link with
  | «axiom» a b => simp [Link.isConnective] at connective
  | tensor a b actualConclusion =>
      simp [Link.produces] at produces
      subst actualConclusion
      rcases connectiveWellFormed.tensor_conclusionFormula with
        ⟨leftFormula, rightFormula, tensorLookup⟩
      rw [atomLookup] at tensorLookup
      simp at tensorLookup
  | «par» a b actualConclusion =>
      simp [Link.produces] at produces
      subst actualConclusion
      rcases connectiveWellFormed.par_conclusionFormula with
        ⟨leftFormula, rightFormula, parLookup⟩
      rw [atomLookup] at parLookup
      simp at parLookup

private theorem slStepSourceNeAxiomEndpoint
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {source next left right endpoint : Vertex} {linkIndex : Nat}
    (step : SourceLeftStep certificate source next)
    (exactAxiom :
      certificate.links[linkIndex]? = some (.axiom left right))
    (endpointAt : endpoint = left ∨ endpoint = right) :
    source ≠ endpoint := by
  cases step with
  | tensor exactConnective =>
      exact connectiveConclusionNeAxiomEndpoint structural exactConnective
        (by simp [Link.produces]) (by simp [Link.isConnective])
        exactAxiom endpointAt
  | par exactConnective =>
      exact connectiveConclusionNeAxiomEndpoint structural exactConnective
        (by simp [Link.produces]) (by simp [Link.isConnective])
        exactAxiom endpointAt

private theorem axiomEqOfSharedEndpoint
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

set_option maxHeartbeats 800000 in
/-- Structural reverse completeness for one exact fresh source-left run.
Every vertex in the complete source-left region is either in the recursive
trace or is the returned partner endpoint.  The reached endpoint is already
in the trace by `run.traceLast`.  This is local to the supplied run and does
not establish scheduler progress, totality, or worklist completeness. -/
theorem FreshSourceLeftRun.sourceLeftRegion_touched
    {certificate : Certificate} {state : UnificationState}
    {fuel : Nat} {tags : Array Bool}
    {start reached partner vertex : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (structural : certificate.StructurallyWellFormed)
    (run : FreshSourceLeftRun certificate state fuel tags start trace
      reached partner linkIndex)
    (region : SourceLeftRegionVertex certificate start vertex) :
    vertex ∈ trace ∨ vertex = partner := by
  induction run with
  | @axiomLeft fuel tags linkIndex left right source sourceLookup
      sourceLinkIndex sourceLink exactLink different leftFresh rightFresh
      leftReady rightReady =>
      cases region with
      | visited reachable =>
          cases reachable with
          | refl => simp
          | step head tail =>
              exact False.elim
                ((slStepSourceNeAxiomEndpoint structural head exactLink
                  (Or.inl rfl)) rfl)
      | @terminalPartner terminalReached terminalPartner terminalIndex
          reachable terminalAxiom =>
          cases reachable with
          | refl =>
              rcases terminalAxiom with terminalAxiom | terminalAxiom
              · have linkEq := axiomEqOfSharedEndpoint structural
                  (List.mem_of_getElem? exactLink) (Or.inl rfl)
                  (List.mem_of_getElem? terminalAxiom) (Or.inl rfl)
                have partnerEq : vertex = right :=
                  (Link.axiom.inj linkEq).2.symm
                exact Or.inr partnerEq
              · have linkEq := axiomEqOfSharedEndpoint structural
                  (List.mem_of_getElem? exactLink) (Or.inl rfl)
                  (List.mem_of_getElem? terminalAxiom) (Or.inr rfl)
                have impossible : left = right :=
                  (Link.axiom.inj linkEq).2.symm
                exact False.elim (different impossible)
          | step head tail =>
              exact False.elim
                ((slStepSourceNeAxiomEndpoint structural head exactLink
                  (Or.inl rfl)) rfl)
  | @axiomRight fuel tags linkIndex left right source sourceLookup
      sourceLinkIndex sourceLink exactLink different leftFresh rightFresh
      leftReady rightReady =>
      cases region with
      | visited reachable =>
          cases reachable with
          | refl => simp
          | step head tail =>
              exact False.elim
                ((slStepSourceNeAxiomEndpoint structural head exactLink
                  (Or.inr rfl)) rfl)
      | @terminalPartner terminalReached terminalPartner terminalIndex
          reachable terminalAxiom =>
          cases reachable with
          | refl =>
              rcases terminalAxiom with terminalAxiom | terminalAxiom
              · have linkEq := axiomEqOfSharedEndpoint structural
                  (List.mem_of_getElem? exactLink) (Or.inr rfl)
                  (List.mem_of_getElem? terminalAxiom) (Or.inl rfl)
                have impossible : left = right :=
                  (Link.axiom.inj linkEq).1
                exact False.elim (different impossible)
              · have linkEq := axiomEqOfSharedEndpoint structural
                  (List.mem_of_getElem? exactLink) (Or.inr rfl)
                  (List.mem_of_getElem? terminalAxiom) (Or.inr rfl)
                have partnerEq : vertex = left :=
                  (Link.axiom.inj linkEq).1.symm
                exact Or.inr partnerEq
          | step head tail =>
              exact False.elim
                ((slStepSourceNeAxiomEndpoint structural head exactLink
                  (Or.inr rfl)) rfl)
  | @tensor fuel tags producerIndex linkIndex left right conclusion reached
      partner trace source sourceLookup sourceLinkIndex sourceLink exactLink
      currentFresh currentReady tail induction =>
      cases region with
      | visited reachable =>
          cases reachable with
          | refl => exact Or.inl (by simp)
          | step head remaining =>
              have nextEq : _ = left :=
                slStepNextUnique structural head (.tensor exactLink)
              subst_vars
              rcases induction (.visited remaining) with inTrace | endpoint
              · exact Or.inl (by simp [inTrace])
              · exact Or.inr endpoint
      | @terminalPartner terminalReached terminalPartner terminalIndex
          reachable terminalAxiom =>
          cases reachable with
          | refl =>
              rcases terminalAxiom with terminalAxiom | terminalAxiom
              · exact False.elim
                  ((slStepSourceNeAxiomEndpoint structural (.tensor exactLink)
                    terminalAxiom (Or.inl rfl)) rfl)
              · exact False.elim
                  ((slStepSourceNeAxiomEndpoint structural (.tensor exactLink)
                    terminalAxiom (Or.inr rfl)) rfl)
          | step head remaining =>
              have nextEq : _ = left :=
                slStepNextUnique structural head (.tensor exactLink)
              subst_vars
              rcases induction (.terminalPartner remaining terminalAxiom) with
                inTrace | endpoint
              · exact Or.inl (by simp [inTrace])
              · exact Or.inr endpoint
  | @par fuel tags producerIndex linkIndex left right conclusion reached
      partner trace source sourceLookup sourceLinkIndex sourceLink exactLink
      currentFresh currentReady tail induction =>
      cases region with
      | visited reachable =>
          cases reachable with
          | refl => exact Or.inl (by simp)
          | step head remaining =>
              have nextEq : _ = left :=
                slStepNextUnique structural head (.par exactLink)
              subst_vars
              rcases induction (.visited remaining) with inTrace | endpoint
              · exact Or.inl (by simp [inTrace])
              · exact Or.inr endpoint
      | @terminalPartner terminalReached terminalPartner terminalIndex
          reachable terminalAxiom =>
          cases reachable with
          | refl =>
              rcases terminalAxiom with terminalAxiom | terminalAxiom
              · exact False.elim
                  ((slStepSourceNeAxiomEndpoint structural (.par exactLink)
                    terminalAxiom (Or.inl rfl)) rfl)
              · exact False.elim
                  ((slStepSourceNeAxiomEndpoint structural (.par exactLink)
                    terminalAxiom (Or.inr rfl)) rfl)
          | step head remaining =>
              have nextEq : _ = left :=
                slStepNextUnique structural head (.par exactLink)
              subst_vars
              rcases induction (.terminalPartner remaining terminalAxiom) with
                inTrace | endpoint
              · exact Or.inl (by simp [inTrace])
              · exact Or.inr endpoint

end ProofNetIR.SequentialUnification

namespace ProofNetIR.SequentialFigure7

open SequentialUnification
open SequentialSchedulerBridge

set_option maxHeartbeats 800000 in
/-- Every vertex in a reservation event's complete source-left region was
touched by that exact event.  The proof reconstructs the run from the
successful initialization or `new` equation retained by `ReservationEvent`;
it does not assume another executor call succeeds or establish scheduler
progress, totality, or worklist completeness. -/
theorem ReservationEvent.sourceLeftRegion_touched
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (event : ReservationEvent certificate)
    {vertex : Vertex}
    (region : SourceLeftRegionVertex certificate event.start vertex) :
    event.Touched vertex := by
  cases event with
  | @initial after start step =>
      change SourceLeftRegionVertex certificate start vertex at region
      change step.result.Touched vertex
      have execution :
          FreshSourceLeftRun.FreshSourceLeftExecution certificate
            (ReservationState.empty certificate).core
            certificate.formulas.size
            (ReservationState.empty certificate).tags start
            step.result.trace step.reached step.partner
            step.result.linkIndex := by
        exact ⟨step.result, by
          simpa [nextAxiom?] using step.search_eq,
          rfl, rfl, step.oriented_eq⟩
      rcases (FreshSourceLeftRun.execution_iff_nonempty.mp execution) with
        ⟨run⟩
      have hit := run.sourceLeftRegion_touched structural region
      rcases step.route.storedEndpoints with
        ⟨reachedEq, partnerEq⟩ | ⟨reachedEq, partnerEq⟩
      · rcases hit with hit | hit
        · exact Or.inl hit
        · exact Or.inr (Or.inr (hit.trans partnerEq))
      · rcases hit with hit | hit
        · exact Or.inl hit
        · exact Or.inr (Or.inl (hit.trans partnerEq))
  | @new before after step =>
      change SourceLeftRegionVertex certificate step.tensor.mate vertex at region
      change step.search.Touched vertex
      have execution :
          FreshSourceLeftRun.FreshSourceLeftExecution certificate
            step.coreMarked certificate.formulas.size before.tags
            step.tensor.mate step.search.trace step.reached step.partner
            step.search.linkIndex := by
        exact ⟨step.search, by
          simpa [nextAxiom?] using step.search_eq,
          rfl, rfl, step.oriented_eq⟩
      rcases (FreshSourceLeftRun.execution_iff_nonempty.mp execution) with
        ⟨run⟩
      have hit := run.sourceLeftRegion_touched structural region
      rcases step.route.storedEndpoints with
        ⟨reachedEq, partnerEq⟩ | ⟨reachedEq, partnerEq⟩
      · rcases hit with hit | hit
        · exact Or.inl hit
        · exact Or.inr (Or.inr (hit.trans partnerEq))
      · rcases hit with hit | hit
        · exact Or.inl hit
        · exact Or.inr (Or.inl (hit.trans partnerEq))

/-- On a structurally well-formed certificate, an exact reservation event
touches precisely its complete source-left region. -/
theorem ReservationEvent.touched_iff_sourceLeftRegion
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (event : ReservationEvent certificate)
    {vertex : Vertex} :
    event.Touched vertex ↔
      SourceLeftRegionVertex certificate event.start vertex := by
  constructor
  · exact event.touched_sourceLeftRegion
  · exact ReservationEvent.sourceLeftRegion_touched structural event

end ProofNetIR.SequentialFigure7
