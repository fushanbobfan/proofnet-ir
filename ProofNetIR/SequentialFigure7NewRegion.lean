import ProofNetIR.IntrinsicCanonical
import ProofNetIR.SequentialFigure7NewEnabledCore
import ProofNetIR.SequentialFigure7ProgressInvariant

namespace ProofNetIR

/-!
# Exact source-region reconstruction for Figure-7 `new`

This module reconstructs the proof-relevant `NEXTAXIOM` run already described
by a `FreshSourceLeftRoute`.  The reconstruction is local: structural
well-formedness separates every connective conclusion in the route from the
terminal axiom's other endpoint, so the route itself supplies all remaining
freshness and readiness data.  It assumes no executor success, scheduler
reachability, enabledness, progress, or completeness.
-/

namespace SequentialFigure7.FreshSourceLeftRoute

open SequentialUnification

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
  have firstWellFormed :=
    structural.2.2.2.2.1 _ firstMembership
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

private theorem connective_eq_of_shared_conclusion
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {first second : Link} {conclusion : Vertex}
    (firstMembership : first ∈ certificate.links)
    (firstProduces : first.produces conclusion = true)
    (secondMembership : second ∈ certificate.links)
    (secondProduces : second.produces conclusion = true) :
    first = second := by
  have firstWellFormed :=
    structural.2.2.2.2.1 _ firstMembership
  have formulaShape :
      ∃ formula,
        certificate.formula? conclusion = some formula ∧
          conclusion < certificate.formulas.size ∧
          formula.isAtom = false := by
    cases first with
    | «axiom» left right =>
        simp [Link.produces] at firstProduces
    | tensor left right produced =>
        simp [Link.produces] at firstProduces
        subst produced
        rcases firstWellFormed.tensor_conclusionFormula with
          ⟨leftFormula, rightFormula, formulaLookup⟩
        exact
          ⟨.tensor leftFormula rightFormula, formulaLookup,
            firstWellFormed.2.2.2.2.2.1, rfl⟩
    | «par» left right produced =>
        simp [Link.produces] at firstProduces
        subst produced
        rcases firstWellFormed.par_conclusionFormula with
          ⟨leftFormula, rightFormula, formulaLookup⟩
        exact
          ⟨.par leftFormula rightFormula, formulaLookup,
            firstWellFormed.2.2.2.2.2.1, rfl⟩
  rcases formulaShape with
    ⟨formula, formulaLookup, conclusionBound, compound⟩
  have node := structural.2.2.2.2.2 conclusion conclusionBound
  have count : certificate.producerCount conclusion = 1 := by
    cases formula <;>
      simp [Certificate.NodeWellFormed, formulaLookup] at compound node
    · contradiction
    · exact node.1
    · exact node.1
  unfold Certificate.producerCount at count
  have firstFiltered :
      first ∈ certificate.links.filter (·.produces conclusion) := by
    simp [firstMembership, firstProduces]
  have secondFiltered :
      second ∈ certificate.links.filter (·.produces conclusion) := by
    simp [secondMembership, secondProduces]
  rcases List.length_eq_one_iff.mp count with ⟨only, filterEquation⟩
  rw [filterEquation] at firstFiltered secondFiltered
  simp at firstFiltered secondFiltered
  exact firstFiltered.trans secondFiltered.symm

private theorem source_produces_of_connective
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {expected : Link} {conclusion : Vertex}
    (expectedMembership : expected ∈ certificate.links)
    (expectedProduces : expected.produces conclusion = true)
    {source : SourceIncidence}
    (sourceMembership : source.link ∈ certificate.links)
    (sourceOrigin :
      source.link.containsAxiomEndpoint conclusion = true ∨
        source.link.produces conclusion = true) :
    source.link.produces conclusion = true := by
  rcases sourceOrigin with sourceAxiom | sourceProduces
  · have expectedWellFormed :=
      structural.2.2.2.2.1 _ expectedMembership
    have sourceWellFormed :=
      structural.2.2.2.2.1 _ sourceMembership
    cases expected with
    | «axiom» left right =>
        simp [Link.produces] at expectedProduces
    | tensor left right produced =>
        simp [Link.produces] at expectedProduces
        subst produced
        rcases expectedWellFormed.tensor_conclusionFormula with
          ⟨leftFormula, rightFormula, expectedFormula⟩
        cases sourceLinkEquation : source.link with
        | «axiom» sourceLeft sourceRight =>
            have sourceWellFormed' :
                certificate.LinkWellFormed (.axiom sourceLeft sourceRight) := by
              simpa [sourceLinkEquation] using sourceWellFormed
            simp [sourceLinkEquation, Link.containsAxiomEndpoint] at sourceAxiom
            rcases sourceAxiom with sourceAxiom | sourceAxiom
            · subst sourceLeft
              rcases sourceWellFormed'.axiom_endpointFormula (Or.inl rfl) with
                ⟨name, positive, sourceFormula⟩
              have impossible := Option.some.inj
                (sourceFormula.symm.trans expectedFormula)
              cases impossible
            · subst sourceRight
              rcases sourceWellFormed'.axiom_endpointFormula (Or.inr rfl) with
                ⟨name, positive, sourceFormula⟩
              have impossible := Option.some.inj
                (sourceFormula.symm.trans expectedFormula)
              cases impossible
        | tensor sourceLeft sourceRight sourceConclusion =>
            simp [sourceLinkEquation, Link.containsAxiomEndpoint] at sourceAxiom
        | «par» sourceLeft sourceRight sourceConclusion =>
            simp [sourceLinkEquation, Link.containsAxiomEndpoint] at sourceAxiom
    | «par» left right produced =>
        simp [Link.produces] at expectedProduces
        subst produced
        rcases expectedWellFormed.par_conclusionFormula with
          ⟨leftFormula, rightFormula, expectedFormula⟩
        cases sourceLinkEquation : source.link with
        | «axiom» sourceLeft sourceRight =>
            have sourceWellFormed' :
                certificate.LinkWellFormed (.axiom sourceLeft sourceRight) := by
              simpa [sourceLinkEquation] using sourceWellFormed
            simp [sourceLinkEquation, Link.containsAxiomEndpoint] at sourceAxiom
            rcases sourceAxiom with sourceAxiom | sourceAxiom
            · subst sourceLeft
              rcases sourceWellFormed'.axiom_endpointFormula (Or.inl rfl) with
                ⟨name, positive, sourceFormula⟩
              have impossible := Option.some.inj
                (sourceFormula.symm.trans expectedFormula)
              cases impossible
            · subst sourceRight
              rcases sourceWellFormed'.axiom_endpointFormula (Or.inr rfl) with
                ⟨name, positive, sourceFormula⟩
              have impossible := Option.some.inj
                (sourceFormula.symm.trans expectedFormula)
              cases impossible
        | tensor sourceLeft sourceRight sourceConclusion =>
            simp [sourceLinkEquation, Link.containsAxiomEndpoint] at sourceAxiom
        | «par» sourceLeft sourceRight sourceConclusion =>
            simp [sourceLinkEquation, Link.containsAxiomEndpoint] at sourceAxiom
  · exact sourceProduces

private theorem source_is_axiom_of_axiom_endpoint
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {expectedLeft expectedRight endpoint : Vertex}
    (expectedMembership :
      Link.axiom expectedLeft expectedRight ∈ certificate.links)
    (expectedEndpoint : endpoint = expectedLeft ∨ endpoint = expectedRight)
    {source : SourceIncidence}
    (sourceMembership : source.link ∈ certificate.links)
    (sourceOrigin :
      source.link.containsAxiomEndpoint endpoint = true ∨
        source.link.produces endpoint = true) :
    ∃ sourceLeft sourceRight,
      source.link = .axiom sourceLeft sourceRight ∧
        (endpoint = sourceLeft ∨ endpoint = sourceRight) := by
  have expectedWellFormed :=
    structural.2.2.2.2.1 _ expectedMembership
  rcases expectedWellFormed.axiom_endpointFormula expectedEndpoint with
    ⟨name, positive, expectedFormula⟩
  have sourceWellFormed :=
    structural.2.2.2.2.1 _ sourceMembership
  cases sourceLinkEquation : source.link with
  | «axiom» sourceLeft sourceRight =>
      refine ⟨sourceLeft, sourceRight, rfl, ?_⟩
      rcases sourceOrigin with sourceAxiom | sourceProduces
      · have reversed :
            sourceLeft = endpoint ∨ sourceRight = endpoint := by
          simpa [sourceLinkEquation, Link.containsAxiomEndpoint] using sourceAxiom
        exact reversed.imp Eq.symm Eq.symm
      · simp [sourceLinkEquation, Link.produces] at sourceProduces
  | tensor sourceLeft sourceRight sourceConclusion =>
      have sourceWellFormed' :
          certificate.LinkWellFormed
            (.tensor sourceLeft sourceRight sourceConclusion) := by
        simpa [sourceLinkEquation] using sourceWellFormed
      rcases sourceOrigin with sourceAxiom | sourceProduces
      · simp [sourceLinkEquation, Link.containsAxiomEndpoint] at sourceAxiom
      · simp [sourceLinkEquation, Link.produces] at sourceProduces
        subst sourceConclusion
        rcases sourceWellFormed'.tensor_conclusionFormula with
          ⟨leftFormula, rightFormula, sourceFormula⟩
        have impossible := Option.some.inj
          (expectedFormula.symm.trans sourceFormula)
        cases impossible
  | «par» sourceLeft sourceRight sourceConclusion =>
      have sourceWellFormed' :
          certificate.LinkWellFormed
            (.par sourceLeft sourceRight sourceConclusion) := by
        simpa [sourceLinkEquation] using sourceWellFormed
      rcases sourceOrigin with sourceAxiom | sourceProduces
      · simp [sourceLinkEquation, Link.containsAxiomEndpoint] at sourceAxiom
      · simp [sourceLinkEquation, Link.produces] at sourceProduces
        subst sourceConclusion
        rcases sourceWellFormed'.par_conclusionFormula with
          ⟨leftFormula, rightFormula, sourceFormula⟩
        have impossible := Option.some.inj
          (expectedFormula.symm.trans sourceFormula)
        cases impossible

private theorem sourceIndex_lookup_eq_submitted_connective
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {linkIndex : Nat} {link : Link} {conclusion : Vertex}
    (exactLink : certificate.links[linkIndex]? = some link)
    (produces : link.produces conclusion = true) :
    (sourceIndex certificate)[conclusion]? =
      some [{ linkIndex := linkIndex, link := link }] := by
  have expectedMembership : link ∈ certificate.links :=
    List.mem_of_getElem? exactLink
  have expectedWellFormed :=
    structural.2.2.2.2.1 _ expectedMembership
  have conclusionBound : conclusion < certificate.formulas.size := by
    cases link with
    | «axiom» left right => simp [Link.produces] at produces
    | tensor left right produced =>
        simp [Link.produces] at produces
        subst produced
        exact expectedWellFormed.2.2.2.2.2.1
    | «par» left right produced =>
        simp [Link.produces] at produces
        subst produced
        exact expectedWellFormed.2.2.2.2.2.1
  rcases StructurallyWellFormed.sourceIndex_lookup_eq_singleton
      structural conclusionBound with
    ⟨source, sourceLookup⟩
  have sourceBucketMembership :
      source ∈ ((sourceIndex certificate)[conclusion]?).getD [] := by
    simp [sourceLookup]
  have sourceOrigin := (sourceIndex_sound certificate sourceBucketMembership)
  have sourceLookupBound : source.linkIndex < certificate.links.length :=
    (List.getElem?_eq_some_iff.mp sourceOrigin.1).1
  have sourceMembership : source.link ∈ certificate.links :=
    List.mem_of_getElem? sourceOrigin.1
  have sourceProduces : source.link.produces conclusion = true :=
    source_produces_of_connective structural expectedMembership produces
      sourceMembership sourceOrigin.2
  have sameLink : source.link = link :=
    connective_eq_of_shared_conclusion structural sourceMembership
      sourceProduces expectedMembership produces
  have sameIndex : source.linkIndex = linkIndex := by
    apply (List.getElem?_inj sourceLookupBound structural.links_nodup).mp
    rw [sourceOrigin.1, exactLink, sameLink]
  rcases source with ⟨sourceLinkIndex, sourceLink⟩
  simp only at sameLink sameIndex sourceLookup ⊢
  subst sourceLink
  subst sourceLinkIndex
  exact sourceLookup

private theorem sourceIndex_lookup_eq_submitted_axiom_endpoint
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {linkIndex : Nat} {left right endpoint : Vertex}
    (exactLink : certificate.links[linkIndex]? = some (.axiom left right))
    (endpointAt : endpoint = left ∨ endpoint = right) :
    (sourceIndex certificate)[endpoint]? =
      some [{ linkIndex := linkIndex, link := .axiom left right }] := by
  have expectedMembership :
      Link.axiom left right ∈ certificate.links :=
    List.mem_of_getElem? exactLink
  have expectedWellFormed :=
    structural.2.2.2.2.1 _ expectedMembership
  have endpointBound : endpoint < certificate.formulas.size := by
    rcases endpointAt with rfl | rfl
    · exact expectedWellFormed.2.1
    · exact expectedWellFormed.2.2.1
  rcases StructurallyWellFormed.sourceIndex_lookup_eq_singleton
      structural endpointBound with
    ⟨source, sourceLookup⟩
  have sourceBucketMembership :
      source ∈ ((sourceIndex certificate)[endpoint]?).getD [] := by
    simp [sourceLookup]
  have sourceOrigin := sourceIndex_sound certificate sourceBucketMembership
  have sourceLookupBound : source.linkIndex < certificate.links.length :=
    (List.getElem?_eq_some_iff.mp sourceOrigin.1).1
  have sourceMembership : source.link ∈ certificate.links :=
    List.mem_of_getElem? sourceOrigin.1
  rcases source_is_axiom_of_axiom_endpoint structural expectedMembership
      endpointAt sourceMembership sourceOrigin.2 with
    ⟨sourceLeft, sourceRight, sourceLink, sourceEndpoint⟩
  have sourceAxiomMembership :
      Link.axiom sourceLeft sourceRight ∈ certificate.links := by
    simpa [sourceLink] using sourceMembership
  have sameLink : source.link = .axiom left right := by
    rw [sourceLink]
    exact axiom_eq_of_shared_endpoint structural sourceAxiomMembership
      sourceEndpoint expectedMembership endpointAt
  have sameIndex : source.linkIndex = linkIndex := by
    apply (List.getElem?_inj sourceLookupBound structural.links_nodup).mp
    rw [sourceOrigin.1, exactLink, sameLink]
  rcases source with ⟨sourceLinkIndex, actualLink⟩
  simp only at sameLink sameIndex sourceLookup ⊢
  subst actualLink
  subst sourceLinkIndex
  exact sourceLookup

private theorem exists_run_of_chain
    {certificate : Certificate} {state : UnificationState}
    {fuel : Nat} {tags : Array Bool} {start reached partner : Vertex}
    {trace : List Vertex} {linkIndex : Nat}
    (structural : certificate.StructurallyWellFormed)
    (chain : SourceLeftChain certificate trace)
    (traceHead : trace.head? = some start)
    (traceLast : trace.getLast? = some reached)
    (exactAxiom :
      certificate.links[linkIndex]? = some (.axiom reached partner) ∨
        certificate.links[linkIndex]? = some (.axiom partner reached))
    (traceLength : trace.length ≤ fuel)
    (traceNodup : trace.Nodup)
    (traceFresh :
      ∀ {vertex : Vertex}, vertex ∈ trace → tags[vertex]? = some false)
    (traceReady :
      ∀ {vertex : Vertex}, vertex ∈ trace →
        state.marks[vertex]? = some none)
    (partnerReady : state.marks[partner]? = some none)
    (partnerFresh : tags[partner]? = some false)
    (partnerOutside : partner ∉ trace) :
    Nonempty
      (FreshSourceLeftRun certificate state fuel tags start trace reached
        partner linkIndex) := by
  induction chain generalizing fuel tags start reached partner linkIndex with
  | singleton vertex =>
      simp only [List.head?_cons, Option.some.injEq] at traceHead
      simp only [List.getLast?_singleton, Option.some.injEq] at traceLast
      subst start
      subst reached
      cases fuel with
      | zero => simp at traceLength
      | succ fuel =>
          have vertexFresh : tags[vertex]? = some false :=
            traceFresh (by simp)
          have vertexReady : state.marks[vertex]? = some none :=
            traceReady (by simp)
          rcases exactAxiom with exactLeft | exactRight
          · have sourceLookup :=
              sourceIndex_lookup_eq_submitted_axiom_endpoint structural
                exactLeft (Or.inl rfl)
            have membership := List.mem_of_getElem? exactLeft
            have wellFormed := structural.2.2.2.2.1 _ membership
            exact ⟨.axiomLeft _ sourceLookup rfl rfl exactLeft
              wellFormed.1 vertexFresh partnerFresh vertexReady
              partnerReady⟩
          · have sourceLookup :=
              sourceIndex_lookup_eq_submitted_axiom_endpoint structural
                exactRight (Or.inr rfl)
            have membership := List.mem_of_getElem? exactRight
            have wellFormed := structural.2.2.2.2.1 _ membership
            exact ⟨.axiomRight _ sourceLookup rfl rfl exactRight
              wellFormed.1 partnerFresh vertexFresh partnerReady
              vertexReady⟩
  | @cons source next tail step rest induction =>
      simp only [List.head?_cons, Option.some.injEq] at traceHead
      subst start
      cases fuel with
      | zero => simp at traceLength
      | succ fuel =>
          have tailLength : (next :: tail).length ≤ fuel := by
            simpa using traceLength
          have tailLast : (next :: tail).getLast? = some reached := by
            simpa [List.getLast?_cons_of_ne_nil (by simp : next :: tail ≠ [])]
              using traceLast
          have sourceNotTail : source ∉ next :: tail :=
            (List.nodup_cons.mp traceNodup).1
          have tailNodup : (next :: tail).Nodup :=
            (List.nodup_cons.mp traceNodup).2
          have sourceFresh : tags[source]? = some false :=
            traceFresh (by simp)
          have sourceReady : state.marks[source]? = some none :=
            traceReady (by simp)
          have tailFresh :
              ∀ {vertex : Vertex}, vertex ∈ next :: tail →
                (nextAxiomSetTag tags source)[vertex]? = some false := by
            intro vertex membership
            have different : source ≠ vertex := by
              intro same
              subst vertex
              exact sourceNotTail membership
            simpa [nextAxiomSetTag_eq, different] using
              traceFresh (by simp [membership])
          have tailReady :
              ∀ {vertex : Vertex}, vertex ∈ next :: tail →
                state.marks[vertex]? = some none := by
            intro vertex membership
            exact traceReady (by simp [membership])
          have partnerNeSource : source ≠ partner := by
            intro same
            subst partner
            exact partnerOutside (by simp)
          have tailPartnerFresh :
              (nextAxiomSetTag tags source)[partner]? = some false := by
            simpa [nextAxiomSetTag_eq, partnerNeSource] using partnerFresh
          have tailPartnerOutside : partner ∉ next :: tail := by
            intro membership
            exact partnerOutside (by simp [membership])
          rcases induction rfl tailLast exactAxiom tailLength
              tailNodup tailFresh tailReady partnerReady tailPartnerFresh
              tailPartnerOutside with
            ⟨tailRun⟩
          cases step with
          | @tensor producerIndex left right conclusion exactLink =>
              have sourceLookup :=
                sourceIndex_lookup_eq_submitted_connective
                  (link := .tensor next right source) (conclusion := source)
                  structural exactLink (by simp [Link.produces])
              exact ⟨FreshSourceLeftRun.tensor
                (producerIndex := producerIndex) (left := next)
                (right := right) (conclusion := source)
                { linkIndex := producerIndex,
                  link := .tensor next right source }
                sourceLookup rfl rfl exactLink sourceFresh sourceReady
                tailRun⟩
          | @par producerIndex left right conclusion exactLink =>
              have sourceLookup :=
                sourceIndex_lookup_eq_submitted_connective
                  (link := .par next right source) (conclusion := source)
                  structural exactLink (by simp [Link.produces])
              exact ⟨FreshSourceLeftRun.par
                (producerIndex := producerIndex) (left := next)
                (right := right) (conclusion := source)
                { linkIndex := producerIndex,
                  link := .par next right source }
                sourceLookup rfl rfl exactLink sourceFresh sourceReady
                tailRun⟩

private theorem connective_conclusion_ne_axiom_endpoint
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
  have connectiveLookup :=
    sourceIndex_lookup_eq_submitted_connective
      structural exactConnective produces
  have axiomLookup :=
    sourceIndex_lookup_eq_submitted_axiom_endpoint
      structural exactAxiom endpointAt
  have incidenceEq :
      ({ linkIndex := producerIndex, link := link } : SourceIncidence) =
        ({ linkIndex := axiomIndex, link := .axiom left right } :
          SourceIncidence) := by
    have singletonEq :
        ([{ linkIndex := producerIndex, link := link }] :
          List SourceIncidence) =
          [{ linkIndex := axiomIndex, link := .axiom left right }] :=
      Option.some.inj (connectiveLookup.symm.trans axiomLookup)
    simpa using singletonEq
  have linkEq : link = .axiom left right :=
    congrArg SourceIncidence.link incidenceEq
  subst link
  simp [Link.isConnective] at connective

private theorem step_source_ne_axiom_partner
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {source next reached partner : Vertex} {linkIndex : Nat}
    (step : SourceLeftStep certificate source next)
    (exactAxiom :
      certificate.links[linkIndex]? = some (.axiom reached partner) ∨
        certificate.links[linkIndex]? = some (.axiom partner reached)) :
    source ≠ partner := by
  cases step with
  | @tensor producerIndex left right conclusion exactConnective =>
      rcases exactAxiom with exactAxiom | exactAxiom
      · exact connective_conclusion_ne_axiom_endpoint structural
          exactConnective (by simp [Link.produces])
          (by simp [Link.isConnective]) exactAxiom (Or.inr rfl)
      · exact connective_conclusion_ne_axiom_endpoint structural
          exactConnective (by simp [Link.produces])
          (by simp [Link.isConnective]) exactAxiom (Or.inl rfl)
  | @par producerIndex left right conclusion exactConnective =>
      rcases exactAxiom with exactAxiom | exactAxiom
      · exact connective_conclusion_ne_axiom_endpoint structural
          exactConnective (by simp [Link.produces])
          (by simp [Link.isConnective]) exactAxiom (Or.inr rfl)
      · exact connective_conclusion_ne_axiom_endpoint structural
          exactConnective (by simp [Link.produces])
          (by simp [Link.isConnective]) exactAxiom (Or.inl rfl)

private theorem reached_ne_partner_of_exact_axiom
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {reached partner : Vertex} {linkIndex : Nat}
    (exactAxiom :
      certificate.links[linkIndex]? = some (.axiom reached partner) ∨
        certificate.links[linkIndex]? = some (.axiom partner reached)) :
    reached ≠ partner := by
  rcases exactAxiom with exactAxiom | exactAxiom
  · exact (structural.2.2.2.2.1 _
      (List.mem_of_getElem? exactAxiom)).1
  · exact (structural.2.2.2.2.1 _
      (List.mem_of_getElem? exactAxiom)).1.symm

private theorem partner_not_mem_chain_of_structural
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {trace : List Vertex} {reached partner : Vertex} {linkIndex : Nat}
    (chain : SourceLeftChain certificate trace)
    (traceLast : trace.getLast? = some reached)
    (exactAxiom :
      certificate.links[linkIndex]? = some (.axiom reached partner) ∨
        certificate.links[linkIndex]? = some (.axiom partner reached)) :
    partner ∉ trace := by
  induction chain generalizing reached partner linkIndex with
  | singleton vertex =>
      have vertexEq : vertex = reached := by
        simpa using traceLast
      subst vertex
      simpa using (reached_ne_partner_of_exact_axiom
        structural exactAxiom).symm
  | @cons source next tail step rest induction =>
      have tailLast : (next :: tail).getLast? = some reached := by
        simpa [List.getLast?_cons_of_ne_nil (by simp : next :: tail ≠ [])]
          using traceLast
      simp only [List.mem_cons, not_or]
      exact ⟨(step_source_ne_axiom_partner structural step exactAxiom).symm,
        by simpa only [List.mem_cons, not_or] using
          induction tailLast exactAxiom⟩

/-- Structural well-formedness makes the terminal axiom partner disjoint from
the complete source-left trace.  Nonterminal trace occurrences are exact
connective conclusions, while the last occurrence is the distinct reached
endpoint of the exact terminal axiom. -/
theorem partner_not_mem_trace_of_structural
    {certificate : Certificate} {state : UnificationState}
    {tags : Array Bool} {start : Vertex}
    (route :
      SequentialFigure7.FreshSourceLeftRoute certificate state tags start)
    (structural : certificate.StructurallyWellFormed) :
    route.partner ∉ route.trace :=
  partner_not_mem_chain_of_structural structural route.chain route.traceLast
    route.exactAxiom

/-- A structurally well-formed exact route reconstructs the formula-budget
proof-relevant run.  This is a local route-to-run theorem, not a scheduler
enabledness, executor-success, reachability, or progress result. -/
theorem toFreshSourceLeftRun_of_partnerOutside
    {certificate : Certificate} {state : UnificationState}
    {tags : Array Bool} {start : Vertex}
    (route :
      SequentialFigure7.FreshSourceLeftRoute certificate state tags start)
    (structural : certificate.StructurallyWellFormed)
    (partnerOutside : route.partner ∉ route.trace) :
    Nonempty
      (FreshSourceLeftRun certificate state certificate.formulas.size tags
        start route.trace route.reached route.partner route.linkIndex) :=
  exists_run_of_chain structural route.chain route.traceHead route.traceLast
    route.exactAxiom route.traceLength route.traceNodup route.traceFresh
    route.traceReady route.partnerReady route.partnerFresh partnerOutside

/-- Structural well-formedness alone discharges the terminal-partner
separation needed by exact run reconstruction. -/
theorem toFreshSourceLeftRun
    {certificate : Certificate} {state : UnificationState}
    {tags : Array Bool} {start : Vertex}
    (route :
      SequentialFigure7.FreshSourceLeftRoute certificate state tags start)
    (structural : certificate.StructurallyWellFormed) :
    Nonempty
      (FreshSourceLeftRun certificate state certificate.formulas.size tags
        start route.trace route.reached route.partner route.linkIndex) :=
  route.toFreshSourceLeftRun_of_partnerOutside structural
    (route.partner_not_mem_trace_of_structural structural)

end SequentialFigure7.FreshSourceLeftRoute

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- Input-only source-region data sufficient to discharge the two pieces that
remain outside an exact `NEXTAXIOM` run: global queue separation for the
terminal endpoints and capacity for the next waiting cell.  It stores no
executor result, transition equation, history, or reachability witness. -/
structure NewSourceRegionInput (certificate : Certificate)
    (before : ReservationState) : Type where
  guard : NewGuard certificate before
  trace : List Vertex
  reached : Vertex
  partner : Vertex
  linkIndex : Nat
  run :
    SequentialUnification.FreshSourceLeftRun certificate
      guard.head.markedCore certificate.formulas.size before.tags
      guard.tensor.mate trace reached partner linkIndex
  reached_not_queued :
    reached ∉ guard.head.markedStack.queuedVertices
  partner_not_queued :
    partner ∉ guard.head.markedStack.queuedVertices
  fresh_capacity :
    guard.head.markedStack.nextAge < guard.head.markedStack.waiting.size

namespace NewSourceRegionInput

private def prepared
    {certificate : Certificate} {before : ReservationState}
    (input : NewSourceRegionInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    PreparedStep before where
  stackResult := input.guard.head.stackResult
  coreMarked := input.guard.head.markedCore
  stack_eq := input.guard.head.stack_pop_eq invariant
  core_mark_eq := input.guard.head.core_mark_eq invariant

private theorem middle_schedulerInvariant
    {certificate : Certificate} {before : ReservationState}
    (input : NewSourceRegionInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    SchedulerInvariant certificate input.guard.head.middle := by
  simpa [prepared, ReadyHeadInput.stackResult, PreparedStep.after,
    ReadyHeadInput.middle, ReadyHeadInput.markedStack,
    ReadyHeadInput.markedCore] using
      (input.prepared invariant).schedulerInvariant invariant

/-- The complete state invariant supplies every operational enqueue fact
except endpoint absence and fresh waiting capacity; those three facts are the
explicit source-region fields.  `FutureWaitingUndefined` turns capacity into
the required unused-cell lookup. -/
theorem operationalNewReadyAt
    {certificate : Certificate} {before : ReservationState}
    (input : NewSourceRegionInput certificate before)
    (invariant : SchedulerInvariant certificate before)
    (future : FutureWaitingUndefined before) :
    OperationalNewReadyAt input.guard.head.markedStack
      input.guard.head.rawAge input.reached input.partner := by
  have middleInvariant := input.middle_schedulerInvariant invariant
  have activeMembership :
      input.guard.head.rawAge ∈ input.guard.head.markedStack.sigma := by
    have oldMembership :
        input.guard.head.rawAge ∈ before.stack.sigma :=
      List.mem_of_getLast? input.guard.head.sigma_top
    simpa [ReadyHeadInput.markedStack] using oldMembership
  have activeLt :
      input.guard.head.rawAge < input.guard.head.markedStack.nextAge :=
    middleInvariant.stack_wellShaped.sigma_partition.boundary_lt
      input.guard.head.rawAge activeMembership
  have reachedReady :
      input.guard.head.markedStack.marks[input.reached]? = some none := by
    change input.guard.head.middle.stack.marks[input.reached]? = some none
    rw [← middleInvariant.realizesSigma.marks_eq]
    change input.guard.head.markedCore.marks[input.reached]? = some none
    exact input.run.reachedReady
  have partnerReady :
      input.guard.head.markedStack.marks[input.partner]? = some none := by
    change input.guard.head.middle.stack.marks[input.partner]? = some none
    rw [← middleInvariant.realizesSigma.marks_eq]
    change input.guard.head.markedCore.marks[input.partner]? = some none
    exact input.run.partnerReady
  have reachedBound :
      input.reached < input.guard.head.markedStack.marks.size :=
    (Array.getElem?_eq_some_iff.mp reachedReady).1
  have partnerBound :
      input.partner < input.guard.head.markedStack.marks.size :=
    (Array.getElem?_eq_some_iff.mp partnerReady).1
  have different : input.reached ≠ input.partner := by
    cases input.run.terminalAxiom with
    | reachedLeft _ different _ _ => exact different
    | reachedRight _ different _ _ => exact different
  have activeUndefined :
      input.guard.head.markedStack.waiting[input.guard.head.rawAge]? =
        some .undefined := by
    have middleActive :
        input.guard.head.middle.stack.waiting[input.guard.head.rawAge]? =
          some .undefined :=
      middleInvariant.stack_operationalWaitingDomain.active_undefined
        middleInvariant.stack_wellShaped (by
          simpa [ReadyHeadInput.middle, ReadyHeadInput.markedStack] using
            input.guard.head.sigma_top)
    simpa [ReadyHeadInput.middle] using middleActive
  have oldCapacity :
      before.stack.nextAge < before.stack.waiting.size := by
    simpa [ReadyHeadInput.markedStack] using input.fresh_capacity
  have freshUndefined :
      input.guard.head.markedStack.waiting[
        input.guard.head.markedStack.nextAge]? = some .undefined := by
    have oldUndefined :=
      future before.stack.nextAge (Nat.le_refl _) oldCapacity
    simpa [ReadyHeadInput.markedStack] using oldUndefined
  exact ⟨Nat.zero_lt_of_lt activeLt,
    by simpa [ReadyHeadInput.markedStack] using input.guard.head.sigma_top,
    activeLt, reachedBound, partnerBound, different,
    input.reached_not_queued, input.partner_not_queued,
    reachedReady, partnerReady, activeUndefined, freshUndefined⟩

/-- Package the exact run and the derived enqueue guard as the existing
input-only `NewEnabledInput`. -/
def toNewEnabledInput
    {certificate : Certificate} {before : ReservationState}
    (input : NewSourceRegionInput certificate before)
    (invariant : SchedulerInvariant certificate before)
    (future : FutureWaitingUndefined before) :
    NewEnabledInput certificate before where
  guard := input.guard
  trace := input.trace
  reached := input.reached
  partner := input.partner
  linkIndex := input.linkIndex
  run := input.run
  enqueueReady := input.operationalNewReadyAt invariant future

/-- The source-region witness entails local input-only `new` enabledness under
the supplied state and unused-future-cell invariants.  This is not a
reachability, progress, or totality theorem. -/
theorem newEnabled
    {certificate : Certificate} {before : ReservationState}
    (input : NewSourceRegionInput certificate before)
    (invariant : SchedulerInvariant certificate before)
    (future : FutureWaitingUndefined before) :
    NewEnabled certificate before :=
  ⟨input.toNewEnabledInput invariant future⟩

end NewSourceRegionInput

end SequentialFigure7

end ProofNetIR
