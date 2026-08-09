import ProofNetIR.SequentialFigure7SameRepresentativeGeometry

namespace ProofNetIR

/-!
# Figure-7 same-representative historical-touch geometry

This module excludes one local blocker for an input-only `new`: a vertex
touched by one exact historical reservation event cannot also lie in the
current tensor mate's complete source-left region when the event and active
ready head have the same current union-find representative.

The proof is non-circular. It uses the historical route, final reservation
realization, current component provenance, and declarative reference-switching
acyclicity. It does not assume a `FreshSourceLeftRun`, `NewInputNecessary`,
`NewEnabled`, success of the current `new?` call, dispatcher progress, or
worklist completeness.
-/

namespace SequentialUnification

/-- Every member of a source-left chain reaches the chain's last vertex. -/
theorem SourceLeftChain.reachable_to_last_of_mem
    {certificate : Certificate} {trace : List Vertex}
    {vertex target : Vertex}
    (chain : SourceLeftChain certificate trace)
    (membership : vertex ∈ trace)
    (last : trace.getLast? = some target) :
    SourceLeftReachable certificate vertex target := by
  induction chain generalizing vertex target with
  | singleton only =>
      simp only [List.mem_singleton] at membership
      subst vertex
      simp only [List.getLast?_singleton, Option.some.injEq] at last
      subst target
      exact .refl only
  | @cons source next tail step rest induction =>
      simp only [List.mem_cons] at membership
      have restLast : (next :: tail).getLast? = some target := by
        simpa [List.getLast?_cons_of_ne_nil (by simp : next :: tail ≠ [])]
          using last
      rcases membership with rfl | membership
      · exact .step step
          (rest.reachable_of_head_last (by simp) restLast)
      · exact induction
          (by simpa only [List.mem_cons] using membership) restLast

end SequentialUnification

namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState
open SequentialUnification

namespace ReservationEvent

/-- A historical touch has a structural source-left continuation to the
submitted axiom's stored-left endpoint. -/
theorem leftEndpoint_sourceLeftRegion_of_touched
    {certificate : Certificate}
    (event : ReservationEvent certificate)
    {vertex : Vertex}
    (touched : event.Touched vertex) :
    SourceLeftRegionVertex certificate vertex event.search.result.left := by
  rcases touched with inTrace | rfl | rfl
  · have reachable :
        SourceLeftReachable certificate vertex event.search.reached :=
      event.search.route.chain.reachable_to_last_of_mem inTrace
        event.search.route.traceLast
    rcases event.search.route.storedEndpoints with
      ⟨reachedEq, _partnerEq⟩ | ⟨reachedEq, _partnerEq⟩
    · simpa [reachedEq] using
        (SourceLeftRegionVertex.visited reachable)
    · exact .terminalPartner reachable (by
        right
        simpa [reachedEq] using event.search.result.exactLink)
  · exact .visited (.refl _)
  · exact .terminalPartner (.refl _)
      (Or.inr event.search.result.exactLink)

end ReservationEvent

namespace NewGuard

/-- Every occurrence in the selected mate's complete source-left region is
strictly less complex than the selected tensor conclusion. -/
theorem sourceLeftRegion_formulaComplexity_lt_conclusion
    {certificate : Certificate} {before : ReservationState}
    (guard : NewGuard certificate before)
    (structural : certificate.StructurallyWellFormed)
    {vertex : Vertex}
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex) :
    certificate.formulaComplexityAt vertex <
      certificate.formulaComplexityAt guard.tensor.conclusion := by
  have tensorWellFormed := guard.tensor_valid.2.2.1
  have mateBelowConclusion :
      certificate.formulaComplexityAt guard.tensor.mate <
        certificate.formulaComplexityAt guard.tensor.conclusion := by
    simpa [Certificate.linkConclusionComplexity] using
      tensorWellFormed.premise_complexity_lt_conclusion
        (premise := guard.tensor.mate) (by
          cases sideEquation : guard.tensor.side <;>
            simp [Link.premises, TensorBelow.mate,
              TensorPremiseSide.mate, sideEquation])
  cases region with
  | visited reachable =>
      have vertexLeMate := reachable.formulaComplexity_le structural
      omega
  | terminalPartner reachable exactAxiom =>
      have endpointFormula :
          ∃ name positive,
            certificate.formula? vertex = some (.atom name positive) := by
        rcases exactAxiom with exactAxiom | exactAxiom
        · have axiomWellFormed :=
            structural.2.2.2.2.1 _ (List.mem_of_getElem? exactAxiom)
          exact axiomWellFormed.axiom_endpointFormula (Or.inr rfl)
        · have axiomWellFormed :=
            structural.2.2.2.2.1 _ (List.mem_of_getElem? exactAxiom)
          exact axiomWellFormed.axiom_endpointFormula (Or.inl rfl)
      rcases endpointFormula with ⟨name, positive, partnerFormula⟩
      have partnerComplexity :
          certificate.formulaComplexityAt vertex = 0 := by
        simp [Certificate.formulaComplexityAt, partnerFormula,
          Formula.complexity]
      rw [partnerComplexity]
      omega

end NewGuard

namespace CanonicalTagHistory

/-- A touch by one exact historical reservation event cannot lie in the
current `new` source-left region when the event and active ready head have the
same current representative.

This excludes only the same-representative historical-touch case. It does not
exclude strictly older events or old marked owners, construct a fresh route,
make `NewGuard` sufficient, or establish dispatcher progress. -/
theorem not_event_touch_of_sameRepresentative
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    (sameRepresentative :
      before.core.representative event.rawAge =
        before.core.representative guard.head.rawAge)
    {vertex : Vertex}
    (eventTouched : event.Touched vertex)
    (candidateRegion :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex) :
    False := by
  rcases guard.head.activeComponent invariant with
    ⟨activeComponent, _activeUsed, activeOwned, activeLookup,
      activeWitness, activeAccounted, headOwned, activeRoot⟩
  rcases tagHistory.reservationLedger_axiomEndpoints_accounted
      correct.1 eventMembership with
    ⟨eventComponent, _eventUsed, _eventForestUsed, eventOwned,
      eventLookup, eventDerivation, _eventLink, _eventWitness,
      _eventAccounted, eventLeftOwned, _eventRightOwned⟩
  have eventIndexEq :
      before.core.representative event.rawAge = guard.head.rawAge :=
    sameRepresentative.trans activeRoot
  have eventLookupAtActive :
      before.core.components[guard.head.rawAge]? =
        some (some eventComponent) := by
    simpa [eventIndexEq] using eventLookup
  have componentEq : eventComponent = activeComponent := by
    exact Option.some.inj
      (Option.some.inj (eventLookupAtActive.symm.trans activeLookup))
  subst eventComponent
  have ownedEq : eventOwned = activeOwned :=
    Certificate.OccurrenceDerivation.owned_unique correct.1
      eventDerivation activeWitness.derivation
  have eventLeftActiveOwned :
      event.search.result.left ∈ activeOwned := by
    rw [← ownedEq]
    exact eventLeftOwned
  rcases activeWitness.referencePath_within_owned
      eventLeftActiveOwned headOwned with
    ⟨componentPath, componentStarts, componentFinishes,
      componentPathOwned⟩
  have conclusionNotOwned :
      guard.tensor.conclusion ∉ activeOwned :=
    guard.tensorConclusion_not_owned invariant activeLookup activeAccounted
  have componentAvoids :
      guard.tensor.conclusion ∉ componentPath.vertices := by
    intro membership
    exact conclusionNotOwned
      (componentPathOwned guard.tensor.conclusion membership)
  have eventLeftNeConclusion :
      event.search.result.left ≠ guard.tensor.conclusion := by
    intro same
    apply conclusionNotOwned
    simpa [same] using eventLeftActiveOwned
  have mateBelowConclusion :
      certificate.formulaComplexityAt guard.tensor.mate <
        certificate.formulaComplexityAt guard.tensor.conclusion :=
    guard.sourceLeftRegion_formulaComplexity_lt_conclusion correct.1
      (.visited (.refl _))
  have vertexBelowConclusion :
      certificate.formulaComplexityAt vertex <
        certificate.formulaComplexityAt guard.tensor.conclusion :=
    guard.sourceLeftRegion_formulaComplexity_lt_conclusion correct.1
      candidateRegion
  have vertexNeConclusion : vertex ≠ guard.tensor.conclusion := by
    intro same
    subst vertex
    omega
  rcases sourceLeftRegionVertex_referencePath_avoiding correct.1
      candidateRegion mateBelowConclusion vertexNeConclusion with
    ⟨candidatePath, candidateStarts, candidateFinishes,
      candidateAvoids⟩
  have historicalRegion :
      SourceLeftRegionVertex certificate vertex
        event.search.result.left :=
    event.leftEndpoint_sourceLeftRegion_of_touched eventTouched
  rcases sourceLeftRegionVertex_referencePath_avoiding correct.1
      historicalRegion vertexBelowConclusion eventLeftNeConclusion with
    ⟨eventPath, eventStarts, eventFinishes, eventAvoids⟩
  have firstMeeting : candidatePath.finish = eventPath.start :=
    candidateFinishes.trans eventStarts.symm
  rcases Graph.EdgeSimplePath.connectEraseAvoiding candidatePath eventPath
      firstMeeting candidateAvoids eventAvoids with
    ⟨prefixPath, prefixStarts, prefixFinishes, prefixAvoids⟩
  have secondMeeting : prefixPath.finish = componentPath.start :=
    prefixFinishes.trans (eventFinishes.trans componentStarts.symm)
  rcases Graph.EdgeSimplePath.connectEraseAvoiding prefixPath componentPath
      secondMeeting prefixAvoids componentAvoids with
    ⟨path, pathStarts, pathFinishes, conclusionNotInPath⟩
  have combinedStarts : path.start = guard.tensor.mate :=
    pathStarts.trans (prefixStarts.trans candidateStarts)
  have combinedFinishes : path.finish = guard.head.vertex :=
    pathFinishes.trans componentFinishes
  have tensorMembership :
      Link.tensor guard.tensor.storedLeft guard.tensor.storedRight
          guard.tensor.conclusion ∈ certificate.links :=
    List.mem_of_getElem? guard.tensor_valid.2.1
  have headEquation := guard.tensor_valid.2.2.2
  cases sideEquation : guard.tensor.side with
  | storedLeft =>
      have headIsLeft :
          guard.head.vertex = guard.tensor.storedLeft := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using headEquation
      have mateIsRight :
          guard.tensor.mate = guard.tensor.storedRight := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      apply referenceAcyclic_no_tensorBypass correct.1
        correct.referenceSwitchingTree.acyclic tensorMembership path.reverse
      · exact combinedFinishes.trans headIsLeft
      · exact combinedStarts.trans mateIsRight
      · simpa using conclusionNotInPath
  | storedRight =>
      have headIsRight :
          guard.head.vertex = guard.tensor.storedRight := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using headEquation
      have mateIsLeft :
          guard.tensor.mate = guard.tensor.storedLeft := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      apply referenceAcyclic_no_tensorBypass correct.1
        correct.referenceSwitchingTree.acyclic tensorMembership path
      · exact combinedStarts.trans mateIsLeft
      · exact combinedFinishes.trans headIsRight
      · exact conclusionNotInPath

end CanonicalTagHistory

end SequentialFigure7

end ProofNetIR
