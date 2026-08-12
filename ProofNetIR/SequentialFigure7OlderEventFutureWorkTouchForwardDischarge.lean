/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchForwardPreservation
import ProofNetIR.SequentialComponentSourceLeftGeometry

/-!
# Figure-7 forward discharge of the created-head touch seam

For an already-successful typed `forward` step, certificate well-formedness and
the canonical history force every source-left vertex touched by an older
reservation event into that event's occurrence carrier. The same vertex would
also belong to the active carrier if it touched the newly inserted par
conclusion. Exact component-forest disjointness therefore excludes the touch.

The direct corollary feeds this result to the existing conditional `forward`
preservation theorem. It still requires the prior older-event future-work
head-separation invariant. This module proves no source-region or raw seam,
global availability, progress, totality, completeness, fallback removal, or
complexity result.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialUnification
open SequentialSchedulerBridge

namespace ForwardStep

/-- Every strictly older prior ledger event leaves the par conclusion inserted
by a successful typed `forward` step untouched. -/
theorem createdHeadTouchSeparated
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : ForwardStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed) :
    ForwardCreatedHeadTouchSeparated prior step := by
  have invariant : SchedulerInvariant certificate before :=
    history.schedulerInvariant structural
  intro event eventMembership _created older touched
  rcases prior.reservationLedger_axiomEndpoints_accounted
      structural eventMembership with
    ⟨eventComponent, eventUsed, eventForestUsed, eventOwned,
      eventLookup, eventDerivation, eventLink, eventWitness,
      eventAccounted, eventLeftOwned, eventRightOwned⟩
  rcases invariant.component_forest_provenance with
    ⟨usedAt, ownedAt, live, separated, markedOwned⟩
  have eventFacts := live eventLookup
  have eventOwnedEq :
      eventOwned = ownedAt (before.core.representative event.rawAge) :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      eventDerivation eventFacts.1.derivation
  have eventLeftForestOwned :
      event.search.result.left ∈
        ownedAt (before.core.representative event.rawAge) := by
    rw [← eventOwnedEq]
    exact eventLeftOwned
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have tokenGuards :=
    UnificationState.forwardToken?_success step.queueStep.token_guard
  have activeRoot :
      step.prepared.coreMarked.representative step.queueStep.outputToken =
        step.queueStep.outputToken :=
    middleInvariant.core_abstractable.tokenAt?_root tokenGuards.2.1
  have activeMiddleLookup :
      step.prepared.coreMarked.components[step.queueStep.outputToken]? =
        some (some step.queueStep.component) := by
    have rawLookup :=
      UnificationState.componentAt?_some_raw step.queueStep.component_lookup
    simpa [activeRoot] using rawLookup
  have componentsEq :
      step.prepared.coreMarked.components = before.core.components :=
    (UnificationState.markReadyRaw?_exact
      step.prepared.core_mark_eq).2.2.2.1
  have activeBeforeLookup :
      before.core.components[step.queueStep.outputToken]? =
        some (some step.queueStep.component) := by
    rw [← componentsEq]
    exact activeMiddleLookup
  have activeFacts := live activeBeforeLookup
  have outputDerivation :
      certificate.OccurrenceDerivation
        (.par step.queueStep.leftFocus step.queueStep.rightFocus
          step.queueStep.component.tree)
        (step.queueStep.context ++ [step.consumer.conclusion])
        (step.consumer.linkIndex :: usedAt step.queueStep.outputToken)
        (step.consumer.conclusion :: ownedAt step.queueStep.outputToken) :=
    Certificate.OccurrenceDerivation.ofQueueParStep step.queueStep
      activeFacts.1.derivation step.consumer.linkIndex step.submitted_par
  have eventLeftRegion :
      SourceLeftRegionVertex certificate step.consumer.conclusion
        event.search.result.left :=
    event.leftEndpoint_sourceLeftRegion_of_touched touched
  have eventLeftOutputOwned :
      event.search.result.left ∈
        step.consumer.conclusion :: ownedAt step.queueStep.outputToken :=
    outputDerivation.sourceLeftRegion_owned invariant.structural
      (by simp) eventLeftRegion
  have eventAxiomMembership :
      Link.axiom event.search.result.left event.search.result.right ∈
        certificate.links :=
    List.mem_of_getElem? event.search.result.exactLink
  have forwardParMembership :
      Link.par step.consumer.storedLeft step.consumer.storedRight
          step.consumer.conclusion ∈ certificate.links :=
    List.mem_of_getElem? step.submitted_par
  have eventLeftNeConclusion :
      event.search.result.left ≠ step.consumer.conclusion := by
    intro same
    exact invariant.structural.axiomEndpoint_ne_connectiveConclusion
      eventAxiomMembership (Or.inl rfl) forwardParMembership
      (by simpa [Link.produces] using same.symm)
  have eventLeftActiveOwned :
      event.search.result.left ∈ ownedAt step.queueStep.outputToken := by
    rcases List.mem_cons.mp eventLeftOutputOwned with same | membership
    · exact False.elim (eventLeftNeConclusion same)
    · exact membership
  have olderBefore :
      before.core.representative event.rawAge <
        before.core.representative step.prepared.stackResult.rawAge := by
    rw [← step.prepared.after_representative_eq_before event.rawAge,
      ← step.prepared.after_representative_eq_before
        step.prepared.stackResult.rawAge]
    exact older
  have activeBeforeRoot :
      before.core.representative step.prepared.stackResult.rawAge =
        step.queueStep.outputToken := by
    rw [← step.prepared.after_representative_eq_before
      step.prepared.stackResult.rawAge]
    change
      step.prepared.coreMarked.representative
          step.prepared.stackResult.rawAge = step.queueStep.outputToken
    simpa [step.output_token_eq_active] using activeRoot
  have differentSlots :
      before.core.representative event.rawAge ≠
        step.queueStep.outputToken := by
    intro same
    rw [← activeBeforeRoot] at same
    exact (Nat.ne_of_lt olderBefore) same
  have ownedDisjoint :=
    (separated eventLookup activeBeforeLookup differentSlots).2
  exact ownedDisjoint event.search.result.left eventLeftForestOwned
    eventLeftActiveOwned

/-- A successful typed `forward` preserves older-event future-work head
separation from structural well-formedness and the supplied prior invariant.

The implicit dispatcher is indexed by the history-derived scheduler invariant;
no explicit scheduler-invariant or created-head premise is required. -/
theorem olderEventFutureWorkTouchSeparated_of_structural
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : ForwardStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderEventFutureWorkTouchSeparated prior)
    (structural : certificate.StructurallyWellFormed)
    {dispatch :
      DispatchStep certificate before (history.schedulerInvariant structural)
        ⟨.forward, after⟩} :
    OlderEventFutureWorkTouchSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.forward step)) :=
  step.olderEventFutureWorkTouchSeparated prior separated
    (step.createdHeadTouchSeparated prior structural)

end ForwardStep
end SequentialFigure7
end ProofNetIR
