/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchUnifyPayloadPreservation
import ProofNetIR.SequentialComponentSourceLeftGeometry

/-!
# Figure-7 UnifyPayload discharge of the created-head touch seam

For an already-successful typed `unifyPayload` step, the exact tensor queue
joins the previous and active live components. A strictly older reservation
event belongs to neither input slot. If that event touched the inserted tensor
conclusion, source-left carrier closure would nevertheless put its stored-left
axiom endpoint in one of those two slots, contradicting component-forest
disjointness.

The direct corollary feeds this result to the existing conditional
`unifyPayload` preservation theorem. It still requires the supplied prior
older-event future-work head-separation invariant. This module proves no
source-region or raw seam, global availability, progress, totality,
completeness, fallback removal, or complexity result.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialUnification
open SequentialSchedulerBridge

namespace UnifyPayloadStep

/-- Every strictly older prior ledger event leaves the tensor conclusion
inserted by a successful typed `unifyPayload` step untouched. -/
theorem createdHeadTouchSeparated
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : UnifyPayloadStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed) :
    UnifyPayloadCreatedHeadTouchSeparated prior step := by
  have invariant : SchedulerInvariant certificate before :=
    history.schedulerInvariant structural
  intro event eventMembership _created older touched
  rcases prior.reservationLedger_axiomEndpoints_accounted
      structural eventMembership with
    ⟨eventComponent, eventUsed, eventForestUsed, eventOwned,
      eventLookup, eventDerivation, eventLink, eventWitness,
      eventAccounted, eventLeftOwned, eventRightOwned⟩
  rcases invariant.component_forest_provenance with
    ⟨usedAt, ownedAt, live, forestSeparated, markedOwned⟩
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
    UnificationState.unifyTokens?_success step.tensorStep.token_guard
  have leftRoot :
      step.prepared.coreMarked.representative step.tensorStep.leftToken =
        step.tensorStep.leftToken :=
    middleInvariant.core_abstractable.tokenAt?_root tokenGuards.2.1
  have rightRoot :
      step.prepared.coreMarked.representative step.tensorStep.rightToken =
        step.tensorStep.rightToken :=
    middleInvariant.core_abstractable.tokenAt?_root tokenGuards.2.2.1
  have leftMiddleLookup :
      step.prepared.coreMarked.components[step.tensorStep.leftToken]? =
        some (some step.tensorStep.leftComponent) := by
    have raw := UnificationState.componentAt?_some_raw
      step.tensorStep.left_component
    simpa [leftRoot] using raw
  have rightMiddleLookup :
      step.prepared.coreMarked.components[step.tensorStep.rightToken]? =
        some (some step.tensorStep.rightComponent) := by
    have raw := UnificationState.componentAt?_some_raw
      step.tensorStep.right_component
    simpa [rightRoot] using raw
  have componentsEq :
      step.prepared.coreMarked.components = before.core.components :=
    (UnificationState.markReadyRaw?_exact
      step.prepared.core_mark_eq).2.2.2.1
  have leftBeforeLookup :
      before.core.components[step.tensorStep.leftToken]? =
        some (some step.tensorStep.leftComponent) := by
    rw [← componentsEq]
    exact leftMiddleLookup
  have rightBeforeLookup :
      before.core.components[step.tensorStep.rightToken]? =
        some (some step.tensorStep.rightComponent) := by
    rw [← componentsEq]
    exact rightMiddleLookup
  have leftFacts := live leftBeforeLookup
  have rightFacts := live rightBeforeLookup
  have outputDerivation :
      certificate.OccurrenceDerivation
        (.tensor step.tensorStep.leftFocus step.tensorStep.rightFocus
          step.tensorStep.leftComponent.tree
          step.tensorStep.rightComponent.tree)
        (step.consumer.conclusion ::
          (step.tensorStep.leftContext ++ step.tensorStep.rightContext))
        (step.consumer.linkIndex ::
          (usedAt step.tensorStep.leftToken ++
            usedAt step.tensorStep.rightToken))
        (step.consumer.conclusion ::
          (ownedAt step.tensorStep.leftToken ++
            ownedAt step.tensorStep.rightToken)) :=
    Certificate.OccurrenceDerivation.ofQueueTensorStep step.tensorStep
      leftFacts.1.derivation rightFacts.1.derivation
      step.consumer.linkIndex step.submitted_tensor
  have eventLeftRegion :
      SourceLeftRegionVertex certificate step.consumer.conclusion
        event.search.result.left :=
    event.leftEndpoint_sourceLeftRegion_of_touched touched
  have eventLeftOutputOwned :
      event.search.result.left ∈
        step.consumer.conclusion ::
          (ownedAt step.tensorStep.leftToken ++
            ownedAt step.tensorStep.rightToken) :=
    outputDerivation.sourceLeftRegion_owned invariant.structural
      (by simp) eventLeftRegion
  have eventAxiomMembership :
      Link.axiom event.search.result.left event.search.result.right ∈
        certificate.links :=
    List.mem_of_getElem? event.search.result.exactLink
  have tensorMembership :
      Link.tensor step.consumer.storedLeft step.consumer.storedRight
          step.consumer.conclusion ∈ certificate.links :=
    List.mem_of_getElem? step.submitted_tensor
  have eventLeftNeConclusion :
      event.search.result.left ≠ step.consumer.conclusion := by
    intro same
    exact invariant.structural.axiomEndpoint_ne_connectiveConclusion
      eventAxiomMembership (Or.inl rfl) tensorMembership
      (by simpa [Link.produces] using same.symm)
  have previousLtActive :
      step.previousBoundary < step.prepared.stackResult.rawAge :=
    Nat.lt_of_le_of_lt step.lower step.upper
  have previousRoot :
      step.prepared.coreMarked.representative step.previousBoundary =
        step.previousBoundary := by
    rcases step.tokens_eq_adjacent with orientation | orientation
    · rw [← orientation.2.2]
      exact rightRoot
    · rw [← orientation.2.1]
      exact leftRoot
  have eventOlderPrevious :
      before.core.representative event.rawAge < step.previousBoundary := by
    calc
      before.core.representative event.rawAge =
          step.prepared.after.core.representative event.rawAge :=
        (step.prepared.after_representative_eq_before event.rawAge).symm
      _ < step.prepared.after.core.representative step.previousBoundary :=
        older
      _ = step.previousBoundary := by
        simpa [PreparedStep.after] using previousRoot
  have differentLeft :
      before.core.representative event.rawAge ≠
        step.tensorStep.leftToken := by
    intro same
    rcases step.tokens_eq_adjacent with orientation | orientation
    · rw [orientation.2.1] at same
      rw [same] at eventOlderPrevious
      exact (Nat.not_lt_of_ge (Nat.le_of_lt previousLtActive))
        eventOlderPrevious
    · rw [orientation.2.1] at same
      exact (Nat.ne_of_lt eventOlderPrevious) same
  have differentRight :
      before.core.representative event.rawAge ≠
        step.tensorStep.rightToken := by
    intro same
    rcases step.tokens_eq_adjacent with orientation | orientation
    · rw [orientation.2.2] at same
      exact (Nat.ne_of_lt eventOlderPrevious) same
    · rw [orientation.2.2] at same
      rw [same] at eventOlderPrevious
      exact (Nat.not_lt_of_ge (Nat.le_of_lt previousLtActive))
        eventOlderPrevious
  rcases List.mem_cons.mp eventLeftOutputOwned with same | membership
  · exact False.elim (eventLeftNeConclusion same)
  · rcases List.mem_append.mp membership with leftOwned | rightOwned
    · have disjoint :=
        (forestSeparated eventLookup leftBeforeLookup differentLeft).2
      exact disjoint event.search.result.left eventLeftForestOwned leftOwned
    · have disjoint :=
        (forestSeparated eventLookup rightBeforeLookup differentRight).2
      exact disjoint event.search.result.left eventLeftForestOwned rightOwned

/-- A successful typed `unifyPayload` preserves older-event future-work head
separation from structural well-formedness and the supplied prior invariant.

The implicit dispatcher is indexed by the history-derived scheduler invariant;
no explicit scheduler-invariant or created-head premise is required. -/
theorem olderEventFutureWorkTouchSeparated_of_structural
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : UnifyPayloadStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderEventFutureWorkTouchSeparated prior)
    (structural : certificate.StructurallyWellFormed)
    {dispatch :
      DispatchStep certificate before (history.schedulerInvariant structural)
        ⟨.unifyPayload, after⟩} :
    OlderEventFutureWorkTouchSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.unifyPayload step)) :=
  step.olderEventFutureWorkTouchSeparated prior separated
    (step.createdHeadTouchSeparated prior structural)

end UnifyPayloadStep
end SequentialFigure7
end ProofNetIR
