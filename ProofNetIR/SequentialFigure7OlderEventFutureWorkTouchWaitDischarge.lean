/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchWaitPreservation
import ProofNetIR.SequentialComponentSourceLeftGeometry

/-!
# Figure-7 wait discharge of the created-head touch seam

For an already-successful typed `wait` step, structural well-formedness and
the canonical history force every strictly older reservation event away from
the inserted par conclusion.  A touch through that conclusion continues
through the submitted par's stored-left premise.  That premise is either the
selected occurrence or its already-marked mate, so the middle component
forest assigns it to a live slot strictly newer than the event slot.  Exact
live-slot disjointness then excludes the touch.

The direct corollary feeds this result to the existing conditional `wait`
preservation theorem.  It still requires the supplied prior separation
invariant.  This module proves no source-region or raw seam, global
availability, progress, totality, completeness, fallback removal, or
complexity result.
-/

namespace ProofNetIR

namespace SequentialUnification
namespace SourceLeftRegionVertex

/-- Removing the exact first submitted par step from a source-left region
witness leaves a region rooted at its stored-left premise.  This local helper
is kept private until another rule needs the same decomposition. -/
private theorem dropPar
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {linkIndex : Nat} {left right conclusion vertex : Vertex}
    (exactPar :
      certificate.links[linkIndex]? = some (.par left right conclusion))
    (region : SourceLeftRegionVertex certificate conclusion vertex)
    (ne : vertex ≠ conclusion) :
    SourceLeftRegionVertex certificate left vertex := by
  cases region with
  | visited reachable =>
      cases reachable with
      | refl => exact False.elim (ne rfl)
      | step head tail =>
          cases head with
          | tensor exactOther =>
              have same :=
                UnificationState.StructurallyWellFormed.producerLink_unique
                  (conclusion := conclusion) structural
                  (List.mem_of_getElem? exactPar) (by simp [Link.produces])
                  (List.mem_of_getElem? exactOther) (by simp [Link.produces])
              cases same
          | par exactOther =>
              have same :=
                UnificationState.StructurallyWellFormed.producerLink_unique
                  (conclusion := conclusion) structural
                  (List.mem_of_getElem? exactPar) (by simp [Link.produces])
                  (List.mem_of_getElem? exactOther) (by simp [Link.produces])
              cases same
              exact .visited tail
  | @terminalPartner reached partner axiomIndex reachable exactAxiom =>
      cases reachable with
      | refl =>
          exfalso
          have parMembership :
              Link.par left right conclusion ∈ certificate.links :=
            List.mem_of_getElem? exactPar
          rcases exactAxiom with axiomEq | axiomEq
          · exact structural.axiomEndpoint_ne_connectiveConclusion
              (List.mem_of_getElem? axiomEq) (Or.inl rfl) parMembership
              (by simp [Link.produces])
          · exact structural.axiomEndpoint_ne_connectiveConclusion
              (List.mem_of_getElem? axiomEq) (Or.inr rfl) parMembership
              (by simp [Link.produces])
      | step head tail =>
          cases head with
          | tensor exactOther =>
              have same :=
                UnificationState.StructurallyWellFormed.producerLink_unique
                  (conclusion := conclusion) structural
                  (List.mem_of_getElem? exactPar) (by simp [Link.produces])
                  (List.mem_of_getElem? exactOther) (by simp [Link.produces])
              cases same
          | par exactOther =>
              have same :=
                UnificationState.StructurallyWellFormed.producerLink_unique
                  (conclusion := conclusion) structural
                  (List.mem_of_getElem? exactPar) (by simp [Link.produces])
                  (List.mem_of_getElem? exactOther) (by simp [Link.produces])
              cases same
              exact .terminalPartner tail exactAxiom

end SourceLeftRegionVertex
end SequentialUnification

namespace SequentialFigure7

open SequentialUnification
open SequentialSchedulerBridge
open SequentialSchedulerState

namespace WaitStep

/-- Every strictly older prior ledger event leaves the par conclusion
inserted by a successful typed `wait` step untouched. -/
theorem createdHeadTouchSeparated
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : WaitStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed) :
    WaitCreatedHeadTouchSeparated prior step := by
  have invariant : SchedulerInvariant certificate before :=
    history.schedulerInvariant structural
  have middleInvariant := step.prepared.schedulerInvariant invariant
  intro event eventMembership _created older touched
  rcases prior.reservationLedger_axiomEndpoints_accounted
      structural eventMembership with
    ⟨eventComponent, eventUsed, eventForestUsed, eventOwned,
      eventLookup, eventDerivation, eventLink, eventWitness,
      eventAccounted, eventLeftOwned, eventRightOwned⟩
  rcases middleInvariant.component_forest_provenance with
    ⟨usedAt, ownedAt, live, separated, markedOwned⟩
  have componentsEq :
      step.prepared.after.core.components = before.core.components :=
    (UnificationState.markReadyRaw?_exact
      step.prepared.core_mark_eq).2.2.2.1
  have eventMiddleLookup :
      step.prepared.after.core.components[
          step.prepared.after.core.representative event.rawAge]? =
        some (some eventComponent) := by
    rw [step.prepared.after_representative_eq_before event.rawAge,
      componentsEq]
    exact eventLookup
  have eventFacts := live eventMiddleLookup
  have eventOwnedEq :
      eventOwned =
        ownedAt (step.prepared.after.core.representative event.rawAge) :=
    Certificate.OccurrenceDerivation.owned_unique structural
      eventDerivation eventFacts.1.derivation
  have eventLeftForestOwned :
      event.search.result.left ∈
        ownedAt (step.prepared.after.core.representative event.rawAge) := by
    rw [← eventOwnedEq]
    exact eventLeftOwned
  have eventLeftRegionFromConclusion :
      SourceLeftRegionVertex certificate step.consumer.conclusion
        event.search.result.left :=
    event.leftEndpoint_sourceLeftRegion_of_touched touched
  have eventLeftNeConclusion :
      event.search.result.left ≠ step.consumer.conclusion := by
    intro same
    have eventAxiomMembership :
        Link.axiom event.search.result.left event.search.result.right ∈
          certificate.links :=
      List.mem_of_getElem? event.search.result.exactLink
    have waitParMembership :
        Link.par step.consumer.storedLeft step.consumer.storedRight
            step.consumer.conclusion ∈ certificate.links :=
      List.mem_of_getElem? step.submitted_par
    exact structural.axiomEndpoint_ne_connectiveConclusion
      eventAxiomMembership (Or.inl rfl) waitParMembership
      (by simpa [Link.produces] using same.symm)
  have eventLeftRegion :
      SourceLeftRegionVertex certificate step.consumer.storedLeft
        event.search.result.left :=
    SourceLeftRegionVertex.dropPar structural step.submitted_par
      eventLeftRegionFromConclusion eventLeftNeConclusion
  have selectedMarked :
      step.prepared.after.core.marks[step.prepared.stackResult.vertex]? =
        some (some step.prepared.stackResult.rawAge) :=
    (UnificationState.markReadyRaw?_exact
      step.prepared.core_mark_eq).2.2.2.2.2.2
  have mateMarked :
      step.prepared.after.core.marks[step.consumer.mate]? =
        some (some step.mateRawAge) :=
    step.mate_marked
  rcases markedOwned selectedMarked with
    ⟨selectedIndex, selectedComponent, selectedRep,
      selectedLookup, selectedOwned⟩
  rcases markedOwned mateMarked with
    ⟨mateIndex, mateComponent, mateRep, mateLookup, mateOwned⟩
  have selectedFacts := live selectedLookup
  have mateFacts := live mateLookup
  have selectedAgeBound :
      step.prepared.stackResult.rawAge <
        step.prepared.after.stack.nextAge := by
    have stackMarked :
        step.prepared.after.stack.marks[
            step.prepared.stackResult.vertex]? =
          some (some step.prepared.stackResult.rawAge) := by
      rw [← middleInvariant.realizesSigma.marks_eq]
      exact selectedMarked
    exact middleInvariant.stack_wellShaped.assigned_age_bound
      step.prepared.stackResult.vertex
      step.prepared.stackResult.rawAge stackMarked
  have selectedSigmaTop :
      step.prepared.after.stack.sigma.getLast? =
        some step.prepared.stackResult.rawAge := by
    rcases SequentialStackState.popReadyMark?_exact
        step.prepared.stack_eq with
      ⟨_topReady, sigmaTop, _unmarked, _marks, _nextAge, sigmaEq,
        _ready, _waiting, _marked⟩
    change step.prepared.stackResult.after.sigma.getLast? =
      some step.prepared.stackResult.rawAge
    rw [sigmaEq]
    exact sigmaTop
  have selectedBoundaryLookup :
      sigmaBoundary? step.prepared.after.stack.sigma
          step.prepared.stackResult.rawAge =
        some step.prepared.stackResult.rawAge :=
    middleInvariant.stack_wellShaped.sigma_partition
      |>.sigmaBoundary?_eq_top selectedSigmaTop
  have selectedRoot :
      step.prepared.after.core.representative
          step.prepared.stackResult.rawAge =
        step.prepared.stackResult.rawAge := by
    have realized :=
      middleInvariant.realizesSigma.representative_eq_boundary
        selectedAgeBound
    exact Option.some.inj (realized.symm.trans selectedBoundaryLookup)
  have mateAgeBound :
      step.mateRawAge < step.prepared.after.stack.nextAge := by
    have stackMarked :
        step.prepared.after.stack.marks[step.consumer.mate]? =
          some (some step.mateRawAge) := by
      rw [← middleInvariant.realizesSigma.marks_eq]
      exact mateMarked
    exact middleInvariant.stack_wellShaped.assigned_age_bound
      step.consumer.mate step.mateRawAge stackMarked
  have mateRootAtBoundary :
      step.prepared.after.core.representative step.mateRawAge =
        step.destination.boundary := by
    have realized :=
      middleInvariant.realizesSigma.representative_eq_boundary mateAgeBound
    exact Option.some.inj
      (realized.symm.trans step.destination.boundary_eq)
  have mateParentBound :
      step.mateRawAge < step.prepared.after.core.parents.size := by
    rw [middleInvariant.realizesSigma.horizon_eq]
    exact mateAgeBound
  have destinationRoot :
      step.prepared.after.core.representative step.destination.boundary =
        step.destination.boundary := by
    have idempotent :=
      middleInvariant.core_abstractable.representativeIdempotent
        mateParentBound
    rw [mateRootAtBoundary] at idempotent
    exact idempotent
  have olderAtBoundary :
      step.prepared.after.core.representative event.rawAge <
        step.destination.boundary := by
    rw [destinationRoot] at older
    exact older
  have boundaryLtSelected :
      step.destination.boundary < step.prepared.stackResult.rawAge :=
    Nat.lt_of_le_of_lt (sigmaBoundary?_le step.destination.boundary_eq)
      step.younger
  have eventNeSelected :
      step.prepared.after.core.representative event.rawAge ≠
        selectedIndex := by
    intro same
    rw [← selectedRep, selectedRoot] at same
    rw [same] at olderAtBoundary
    exact (Nat.not_lt_of_ge (Nat.le_of_lt boundaryLtSelected))
      olderAtBoundary
  have mateIndexEq : mateIndex = step.destination.boundary :=
    mateRep.symm.trans mateRootAtBoundary
  have eventNeMate :
      step.prepared.after.core.representative event.rawAge ≠ mateIndex := by
    intro same
    rw [mateIndexEq] at same
    exact (Nat.ne_of_lt olderAtBoundary) same
  cases sideEquation : step.consumer.side with
  | storedLeft =>
      have storedLeftEq :
          step.consumer.storedLeft =
            step.prepared.stackResult.vertex := by
        have selectedEq :
            step.prepared.stackResult.vertex =
              step.consumer.storedLeft := by
          simpa [TensorPremiseSide.premise, sideEquation] using
            step.consumer.premise_eq
        exact selectedEq.symm
      have eventLeftSelectedOwned :
          event.search.result.left ∈ ownedAt selectedIndex :=
        selectedFacts.1.derivation.sourceLeftRegion_owned structural
          selectedOwned (by simpa [storedLeftEq] using eventLeftRegion)
      have disjoint :=
        (separated eventMiddleLookup selectedLookup eventNeSelected).2
      exact disjoint event.search.result.left eventLeftForestOwned
        eventLeftSelectedOwned
  | storedRight =>
      have storedLeftEq :
          step.consumer.storedLeft = step.consumer.mate := by
        simp [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEquation]
      have eventLeftMateOwned :
          event.search.result.left ∈ ownedAt mateIndex :=
        mateFacts.1.derivation.sourceLeftRegion_owned structural mateOwned
          (by simpa [storedLeftEq] using eventLeftRegion)
      have disjoint :=
        (separated eventMiddleLookup mateLookup eventNeMate).2
      exact disjoint event.search.result.left eventLeftForestOwned
        eventLeftMateOwned

/-- A successful typed `wait` preserves older-event future-work head
separation from structural well-formedness and the supplied prior invariant.

The implicit dispatcher is indexed by the history-derived scheduler invariant;
no explicit scheduler-invariant or created-head premise is required. -/
theorem olderEventFutureWorkTouchSeparated_of_structural
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : WaitStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderEventFutureWorkTouchSeparated prior)
    (structural : certificate.StructurallyWellFormed)
    {dispatch :
      DispatchStep certificate before (history.schedulerInvariant structural)
        ⟨.wait, after⟩} :
    OlderEventFutureWorkTouchSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.wait step)) :=
  step.olderEventFutureWorkTouchSeparated prior separated
    (step.createdHeadTouchSeparated prior structural)

end WaitStep
end SequentialFigure7
end ProofNetIR
