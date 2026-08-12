/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveRegionTouchOrder

namespace ProofNetIR

/-!
# Figure-7 active tensor-conclusion touch decomposition

This module isolates the exact structural consequence of a reservation event
touching a future-New tensor conclusion.  Such a touch continues through the
tensor's stored-left premise, so it reaches either the future candidate's mate
or its queued head according to the submitted tensor orientation.

For the active `NewGuard` candidate, the mate alternative contradicts the
existing active source-left-region tag-freshness theorem.  Therefore every
ledger-event touch of the active tensor conclusion must also touch the active
queued head.

Nothing here proves the tensor conclusion untouched, excludes raw marks,
constructs a target-avoiding path, or establishes scheduler progress,
totality, or worklist completeness.
-/

namespace SequentialFigure7

open SequentialUnification
open SequentialSchedulerBridge
open SequentialSchedulerState

private theorem sourceLeftReachable_trans
    {certificate : Certificate} {first middle last : Vertex}
    (firstPath : SourceLeftReachable certificate first middle)
    (suffix : SourceLeftReachable certificate middle last) :
    SourceLeftReachable certificate first last := by
  induction firstPath with
  | refl => exact suffix
  | step head tail induction => exact .step head (induction suffix)

private theorem ReservationEvent.touched_tensor_storedLeft
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (event : ReservationEvent certificate)
    {tensor : TensorBelow} {head : Vertex}
    (valid : tensor.Valid certificate certificate.consumerIndex head)
    (touched : event.Touched tensor.conclusion) :
    event.Touched tensor.storedLeft := by
  apply event.sourceLeftRegion_touched structural
  have conclusionRegion :
      SourceLeftRegionVertex certificate event.start tensor.conclusion :=
    event.touched_sourceLeftRegion touched
  cases conclusionRegion with
  | visited reachable =>
      exact .visited (sourceLeftReachable_trans reachable
        (.step (.tensor valid.2.1) (.refl tensor.storedLeft)))
  | @terminalPartner reached _partner linkIndex reachable exactAxiom =>
      have tensorMembership :
          Link.tensor tensor.storedLeft tensor.storedRight tensor.conclusion ∈
            certificate.links :=
        List.mem_of_getElem? valid.2.1
      exfalso
      rcases exactAxiom with axiomEq | axiomEq
      · exact structural.axiomEndpoint_ne_connectiveConclusion
          (List.mem_of_getElem? axiomEq) (Or.inr rfl) tensorMembership
          (by simp [Link.produces])
      · exact structural.axiomEndpoint_ne_connectiveConclusion
          (List.mem_of_getElem? axiomEq) (Or.inl rfl) tensorMembership
          (by simp [Link.produces])

/-- Touching a future candidate's tensor conclusion forces a touch of either
the candidate mate or its queued head, according to stored orientation. -/
theorem ReservationEvent.touched_candidateConclusion_cases
    {certificate : Certificate} {state : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (event : ReservationEvent certificate)
    (candidate : FutureNewCandidateAt certificate state)
    (touched : event.Touched candidate.tensor.conclusion) :
    event.Touched candidate.tensor.mate ∨
      event.Touched candidate.head := by
  have storedLeftTouched := event.touched_tensor_storedLeft structural
    candidate.tensor_valid touched
  cases sideEquation : candidate.tensor.side with
  | storedLeft =>
      right
      have headEq : candidate.head = candidate.tensor.storedLeft := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using candidate.tensor_valid.2.2.2
      simpa [headEq] using storedLeftTouched
  | storedRight =>
      left
      simpa [TensorBelow.mate, TensorPremiseSide.mate,
        sideEquation] using storedLeftTouched

private theorem CanonicalTagHistory.touched_of_reservationLedger_event
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {event : ReservationEvent certificate} {vertex : Vertex}
    (membership : event ∈ tagHistory.reservationLedger)
    (touched : event.Touched vertex) :
    tagHistory.Touched vertex := by
  induction tagHistory with
  | empty => simp [CanonicalTagHistory.reservationLedger] at membership
  | init step =>
      simp only [CanonicalTagHistory.reservationLedger,
        List.mem_singleton] at membership
      subst event
      exact touched
  | later prior evidence induction =>
      simp only [CanonicalTagHistory.reservationLedger,
        List.mem_append] at membership
      rcases membership with old | current
      · exact Or.inl (induction old)
      · right
        cases evidence with
        | concl step => simp [DispatchTagEvidence.reservationEvents] at current
        | nop step => simp [DispatchTagEvidence.reservationEvents] at current
        | new step =>
            simp only [DispatchTagEvidence.reservationEvents,
              List.mem_singleton] at current
            subst event
            exact touched
        | wait step => simp [DispatchTagEvidence.reservationEvents] at current
        | forward step => simp [DispatchTagEvidence.reservationEvents] at current
        | unifyPayload step =>
            simp [DispatchTagEvidence.reservationEvents] at current

/-- For the active candidate, every chronological ledger-event touch of the
tensor conclusion also touches the queued head.  The mate alternative is
excluded by active source-left-region tag freshness, including for the
same-boundary event not covered by a strict older-event callback.  This does
not prove the conclusion untouched; it leaves the head-touch alternative
explicit. -/
theorem CanonicalTagHistory.active_conclusion_touch_implies_head_touch
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (separated : OlderEventTouchSeparated tagHistory)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger)
    (conclusionTouched : event.Touched guard.tensor.conclusion) :
    event.Touched guard.head.vertex := by
  let candidate := guard.futureNewCandidateAt invariant
  rcases event.touched_candidateConclusion_cases invariant.structural candidate
      conclusionTouched with mateTouched | headTouched
  · have mateFresh : before.tags[guard.tensor.mate]? = some false :=
      tagHistory.active_sourceLeftRegion_tagFresh_of_olderEventTouchSeparated
        correct invariant guard separated (.visited (.refl guard.tensor.mate))
    have mateGloballyTouched : tagHistory.Touched guard.tensor.mate :=
      tagHistory.touched_of_reservationLedger_event membership mateTouched
    have mateTrue : before.tags[guard.tensor.mate]? = some true :=
      tagHistory.tagged_iff_touched.2 mateGloballyTouched
    rw [mateTrue] at mateFresh
    contradiction
  · exact headTouched

end SequentialFigure7

end ProofNetIR
