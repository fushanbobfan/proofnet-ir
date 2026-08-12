/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchSeparation
import ProofNetIR.SequentialFigure7CrossRepresentativeNewPreservation

namespace ProofNetIR

/-!
# Figure-7 New preservation of older-event future-work touch separation

A successful `new` preserves queued-head touch separation without a created-
region geometry premise. Old events and retained candidates transport through
the prepared prefix. An old event cannot touch a newly appended endpoint,
because the same endpoint is touched by the current `NEXTAXIOM` search and
canonical tag history separates all current touches from earlier ones. The
fresh event is not strictly older than any output candidate.

This module proves only conditional preservation across an already-successful
typed `new` step. It does not establish same-boundary separation, global
history availability, dispatcher progress, totality, or completeness.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

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
        | forward step =>
            simp [DispatchTagEvidence.reservationEvents] at current
        | unifyPayload step =>
            simp [DispatchTagEvidence.reservationEvents] at current

private theorem NewStep.search_touched_of_endpoint
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    {vertex : Vertex}
    (endpoint : vertex = step.reached ∨ vertex = step.partner) :
    step.search.Touched vertex := by
  rcases endpoint with rfl | rfl
  · rcases step.route.storedEndpoints with
      ⟨reachedEq, _partnerEq⟩ | ⟨reachedEq, _partnerEq⟩
    · exact Or.inr (Or.inl reachedEq)
    · exact Or.inr (Or.inr reachedEq)
  · rcases step.route.storedEndpoints with
      ⟨_reachedEq, partnerEq⟩ | ⟨_reachedEq, partnerEq⟩
    · exact Or.inr (Or.inr partnerEq)
    · exact Or.inr (Or.inl partnerEq)

namespace NewStep

/-- A canonical `new` extension preserves strictly older ledger-event
separation from every output future-work head.

No created-region premise is needed: the only new heads are the current
search's reached and partner endpoints, whose current touches are disjoint
from every touch already recorded by the prior canonical history. This is
successful-step preservation, not a same-boundary or global-availability
result. It does not derive the prior invariant, handle Wait/Forward/UnifyPayload,
discharge a raw seam, or establish enabledness or progress. -/
theorem olderEventFutureWorkTouchSeparated
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.new, after⟩}
    (step : NewStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderEventFutureWorkTouchSeparated prior) :
    OlderEventFutureWorkTouchSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.new step)) := by
  refine { event_candidate := ?_ }
  intro event eventMembership candidate older
  simp only [CanonicalTagHistory.reservationLedger,
    DispatchTagEvidence.reservationEvents, List.mem_append,
    List.mem_singleton] at eventMembership
  rcases eventMembership with oldEventMembership | freshEvent
  · rcases candidate.work.beforeNewOrInserted step with
      oldWork | ⟨_candidateAge, candidateHead⟩
    · let middleCandidate :
          FutureNewCandidateAt certificate step.markedMiddle := {
        rawAge := candidate.rawAge
        head := candidate.head
        work := oldWork
        tensor := candidate.tensor
        tensor_valid := candidate.tensor_valid
        mate_unmarked := by
          have mateUnmarked := candidate.mate_unmarked
          rw [step.after_marks_eq_markedMiddle] at mateUnmarked
          exact mateUnmarked }
      let beforeCandidate : FutureNewCandidateAt certificate before :=
        middleCandidate.beforePrepared step.preparedPrefix
      have olderBefore :
          before.core.representative event.rawAge <
            before.core.representative beforeCandidate.rawAge := by
        change
          before.core.representative event.rawAge <
            before.core.representative candidate.rawAge
        rw [← step.preparedPrefix.after_representative_eq_before
          event.rawAge]
        rw [← step.preparedPrefix.after_representative_eq_before
          candidate.rawAge]
        change
          step.markedMiddle.core.representative event.rawAge <
            step.markedMiddle.core.representative candidate.rawAge
        rw [← step.after_representative_eq_markedMiddle event.rawAge]
        rw [← step.after_representative_eq_markedMiddle candidate.rawAge]
        exact older
      have oldUntouched := separated.event_candidate oldEventMembership
        beforeCandidate olderBefore
      simpa [beforeCandidate, middleCandidate, preparedPrefix,
        FutureNewCandidateAt.beforePrepared] using oldUntouched
    · intro touched
      have earlierTouched : prior.Touched candidate.head :=
        prior.touched_of_reservationLedger_event oldEventMembership touched
      have currentTouched :
          (DispatchTagEvidence.new step).Touched candidate.head :=
        step.search_touched_of_endpoint candidateHead
      exact prior.touched_disjoint_next (DispatchTagEvidence.new step)
        earlierTouched currentTouched
  · subst event
    exact (step.freshEvent_not_strictly_older invariant candidate older).elim

end NewStep

end SequentialFigure7

end ProofNetIR
