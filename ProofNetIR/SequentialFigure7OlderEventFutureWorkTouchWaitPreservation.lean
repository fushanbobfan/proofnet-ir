/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchSeparation
import ProofNetIR.SequentialFigure7CrossRepresentativeWaitPreservation

namespace ProofNetIR

/-!
# Figure-7 wait preservation of older-event future-work head separation

A successful `wait` keeps the chronological reservation ledger fixed.  Every
output future-work occurrence is either inherited from the synchronized
prepared state or is the par conclusion prepended at the exact waiting
destination.  The inherited branch transports the prior separation invariant.
The inserted conclusion requires the explicit transition-local premise below.

This module does not derive that premise from scheduler or history invariants,
and it proves no unconditional `wait` preservation, global availability,
target-path construction, raw separation, enabledness, progress, totality, or
completeness result.
-/

namespace SequentialFigure7

open SequentialSchedulerBridge

/-- Every strictly older prior ledger event leaves the exact conclusion
inserted by a successful `wait` untouched.

This is only the residual old-event/inserted-head obligation.  It does not
repeat the inherited-candidate cases covered by the prior invariant. -/
def WaitCreatedHeadTouchSeparated
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (prior : CanonicalTagHistory certificate history)
    (step : WaitStep certificate before after) : Prop :=
  ∀ {event : ReservationEvent certificate},
    event ∈ prior.reservationLedger →
    ∀ _created : WaitCreatedCandidate certificate step,
      step.prepared.after.core.representative event.rawAge <
          step.prepared.after.core.representative
            step.destination.boundary →
        ¬ event.Touched step.consumer.conclusion

namespace WaitStep

/-- A canonical `wait` extension preserves older-event future-work head-touch
separation when its newly inserted conclusion satisfies the explicit residual
touch premise.

The theorem applies to an already-successful typed `WaitStep`.  It does not
derive `WaitCreatedHeadTouchSeparated`, handle the other candidate-creating
rules, discharge a raw or source-region seam, or establish scheduler progress.
-/
theorem olderEventFutureWorkTouchSeparated
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.wait, after⟩}
    (step : WaitStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderEventFutureWorkTouchSeparated prior)
    (createdSeparated : WaitCreatedHeadTouchSeparated prior step) :
    OlderEventFutureWorkTouchSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.wait step)) := by
  refine { event_candidate := ?_ }
  intro event eventMembership candidate older
  have oldEventMembership : event ∈ prior.reservationLedger := by
    simpa [CanonicalTagHistory.reservationLedger,
      DispatchTagEvidence.reservationEvents] using eventMembership
  rcases candidate.work.beforeWaitOrInserted step with
    oldWork | ⟨candidateAge, candidateHead⟩
  · let middleCandidate :
        FutureNewCandidateAt certificate step.prepared.after := {
      rawAge := candidate.rawAge
      head := candidate.head
      work := oldWork
      tensor := candidate.tensor
      tensor_valid := candidate.tensor_valid
      mate_unmarked := by
        have mateUnmarked := candidate.mate_unmarked
        rcases step.destination.exact with
          ⟨_payload, _initialized, _updated, _marks, _nextAge, _sigma,
            _ready, coreEquation, _tags⟩
        rw [coreEquation] at mateUnmarked
        exact mateUnmarked }
    let beforeCandidate : FutureNewCandidateAt certificate before :=
      middleCandidate.beforePrepared step.prepared
    have olderBefore :
        before.core.representative event.rawAge <
          before.core.representative beforeCandidate.rawAge := by
      change
        before.core.representative event.rawAge <
          before.core.representative candidate.rawAge
      rw [← step.prepared.after_representative_eq_before event.rawAge,
        ← step.prepared.after_representative_eq_before candidate.rawAge,
        ← step.destination.after_representative_eq_before event.rawAge,
        ← step.destination.after_representative_eq_before candidate.rawAge]
      exact older
    have oldUntouched := separated.event_candidate oldEventMembership
      beforeCandidate olderBefore
    simpa [beforeCandidate, middleCandidate,
      FutureNewCandidateAt.beforePrepared] using oldUntouched
  · have olderMiddle :
        step.prepared.after.core.representative event.rawAge <
          step.prepared.after.core.representative
            step.destination.boundary := by
      rw [← candidateAge]
      rw [← step.destination.after_representative_eq_before event.rawAge,
        ← step.destination.after_representative_eq_before candidate.rawAge]
      exact older
    let created : WaitCreatedCandidate certificate step := {
      tensor := candidate.tensor
      tensor_valid := by
        rw [← candidateHead]
        exact candidate.tensor_valid
      mate_unmarked := by
        have mateUnmarked := candidate.mate_unmarked
        rcases step.destination.exact with
          ⟨_payload, _initialized, _updated, _marks, _nextAge, _sigma,
            _ready, coreEquation, _tags⟩
        rw [coreEquation] at mateUnmarked
        exact mateUnmarked }
    intro touched
    exact createdSeparated oldEventMembership created olderMiddle
      (by simpa [candidateHead] using touched)

end WaitStep

end SequentialFigure7

end ProofNetIR
