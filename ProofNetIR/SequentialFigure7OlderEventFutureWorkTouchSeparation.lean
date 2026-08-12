/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveConclusionTouch
import ProofNetIR.SequentialFigure7CrossRepresentativeStablePreservation

namespace ProofNetIR

/-!
# Figure-7 older-event future-work touch separation

This module isolates the remaining strict-order branch after tensor-conclusion
touch decomposition.  A new history-indexed invariant says that a strictly
older reservation event does not touch the queued head of any future `new`
candidate.  Together with `OlderEventTouchSeparated`, it excludes a strictly
older event from the candidate tensor conclusion: the structural decomposition
reduces such a touch to the already separated mate or the newly separated head.

The predicate is vacuous for the empty history and, under structural
well-formedness, every exact initialized history.  It transports through the
synchronized prepared prefix and the stable `concl` and `nop` branches.  It is
not derived from declarative correctness, scheduler
invariants, canonical history, or queue provenance.  No preservation through
`new`, `wait`, `forward`, or `unifyPayload`, global availability, target-path
construction, enabledness, progress, totality, or completeness is claimed.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- Every strictly older ledger event leaves every future-New queued head
untouched.

This invariant covers the head alternative left open by
`ReservationEvent.touched_candidateConclusion_cases`; it does not include the
candidate mate region, which remains the separate `OlderEventTouchSeparated`
obligation. -/
structure OlderEventFutureWorkTouchSeparated
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history) : Prop where
  /-- A strictly older authentic event does not touch the candidate's exact
  queued head occurrence. -/
  event_candidate :
    ∀ {event : ReservationEvent certificate},
      event ∈ tagHistory.reservationLedger →
      ∀ candidate : FutureNewCandidateAt certificate state,
        state.core.representative event.rawAge <
            state.core.representative candidate.rawAge →
          ¬ event.Touched candidate.head

namespace OlderEventTouchSeparated

/-- Mate-region separation plus queued-head separation excludes a strictly
older event from the future candidate's tensor conclusion.

This is a pointwise conditional bridge.  It does not establish either input
invariant or provide their global history availability. -/
theorem strict_candidateConclusion_untouched
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (regionSeparated : OlderEventTouchSeparated tagHistory)
    (headSeparated : OlderEventFutureWorkTouchSeparated tagHistory)
    (structural : certificate.StructurallyWellFormed)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger)
    (candidate : FutureNewCandidateAt certificate state)
    (older :
      state.core.representative event.rawAge <
        state.core.representative candidate.rawAge) :
    ¬ event.Touched candidate.tensor.conclusion := by
  intro touched
  rcases event.touched_candidateConclusion_cases structural candidate touched with
    mateTouched | headTouched
  · exact regionSeparated.event_candidate membership candidate older mateTouched
      (.visited (.refl candidate.tensor.mate))
  · exact headSeparated.event_candidate membership candidate older headTouched

end OlderEventTouchSeparated

/-- The exact empty canonical history has no ledger event, so older-event
future-work head-touch separation holds vacuously. -/
theorem empty_olderEventFutureWorkTouchSeparated
    (certificate : Certificate) :
    OlderEventFutureWorkTouchSeparated
      (CanonicalTagHistory.empty :
        CanonicalTagHistory certificate
          (ExecutedHistory.empty : ExecutedHistory certificate
            (ReservationState.empty certificate))) := by
  refine { event_candidate := ?_ }
  intro event membership
  simp [CanonicalTagHistory.reservationLedger] at membership

namespace InitialReservationStep

/-- An exact initialized history has one representative boundary, making the
strict older-event premise impossible for every future-work head. -/
theorem olderEventFutureWorkTouchSeparated
    {certificate : Certificate} {after : ReservationState} {start : Vertex}
    (step : InitialReservationStep certificate after start)
    (structural : certificate.StructurallyWellFormed) :
    OlderEventFutureWorkTouchSeparated (CanonicalTagHistory.init step) := by
  have invariant : SchedulerInvariant certificate after :=
    step.schedulerInvariant structural
  have outputStack :=
    congrArg (fun state : ReservationState ↦ state.stack) step.output_eq
  have stackSigma :=
    (SequentialStackState.initEnqueue?_exact step.stack_eq).2.2.1
  have afterSigma : after.stack.sigma = [0] := by
    exact (congrArg SequentialStackState.sigma outputStack).trans stackSigma
  refine { event_candidate := ?_ }
  intro event membership candidate older
  simp only [CanonicalTagHistory.reservationLedger,
    List.mem_singleton] at membership
  subst event
  have candidateMembership : candidate.rawAge ∈ after.stack.sigma :=
    candidate.work.rawAge_mem_sigma invariant
  rw [afterSigma] at candidateMembership
  have candidateAge : candidate.rawAge = 0 := by
    simpa using candidateMembership
  rw [candidateAge] at older
  exact (Nat.lt_irrefl _ older).elim

end InitialReservationStep

namespace PreparedStep

/-- Queued-head touch separation transports through a synchronized prepared
prefix whenever the output history records the same reservation ledger.

The prefix changes neither representatives nor surviving future-work heads.
The explicit output and ledger equalities prevent this state-only prefix from
manufacturing a history edge. -/
theorem olderEventFutureWorkTouchSeparated
    {certificate : Certificate} {before after : ReservationState}
    (step : PreparedStep before) (outputEquation : after = step.after)
    {beforeHistory : ExecutedHistory certificate before}
    (beforeTags : CanonicalTagHistory certificate beforeHistory)
    (separated : OlderEventFutureWorkTouchSeparated beforeTags)
    {afterHistory : ExecutedHistory certificate after}
    (afterTags : CanonicalTagHistory certificate afterHistory)
    (ledgerEquation :
      afterTags.reservationLedger = beforeTags.reservationLedger) :
    OlderEventFutureWorkTouchSeparated afterTags := by
  subst after
  refine { event_candidate := ?_ }
  intro event eventMembership candidate older touched
  have oldEventMembership : event ∈ beforeTags.reservationLedger := by
    rw [← ledgerEquation]
    exact eventMembership
  let beforeCandidate : FutureNewCandidateAt certificate before :=
    candidate.beforePrepared step
  have olderBefore :
      before.core.representative event.rawAge <
        before.core.representative beforeCandidate.rawAge := by
    change
      before.core.representative event.rawAge <
        before.core.representative candidate.rawAge
    rw [← step.after_representative_eq_before event.rawAge,
      ← step.after_representative_eq_before candidate.rawAge]
    exact older
  exact separated.event_candidate oldEventMembership beforeCandidate olderBefore
    touched

end PreparedStep

namespace ConclStep

/-- A canonical stable `concl` extension preserves older-event future-work
head-touch separation. -/
theorem olderEventFutureWorkTouchSeparated
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch :
      DispatchStep certificate before invariant ⟨.concl, after⟩}
    (step : ConclStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderEventFutureWorkTouchSeparated prior) :
    OlderEventFutureWorkTouchSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.concl step)) := by
  apply step.prepared.olderEventFutureWorkTouchSeparated step.output_eq prior
    separated
  simp [CanonicalTagHistory.reservationLedger,
    DispatchTagEvidence.reservationEvents]

end ConclStep

namespace NopStep

/-- A canonical stable `nop` extension preserves older-event future-work
head-touch separation. -/
theorem olderEventFutureWorkTouchSeparated
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.nop, after⟩}
    (step : NopStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderEventFutureWorkTouchSeparated prior) :
    OlderEventFutureWorkTouchSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.nop step)) := by
  apply step.prepared.olderEventFutureWorkTouchSeparated step.output_eq prior
    separated
  simp [CanonicalTagHistory.reservationLedger,
    DispatchTagEvidence.reservationEvents]

end NopStep

end SequentialFigure7

end ProofNetIR
