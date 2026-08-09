import ProofNetIR.SequentialFigure7CrossRepresentativeStablePreservation

namespace ProofNetIR

/-!
# Figure-7 new preservation of cross-representative source separation

A successful `new` keeps every old future-work occurrence in its marked
middle state and appends exactly the reached/partner pair at the fresh raw
age.  It also appends one fresh reservation event.  Old candidates use the
prior invariant, while candidates at the appended endpoints require the
explicit `NewCreatedRegionSeparated` premise below.

The fresh event is maximal among output future-work raw ages, so it cannot be
strictly older than any output candidate.  This module does not derive the
created-region premise and makes no unconditional preservation, progress, or
completeness claim.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

namespace NewStep

/-- The synchronized prefix of a successful `new`, exposed for transport to
the stable-prefix preservation layer. -/
def preparedPrefix
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) : PreparedStep before where
  stackResult := step.stackResult
  coreMarked := step.coreMarked
  stack_eq := step.stack_eq
  core_mark_eq := step.core_mark_eq

/-- The marked middle state's horizon is exactly the fresh event's raw age. -/
theorem markedMiddle_nextAge_eq_event_rawAge
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    step.markedMiddle.stack.nextAge =
      (ReservationEvent.new step).rawAge := by
  change step.stackResult.after.nextAge = before.stack.nextAge
  exact (SequentialStackState.popReadyMark?_exact step.stack_eq).2.2.2.2.1

/-- The output horizon is one more than the fresh event's raw age. -/
theorem after_nextAge_eq_event_rawAge_add_one
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    after.stack.nextAge = (ReservationEvent.new step).rawAge + 1 := by
  have afterStack : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState ↦ state.stack) step.output_eq
  rcases SequentialStackState.operationalNewEnqueue?_exact
      step.stack_enqueue_eq with
    ⟨_active, _activeEquation, _activeLt, _marks, nextAgeEquation,
      _sigma, _ready, _waiting, _activeWaiting, _freshWaiting⟩
  rw [afterStack, nextAgeEquation]
  change step.markedMiddle.stack.nextAge + 1 =
    (ReservationEvent.new step).rawAge + 1
  rw [step.markedMiddle_nextAge_eq_event_rawAge]

/-- Reserving the fresh axiom preserves every representative observable from
the marked middle state. -/
theorem after_representative_eq_markedMiddle
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) (token : RawTokenAge) :
    after.core.representative token =
      step.markedMiddle.core.representative token := by
  have afterCore : after.core = step.coreAfter :=
    congrArg (fun state : ReservationState ↦ state.core) step.output_eq
  rw [afterCore]
  change step.coreAfter.representative token =
    step.coreMarked.representative token
  exact certificate.reserveAxiomAt?_old_representative
    step.markedMiddle_reservationInvariant.core_orderedParents
    step.core_reserve_eq

/-- Reserving the fresh axiom leaves the marked middle state's marks intact. -/
theorem after_marks_eq_markedMiddle
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    after.core.marks = step.markedMiddle.core.marks := by
  have afterCore : after.core = step.coreAfter :=
    congrArg (fun state : ReservationState ↦ state.core) step.output_eq
  rcases certificate.reserveAxiomAt?_exact step.core_reserve_eq with
    ⟨_left, _right, _component, _link, _ready, _lookup, _frontier,
      marksEquation, _parents, _components, _counter, _fired⟩
  rw [afterCore]
  exact marksEquation

end NewStep

namespace FutureWorkAt

/-- Every output future-work occurrence of `new` either existed in the marked
middle state or is one of the two endpoints appended at the fresh raw age. -/
theorem beforeNewOrInserted
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt after rawAge vertex) :
    FutureWorkAt step.markedMiddle rawAge vertex ∨
      (rawAge = (ReservationEvent.new step).rawAge ∧
        (vertex = step.reached ∨ vertex = step.partner)) := by
  have afterStack : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState ↦ state.stack) step.output_eq
  have middleInvariant := step.markedMiddle_reservationInvariant
  rcases SequentialStackState.operationalNewEnqueue?_exact
      step.stack_enqueue_eq with
    ⟨active, _activeEquation, _activeLt, _marks, _nextAge,
      sigmaEquation, readyEquation, waitingEquation, _activeWaiting,
      _freshWaiting⟩
  have aligned :
      step.markedMiddle.stack.ready.length =
        step.markedMiddle.stack.sigma.length :=
    middleInvariant.stack_wellShaped.ready_aligned
  cases work with
  | @ready position _ bucket _ sigmaAt readyAt member =>
      have sigmaAfter := sigmaAt
      have readyAfter := readyAt
      rw [afterStack, sigmaEquation] at sigmaAfter
      rw [afterStack, readyEquation] at readyAfter
      change
        (step.markedMiddle.stack.sigma ++
          [step.markedMiddle.stack.nextAge])[position]? = some rawAge
            at sigmaAfter
      change
        (step.markedMiddle.stack.ready ++
          [[step.reached, step.partner]])[position]? = some bucket
            at readyAfter
      have positionBound :
          position <
            (step.markedMiddle.stack.ready ++
              [[step.reached, step.partner]]).length :=
        (List.getElem?_eq_some_iff.mp readyAfter).1
      by_cases oldPosition :
          position < step.markedMiddle.stack.ready.length
      · left
        apply FutureWorkAt.ready (position := position) (bucket := bucket)
        · have sigmaPosition :
              position < step.markedMiddle.stack.sigma.length := by
            rw [← aligned]
            exact oldPosition
          rw [List.getElem?_append_left sigmaPosition] at sigmaAfter
          exact sigmaAfter
        · rw [List.getElem?_append_left oldPosition] at readyAfter
          exact readyAfter
        · exact member
      · have freshPosition :
            position = step.markedMiddle.stack.ready.length := by
          simp only [List.length_append, List.length_singleton] at positionBound
          omega
        subst position
        have bucketEquation : bucket = [step.reached, step.partner] := by
          simp at readyAfter
          exact readyAfter.symm
        subst bucket
        have ageEquation :
            rawAge = step.markedMiddle.stack.nextAge := by
          rw [aligned] at sigmaAfter
          simp at sigmaAfter
          exact sigmaAfter.symm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        exact Or.inr ⟨ageEquation.trans
          step.markedMiddle_nextAge_eq_event_rawAge, member⟩
  | @waiting _ payload _ waitingAt member =>
      have waitingAfter := waitingAt
      rw [afterStack, waitingEquation] at waitingAfter
      by_cases same : rawAge = active
      · subst rawAge
        rw [Array.getElem?_setIfInBounds] at waitingAfter
        simp at waitingAfter
        have payloadEmpty : payload = [] := waitingAfter.2
        rw [payloadEmpty] at member
        simp at member
      · left
        apply FutureWorkAt.waiting
        · rw [Array.getElem?_setIfInBounds_ne (Ne.symm same)]
            at waitingAfter
          exact waitingAfter
        · exact member

end FutureWorkAt

/-- One actual future-`new` candidate whose head is an endpoint appended by
the successful enclosing `new` step. -/
structure NewCreatedCandidate (certificate : Certificate)
    {before after : ReservationState}
    (step : NewStep certificate before after) : Type where
  head : Vertex
  endpoint : head = step.reached ∨ head = step.partner
  tensor : TensorBelow
  tensor_valid :
    tensor.Valid certificate certificate.consumerIndex head
  mate_unmarked :
    step.markedMiddle.core.marks[tensor.mate]? = some none

/-- Geometry required only for actual candidates created at the two appended
endpoints.  Representatives are compared in the prepared marked-middle state. -/
def NewCreatedRegionSeparated
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (prior : CanonicalTagHistory certificate history)
    (step : NewStep certificate before after) : Prop :=
  ∀ {event : ReservationEvent certificate},
    event ∈ prior.reservationLedger →
    ∀ created : NewCreatedCandidate certificate step,
      step.markedMiddle.core.representative event.rawAge <
          step.markedMiddle.core.representative
            (ReservationEvent.new step).rawAge →
        SourceLeftRegionsDisjoint certificate event.start
          created.tensor.mate

namespace NewStep

/-- The freshly appended reservation event is not strictly older than any
future candidate in the output state. -/
theorem freshEvent_not_strictly_older
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (candidate : FutureNewCandidateAt certificate after) :
    ¬ after.core.representative (ReservationEvent.new step).rawAge <
        after.core.representative candidate.rawAge := by
  have afterInvariant := step.schedulerInvariant invariant
  have candidateRepresentative :=
    candidate.work.representative_eq_rawAge afterInvariant
  have candidateBound := candidate.work.rawAge_lt_nextAge afterInvariant
  have afterCore : after.core = step.coreAfter :=
    congrArg (fun state : ReservationState ↦ state.core) step.output_eq
  have carriers :=
    UnificationState.markReadyRaw?_carriers step.core_mark_eq
  have freshAge :
      (ReservationEvent.new step).rawAge =
        step.coreMarked.parents.size := by
    change before.stack.nextAge = step.coreMarked.parents.size
    rw [← invariant.realizesSigma.horizon_eq, carriers.1]
  have freshRepresentative :
      after.core.representative (ReservationEvent.new step).rawAge =
        (ReservationEvent.new step).rawAge := by
    rw [afterCore, freshAge]
    exact certificate.reserveAxiomAt?_fresh_representative
      step.core_reserve_eq
  rw [step.after_nextAge_eq_event_rawAge_add_one] at candidateBound
  have candidateLe :
      candidate.rawAge ≤ (ReservationEvent.new step).rawAge := by
    apply Nat.le_of_lt_succ
    simpa [Nat.succ_eq_add_one] using candidateBound
  intro older
  rw [freshRepresentative, candidateRepresentative] at older
  exact (Nat.not_lt_of_ge candidateLe) older

/-- A canonical `new` history extension preserves older-source-region
separation under the explicit geometry premise for newly appended endpoints. -/
theorem olderSourceRegionSeparated_of_created
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.new, after⟩}
    (step : NewStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderSourceRegionSeparated prior)
    (createdSeparated : NewCreatedRegionSeparated prior step) :
    OlderSourceRegionSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.new step)) := by
  refine { event_candidate := ?_ }
  intro event eventMembership candidate older
  simp only [CanonicalTagHistory.reservationLedger,
    DispatchTagEvidence.reservationEvents, List.mem_append,
    List.mem_singleton] at eventMembership
  rcases eventMembership with oldEventMembership | freshEvent
  · rcases candidate.work.beforeNewOrInserted step with
      oldWork | ⟨candidateAge, candidateHead⟩
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
      have oldDisjoint := separated.event_candidate oldEventMembership
        beforeCandidate olderBefore
      simpa [beforeCandidate, middleCandidate, preparedPrefix,
        FutureNewCandidateAt.beforePrepared] using oldDisjoint
    · let created : NewCreatedCandidate certificate step := {
        head := candidate.head
        endpoint := candidateHead
        tensor := candidate.tensor
        tensor_valid := candidate.tensor_valid
        mate_unmarked := by
          have mateUnmarked := candidate.mate_unmarked
          rw [step.after_marks_eq_markedMiddle] at mateUnmarked
          exact mateUnmarked }
      have olderMiddle :
          step.markedMiddle.core.representative event.rawAge <
            step.markedMiddle.core.representative
              (ReservationEvent.new step).rawAge := by
        rw [← candidateAge]
        rw [← step.after_representative_eq_markedMiddle event.rawAge]
        rw [← step.after_representative_eq_markedMiddle candidate.rawAge]
        exact older
      simpa [created] using createdSeparated oldEventMembership
        created olderMiddle
  · subst event
    exact (step.freshEvent_not_strictly_older invariant candidate older).elim

end NewStep

end SequentialFigure7

end ProofNetIR
