import ProofNetIR.SequentialFigure7CrossRepresentativeNewPreservation
import ProofNetIR.SequentialFigure7UnifyPayloadInvariant

namespace ProofNetIR

/-!
# Figure-7 UnifyPayload preservation of cross-representative source separation

A successful `unifyPayload` retires the active boundary into the previous
boundary, moves the active ready bucket there, preserves the remaining future
work, and inserts the selected tensor conclusion.  The survivor, moved, and
created cases below form a covering decomposition; they are not asserted to be
mutually exclusive.

The union changes representatives precisely for the retired active class.
Strict older-than ordering rules out a prior event in that class whenever the
output candidate is future work.  Survivors and moved candidates therefore
transport through the prior invariant.  The inserted tensor conclusion uses
the explicit, non-circular `UnifyPayloadCreatedRegionSeparated` premise.

This module does not claim global representative stability, derive the created
region premise, or prove unconditional preservation, progress, or completeness.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

namespace UnifyPayloadStep

private theorem activeBoundary_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.mergeStep.activeBoundary =
      step.prepared.stackResult.rawAge := by
  have mergeTop :
      step.prepared.stackResult.after.sigma.getLast? =
        some step.mergeStep.activeBoundary := by
    rw [step.mergeStep.sigma_eq]
    simp
  have preparedTop :
      step.prepared.stackResult.after.sigma.getLast? =
        some step.prepared.stackResult.rawAge := by
    rcases SequentialStackState.popReadyMark?_exact step.prepared.stack_eq with
      ⟨_, sigmaTop, _, _, _, sigmaAfter, _, _, _⟩
    rw [sigmaAfter]
    exact sigmaTop
  exact Option.some.inj (mergeTop.symm.trans preparedTop)

private theorem middleSigma_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.prepared.after.stack.sigma =
      step.mergeStep.sigmaPrefix ++
        [step.previousBoundary, step.prepared.stackResult.rawAge] := by
  simpa [PreparedStep.after, step.activeBoundary_eq] using
    step.mergeStep.sigma_eq

private theorem previous_lt_active
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.previousBoundary < step.prepared.stackResult.rawAge :=
  Nat.lt_of_le_of_lt step.lower step.upper

private theorem middle_previous_root
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.prepared.after.core.representative step.previousBoundary =
      step.previousBoundary := by
  have middleInvariant :
      ReservationInvariant certificate step.prepared.after :=
    step.prepared.reservationInvariant step.before_invariant
  have previousMembership :
      step.previousBoundary ∈ step.prepared.after.stack.sigma := by
    rw [step.middleSigma_eq]
    simp
  have previousBound :
      step.previousBoundary < step.prepared.after.stack.nextAge :=
    middleInvariant.stack_wellShaped.sigma_partition.boundary_lt _
      previousMembership
  have lookup :
      sigmaBoundary? step.prepared.after.stack.sigma
          step.previousBoundary =
        some step.previousBoundary :=
    middleInvariant.stack_wellShaped.sigma_partition
      |>.sigmaBoundary?_eq_previous_of_between
        step.middleSigma_eq (Nat.le_refl _) step.previous_lt_active
  have realized :=
    middleInvariant.realizesSigma.representative_eq_boundary previousBound
  exact Option.some.inj (realized.symm.trans lookup)

/-- `unifyPayload` changes no raw marks after its prepared prefix. -/
theorem after_marks_eq_prepared
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    after.core.marks = step.prepared.after.core.marks := by
  have afterCore :
      after.core = step.coreAfter :=
    congrArg (fun state : ReservationState ↦ state.core) step.output_eq
  rw [afterCore]
  change step.coreAfter.marks = step.prepared.coreMarked.marks
  rw [step.activationFold.marks_eq]
  rw [step.tensorStep.after_eq]

/-- The output representative map is the prepared map with exactly the active
class redirected to the previous boundary. -/
theorem after_representative_eq_prepared_if
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    {token : RawTokenAge}
    (tokenBound : token < step.prepared.after.core.parents.size) :
    after.core.representative token =
      if step.prepared.after.core.representative token =
          step.prepared.stackResult.rawAge
      then step.previousBoundary
      else step.prepared.after.core.representative token := by
  have middleInvariant :
      ReservationInvariant certificate step.prepared.after :=
    step.prepared.reservationInvariant step.before_invariant
  have middleWellShaped := middleInvariant.stack_wellShaped
  have middleRealizes := middleInvariant.realizesSigma
  have middleOrdered : step.prepared.after.core.OrderedParents := by
    intro child parent lookup
    exact middleInvariant.core_orderedParents lookup
  have previousLtActive := step.previous_lt_active
  have maxTokenEquation :
      max step.tensorStep.leftToken step.tensorStep.rightToken =
        step.prepared.stackResult.rawAge := by
    rcases step.tokens_eq_adjacent with orientation | orientation
    · rw [orientation.2.1, orientation.2.2]
      exact Nat.max_eq_left (Nat.le_of_lt previousLtActive)
    · rw [orientation.2.1, orientation.2.2]
      exact Nat.max_eq_right (Nat.le_of_lt previousLtActive)
  have minTokenEquation :
      min step.tensorStep.leftToken step.tensorStep.rightToken =
        step.previousBoundary := by
    rcases step.tokens_eq_adjacent with orientation | orientation
    · rw [orientation.2.1, orientation.2.2]
      exact Nat.min_eq_right (Nat.le_of_lt previousLtActive)
    · rw [orientation.2.1, orientation.2.2]
      exact Nat.min_eq_left (Nat.le_of_lt previousLtActive)
  have activeMembership :
      step.prepared.stackResult.rawAge ∈
        step.prepared.after.stack.sigma := by
    rw [step.middleSigma_eq]
    simp
  have activeStackBound :
      step.prepared.stackResult.rawAge <
        step.prepared.after.stack.nextAge :=
    middleWellShaped.sigma_partition.boundary_lt _ activeMembership
  have previousStackBound :
      step.previousBoundary < step.prepared.after.stack.nextAge :=
    Nat.lt_trans previousLtActive activeStackBound
  have activeCoreBound :
      step.prepared.stackResult.rawAge <
        step.prepared.after.core.parents.size := by
    rw [middleRealizes.horizon_eq]
    exact activeStackBound
  have previousCoreBound :
      step.previousBoundary < step.prepared.after.core.parents.size := by
    rw [middleRealizes.horizon_eq]
    exact previousStackBound
  have activeLookup :
      sigmaBoundary? step.prepared.after.stack.sigma
          step.prepared.stackResult.rawAge =
        some step.prepared.stackResult.rawAge :=
    middleWellShaped.sigma_partition.sigmaBoundary?_eq_top (by
      rw [step.middleSigma_eq]
      simp)
  have activeRoot :
      step.prepared.after.core.representative
          step.prepared.stackResult.rawAge =
        step.prepared.stackResult.rawAge := by
    have realized :=
      middleRealizes.representative_eq_boundary activeStackBound
    exact Option.some.inj (realized.symm.trans activeLookup)
  have updatedRepresentative :=
    middleOrdered.setParent_representative
      (survivor := step.previousBoundary)
      (retired := step.prepared.stackResult.rawAge)
      previousCoreBound activeCoreBound previousLtActive
      step.middle_previous_root activeRoot tokenBound
  have afterCore :
      after.core = step.coreAfter :=
    congrArg (fun state : ReservationState ↦ state.core) step.output_eq
  rw [afterCore]
  change step.coreAfter.representative token =
    if step.prepared.coreMarked.representative token =
        step.prepared.stackResult.rawAge
    then step.previousBoundary
    else step.prepared.coreMarked.representative token
  unfold UnificationState.representative
  rw [step.activationFold.parents_eq, step.tensorStep.after_eq,
    maxTokenEquation, minTokenEquation]
  exact updatedRepresentative

end UnifyPayloadStep

namespace FutureNewCandidateAt

/-- Every future-`new` candidate after `unifyPayload` lies at or below the
surviving previous boundary. -/
theorem rawAge_le_previousBoundary_of_unifyPayload
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (candidate : FutureNewCandidateAt certificate after) :
    candidate.rawAge ≤ step.previousBoundary := by
  have afterInvariant := step.schedulerInvariant invariant
  have membership := candidate.work.rawAge_mem_sigma afterInvariant
  have afterStack :
      after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState ↦ state.stack) step.output_eq
  have sigmaEquation :
      after.stack.sigma =
        step.mergeStep.sigmaPrefix ++ [step.previousBoundary] := by
    rw [afterStack]
    exact step.exact.1
  have increasing :=
    afterInvariant.stack_wellShaped.sigma_partition.strictIncreasing
  rw [sigmaEquation] at membership increasing
  simp only [List.mem_append, List.mem_singleton] at membership
  rcases membership with inPrefix | same
  · exact Nat.le_of_lt
      ((List.pairwise_append.mp increasing).2.2 candidate.rawAge inPrefix
        step.previousBoundary (by simp))
  · exact Nat.le_of_eq same

end FutureNewCandidateAt

private theorem event_rawAge_lt_nextAge
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (prior : CanonicalTagHistory certificate history)
    {event : ReservationEvent certificate}
    (membership : event ∈ prior.reservationLedger) :
    event.rawAge < before.stack.nextAge := by
  have mapped :
      event.rawAge ∈
        prior.reservationLedger.map ReservationEvent.rawAge :=
    List.mem_map_of_mem
      (f := fun e : ReservationEvent certificate ↦ e.rawAge) membership
  rw [prior.reservationLedger_rawAges] at mapped
  exact List.mem_range.mp mapped

namespace UnifyPayloadStep

private theorem event_representative_eq_prepared_of_older
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (prior : CanonicalTagHistory certificate history)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ prior.reservationLedger)
    (candidate : FutureNewCandidateAt certificate after)
    (older :
      after.core.representative event.rawAge <
        after.core.representative candidate.rawAge) :
    after.core.representative event.rawAge =
      step.prepared.after.core.representative event.rawAge := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have eventBeforeBound := event_rawAge_lt_nextAge prior eventMembership
  have middleNextAge :
      step.prepared.after.stack.nextAge = before.stack.nextAge := by
    rcases SequentialStackState.popReadyMark?_exact step.prepared.stack_eq with
      ⟨_, _, _, _, nextAge, _, _, _, _⟩
    exact nextAge
  have eventMiddleBound :
      event.rawAge < step.prepared.after.core.parents.size := by
    rw [middleInvariant.realizesSigma.horizon_eq, middleNextAge]
    exact eventBeforeBound
  have mapped :=
    step.after_representative_eq_prepared_if eventMiddleBound
  by_cases retired :
      step.prepared.after.core.representative event.rawAge =
        step.prepared.stackResult.rawAge
  · have afterEvent :
        after.core.representative event.rawAge =
          step.previousBoundary := by
      simpa [retired] using mapped
    have afterCandidate :=
      candidate.work.representative_eq_rawAge
        (step.schedulerInvariant invariant)
    have candidateLe :=
      candidate.rawAge_le_previousBoundary_of_unifyPayload step invariant
    have impossible : step.previousBoundary < candidate.rawAge := by
      rw [afterEvent, afterCandidate] at older
      exact older
    exact (Nat.not_lt_of_ge candidateLe impossible).elim
  · simpa [retired] using mapped

end UnifyPayloadStep

namespace FutureWorkAt

/-- Every output future-work occurrence of `unifyPayload` is a survivor from
the prepared state, an active-boundary item moved to the previous boundary, or
the inserted tensor conclusion.  The alternatives need not be disjoint. -/
theorem beforeUnifyPayloadOrMovedOrCreated
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt after rawAge vertex) :
    FutureWorkAt step.prepared.after rawAge vertex ∨
      (rawAge = step.previousBoundary ∧
        FutureWorkAt step.prepared.after
          step.prepared.stackResult.rawAge vertex) ∨
      (rawAge = step.previousBoundary ∧
        vertex = step.consumer.conclusion) := by
  have middleInvariant :
      ReservationInvariant certificate step.prepared.after :=
    step.prepared.reservationInvariant step.before_invariant
  have afterStack :
      after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState ↦ state.stack) step.output_eq
  have afterSigma :
      after.stack.sigma =
        step.mergeStep.sigmaPrefix ++ [step.previousBoundary] := by
    rw [afterStack]
    exact step.exact.1
  have afterReady :
      after.stack.ready =
        step.mergeStep.readyPrefix ++
          [step.consumer.conclusion ::
            (step.payload ++ step.mergeStep.previousReady ++
              step.mergeStep.activeReady)] := by
    rw [afterStack]
    exact step.exact.2.1
  have afterWaiting :
      after.stack.waiting =
        step.prepared.stackResult.after.waiting.setIfInBounds
          step.previousBoundary .undefined := by
    rw [afterStack]
    exact step.exact.2.2.1
  have middleSigma :
      step.prepared.after.stack.sigma =
        step.mergeStep.sigmaPrefix ++
          [step.previousBoundary, step.mergeStep.activeBoundary] :=
    step.mergeStep.sigma_eq
  have middleReady :
      step.prepared.after.stack.ready =
        step.mergeStep.readyPrefix ++
          [step.mergeStep.previousReady, step.mergeStep.activeReady] :=
    step.mergeStep.ready_eq
  have prefixLengths :
      step.mergeStep.sigmaPrefix.length =
        step.mergeStep.readyPrefix.length := by
    have aligned := middleInvariant.stack_wellShaped.ready_aligned
    rw [middleReady, middleSigma] at aligned
    simp at aligned
    omega
  cases work with
  | @ready position _ bucket _ sigmaAt readyAt member =>
      have positionBound :
          position <
            (step.mergeStep.readyPrefix ++
              [step.consumer.conclusion ::
                (step.payload ++ step.mergeStep.previousReady ++
                  step.mergeStep.activeReady)]).length := by
        rw [← afterReady]
        exact (List.getElem?_eq_some_iff.mp readyAt).choose
      by_cases inPrefix : position < step.mergeStep.readyPrefix.length
      · have sigmaInPrefix :
            position < step.mergeStep.sigmaPrefix.length := by
          omega
        left
        apply FutureWorkAt.ready
        · rw [middleSigma, List.getElem?_append_left sigmaInPrefix]
          rw [afterSigma, List.getElem?_append_left sigmaInPrefix] at sigmaAt
          exact sigmaAt
        · rw [middleReady, List.getElem?_append_left inPrefix]
          rw [afterReady, List.getElem?_append_left inPrefix] at readyAt
          exact readyAt
        · exact member
      · have positionTop :
            position = step.mergeStep.readyPrefix.length := by
          simp at positionBound
          omega
        subst position
        have rawAgeEquation : rawAge = step.previousBoundary := by
          rw [afterSigma, ← prefixLengths] at sigmaAt
          simp at sigmaAt
          exact sigmaAt.symm
        have bucketEquation :
            bucket =
              step.consumer.conclusion ::
                (step.payload ++ step.mergeStep.previousReady ++
                  step.mergeStep.activeReady) := by
          rw [afterReady] at readyAt
          simp at readyAt
          simpa [List.append_assoc] using readyAt.symm
        subst rawAge
        subst bucket
        simp only [List.mem_cons, List.mem_append] at member
        rcases member with created | ((payload | previous) | active)
        · right
          right
          exact ⟨rfl, created⟩
        · left
          exact FutureWorkAt.waiting step.waiting_payload payload
        · left
          apply FutureWorkAt.ready
              (position := step.mergeStep.sigmaPrefix.length)
              (bucket := step.mergeStep.previousReady)
          · rw [middleSigma]
            simp
          · rw [middleReady, prefixLengths]
            simp
          · exact previous
        · right
          left
          refine ⟨rfl, ?_⟩
          apply FutureWorkAt.ready
              (position := step.mergeStep.sigmaPrefix.length + 1)
              (bucket := step.mergeStep.activeReady)
          · rw [middleSigma, step.activeBoundary_eq]
            simp
          · rw [middleReady, prefixLengths]
            simp
          · exact active
  | @waiting _ payload _ waitingAt member =>
      by_cases sameBoundary : rawAge = step.previousBoundary
      · subst rawAge
        rw [afterWaiting, Array.getElem?_setIfInBounds] at waitingAt
        have bound :
            step.previousBoundary <
              step.prepared.stackResult.after.waiting.size :=
          (Array.getElem?_eq_some_iff.mp step.waiting_payload).choose
        simp [bound] at waitingAt
      · left
        apply FutureWorkAt.waiting
        · rw [afterWaiting, Array.getElem?_setIfInBounds] at waitingAt
          simpa [PreparedStep.after, sameBoundary,
            Ne.symm sameBoundary] using waitingAt
        · exact member

end FutureWorkAt

/-- One actual future-`new` candidate at the tensor conclusion inserted by
the successful enclosing `unifyPayload` step. -/
structure UnifyPayloadCreatedCandidate (certificate : Certificate)
    {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) : Type where
  tensor : TensorBelow
  tensor_valid :
    tensor.Valid certificate certificate.consumerIndex
      step.consumer.conclusion
  mate_unmarked :
    step.prepared.after.core.marks[tensor.mate]? = some none

/-- Geometry required only for an actual candidate at the tensor conclusion
inserted by `unifyPayload`.  Representatives are compared before the union,
in the prepared state, so this premise does not assume the preservation result. -/
def UnifyPayloadCreatedRegionSeparated
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (prior : CanonicalTagHistory certificate history)
    (step : UnifyPayloadStep certificate before after) : Prop :=
  ∀ {event : ReservationEvent certificate},
    event ∈ prior.reservationLedger →
    ∀ created : UnifyPayloadCreatedCandidate certificate step,
      step.prepared.after.core.representative event.rawAge <
          step.prepared.after.core.representative step.previousBoundary →
        SourceLeftRegionsDisjoint certificate event.start
          created.tensor.mate

namespace UnifyPayloadStep

/-- A canonical `unifyPayload` history extension preserves
older-source-region separation under the explicit geometry premise for its
newly inserted tensor conclusion.  This dispatcher branch appends no
reservation event. -/
theorem olderSourceRegionSeparated_of_created
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch :
      DispatchStep certificate before invariant ⟨.unifyPayload, after⟩}
    (step : UnifyPayloadStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderSourceRegionSeparated prior)
    (createdSeparated :
      UnifyPayloadCreatedRegionSeparated prior step) :
    OlderSourceRegionSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.unifyPayload step)) := by
  refine { event_candidate := ?_ }
  intro event eventMembership candidate older
  have oldEventMembership : event ∈ prior.reservationLedger := by
    simpa [CanonicalTagHistory.reservationLedger,
      DispatchTagEvidence.reservationEvents] using eventMembership
  have afterInvariant := step.schedulerInvariant invariant
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have eventUnchanged :=
    step.event_representative_eq_prepared_of_older invariant prior
      oldEventMembership candidate older
  have afterCandidateRoot :=
    candidate.work.representative_eq_rawAge afterInvariant
  rcases candidate.work.beforeUnifyPayloadOrMovedOrCreated step with
    oldWork | ⟨candidateAge, movedWork⟩ | ⟨candidateAge, candidateHead⟩
  · let middleCandidate :
        FutureNewCandidateAt certificate step.prepared.after := {
      rawAge := candidate.rawAge
      head := candidate.head
      work := oldWork
      tensor := candidate.tensor
      tensor_valid := candidate.tensor_valid
      mate_unmarked := by
        have mateUnmarked := candidate.mate_unmarked
        rw [step.after_marks_eq_prepared] at mateUnmarked
        exact mateUnmarked }
    let beforeCandidate : FutureNewCandidateAt certificate before :=
      middleCandidate.beforePrepared step.prepared
    have middleCandidateRoot :=
      oldWork.representative_eq_rawAge middleInvariant
    have olderMiddle :
        step.prepared.after.core.representative event.rawAge <
          step.prepared.after.core.representative candidate.rawAge := by
      calc
        step.prepared.after.core.representative event.rawAge =
            after.core.representative event.rawAge := eventUnchanged.symm
        _ < after.core.representative candidate.rawAge := older
        _ = candidate.rawAge := afterCandidateRoot
        _ = step.prepared.after.core.representative candidate.rawAge :=
          middleCandidateRoot.symm
    have olderBefore :
        before.core.representative event.rawAge <
          before.core.representative beforeCandidate.rawAge := by
      change
        before.core.representative event.rawAge <
          before.core.representative candidate.rawAge
      rw [← step.prepared.after_representative_eq_before event.rawAge,
        ← step.prepared.after_representative_eq_before candidate.rawAge]
      exact olderMiddle
    have oldDisjoint :=
      separated.event_candidate oldEventMembership beforeCandidate olderBefore
    simpa [beforeCandidate, middleCandidate,
      FutureNewCandidateAt.beforePrepared] using oldDisjoint
  · let middleCandidate :
        FutureNewCandidateAt certificate step.prepared.after := {
      rawAge := step.prepared.stackResult.rawAge
      head := candidate.head
      work := movedWork
      tensor := candidate.tensor
      tensor_valid := candidate.tensor_valid
      mate_unmarked := by
        have mateUnmarked := candidate.mate_unmarked
        rw [step.after_marks_eq_prepared] at mateUnmarked
        exact mateUnmarked }
    let beforeCandidate : FutureNewCandidateAt certificate before :=
      middleCandidate.beforePrepared step.prepared
    have movedRoot :=
      movedWork.representative_eq_rawAge middleInvariant
    have olderMiddle :
        step.prepared.after.core.representative event.rawAge <
          step.prepared.after.core.representative
            step.prepared.stackResult.rawAge := by
      calc
        step.prepared.after.core.representative event.rawAge =
            after.core.representative event.rawAge := eventUnchanged.symm
        _ < after.core.representative candidate.rawAge := older
        _ = candidate.rawAge := afterCandidateRoot
        _ = step.previousBoundary := candidateAge
        _ < step.prepared.stackResult.rawAge := step.previous_lt_active
        _ = step.prepared.after.core.representative
            step.prepared.stackResult.rawAge := movedRoot.symm
    have olderBefore :
        before.core.representative event.rawAge <
          before.core.representative beforeCandidate.rawAge := by
      change
        before.core.representative event.rawAge <
          before.core.representative step.prepared.stackResult.rawAge
      rw [← step.prepared.after_representative_eq_before event.rawAge,
        ← step.prepared.after_representative_eq_before
          step.prepared.stackResult.rawAge]
      exact olderMiddle
    have oldDisjoint :=
      separated.event_candidate oldEventMembership beforeCandidate olderBefore
    simpa [beforeCandidate, middleCandidate,
      FutureNewCandidateAt.beforePrepared] using oldDisjoint
  · let created : UnifyPayloadCreatedCandidate certificate step := {
      tensor := candidate.tensor
      tensor_valid := by
        rw [← candidateHead]
        exact candidate.tensor_valid
      mate_unmarked := by
        have mateUnmarked := candidate.mate_unmarked
        rw [step.after_marks_eq_prepared] at mateUnmarked
        exact mateUnmarked }
    have olderMiddle :
        step.prepared.after.core.representative event.rawAge <
          step.prepared.after.core.representative step.previousBoundary := by
      calc
        step.prepared.after.core.representative event.rawAge =
            after.core.representative event.rawAge := eventUnchanged.symm
        _ < after.core.representative candidate.rawAge := older
        _ = candidate.rawAge := afterCandidateRoot
        _ = step.previousBoundary := candidateAge
        _ = step.prepared.after.core.representative step.previousBoundary :=
          step.middle_previous_root.symm
    simpa [created] using
      createdSeparated oldEventMembership created olderMiddle

end UnifyPayloadStep

end SequentialFigure7

end ProofNetIR
