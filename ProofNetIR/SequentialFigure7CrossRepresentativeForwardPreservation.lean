import ProofNetIR.SequentialFigure7CrossRepresentativeWaitPreservation

namespace ProofNetIR

/-!
# Figure-7 forward preservation of cross-representative source separation

A successful `forward` has two future-work effects after its synchronized
prefix: every waiting occurrence and every old ready occurrence remains at its
exact boundary, while the submitted par conclusion is prepended to the active
ready bucket. Consequently, every output future-work occurrence either already
existed in the prepared middle state or is that inserted conclusion at the
active boundary. The alternatives are not claimed to be disjoint because the
typed local step does not itself assume global queued-occurrence uniqueness.

The production-side par queue changes the active component and firing counter,
but preserves marks and union-find parents. Existing candidates therefore
reduce to stable-prefix preservation. Inserted candidates require the explicit
`ForwardCreatedRegionSeparated` premise below. This module does not derive that
premise from the scheduler invariant and makes no unconditional forward,
progress, or completeness claim.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

namespace ForwardStep

/-- A forward par queue changes no union-find parent, so every representative
is identical in the output and the prepared middle state. -/
theorem after_representative_eq_prepared
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (token : RawTokenAge) :
    after.core.representative token =
      step.prepared.after.core.representative token := by
  have afterCore : after.core = step.coreAfter :=
    congrArg (fun state : ReservationState ↦ state.core) step.output_eq
  rw [afterCore]
  change step.coreAfter.representative token =
    step.prepared.coreMarked.representative token
  simp [UnificationState.representative, step.queueStep.after_eq]

end ForwardStep

namespace FutureWorkAt

/-- Every output future-work occurrence of a successful `forward` either
already existed in the prepared middle state or is the par conclusion inserted
at the active ready boundary.

The disjunction is intentionally not exclusive. A typed `ForwardStep` carries
the local active-bucket `Nodup` guard but not the complete scheduler invariant
needed to exclude the same conclusion from every other queue location. -/
theorem beforeForwardOrInserted
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt after rawAge vertex) :
    FutureWorkAt step.prepared.after rawAge vertex ∨
      (rawAge = step.prepared.stackResult.rawAge ∧
        vertex = step.consumer.conclusion) := by
  have afterStack : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState ↦ state.stack) step.output_eq
  have middleInvariant :
      ReservationInvariant certificate step.prepared.after :=
    step.prepared.reservationInvariant step.before_invariant
  rcases SequentialStackState.popReadyMark?_exact step.prepared.stack_eq with
    ⟨_top, sigmaTop, _unmarked, _marks, _nextAge, sigmaEquation,
      _ready, _waiting, _marked⟩
  have middleSigmaTop :
      step.prepared.after.stack.sigma.getLast? =
        some step.prepared.stackResult.rawAge := by
    change step.prepared.stackResult.after.sigma.getLast? = _
    rw [sigmaEquation]
    exact sigmaTop
  rcases List.getLast?_eq_some_iff.mp middleSigmaTop with
    ⟨sigmaPrefix, sigmaDecomposition⟩
  have prefixLengths :
      step.prependStep.readyPrefix.length = sigmaPrefix.length := by
    have aligned := middleInvariant.stack_wellShaped.ready_aligned
    change
      step.prepared.stackResult.after.ready.length =
        step.prepared.stackResult.after.sigma.length at aligned
    rw [step.prependStep.ready_eq] at aligned
    change
      step.prepared.stackResult.after.sigma =
        sigmaPrefix ++ [step.prepared.stackResult.rawAge] at sigmaDecomposition
    rw [sigmaDecomposition] at aligned
    simp at aligned
    omega
  cases work with
  | @ready position _ bucket _ sigmaAt readyAt member =>
      rw [afterStack, step.prependStep.after_eq] at sigmaAt readyAt
      change step.prepared.after.stack.sigma[position]? = some rawAge at sigmaAt
      change
        (step.prependStep.readyPrefix ++
          [step.consumer.conclusion :: step.prependStep.activeReady])[position]? =
            some bucket at readyAt
      have positionBound :
          position <
            (step.prependStep.readyPrefix ++
              [step.consumer.conclusion ::
                step.prependStep.activeReady]).length :=
        (List.getElem?_eq_some_iff.mp readyAt).1
      by_cases inPrefix : position < step.prependStep.readyPrefix.length
      · left
        apply FutureWorkAt.ready sigmaAt
        · change
            step.prepared.stackResult.after.ready[position]? = some bucket
          rw [step.prependStep.ready_eq,
            List.getElem?_append_left inPrefix]
          rw [List.getElem?_append_left inPrefix] at readyAt
          exact readyAt
        · exact member
      · have positionTop :
            position = step.prependStep.readyPrefix.length := by
          simp at positionBound
          omega
        subst position
        have bucketEquation :
            bucket =
              step.consumer.conclusion :: step.prependStep.activeReady := by
          simp at readyAt
          exact readyAt.symm
        subst bucket
        have rawAgeEquation :
            rawAge = step.prepared.stackResult.rawAge := by
          change
            step.prepared.stackResult.after.sigma[
              step.prependStep.readyPrefix.length]? = some rawAge at sigmaAt
          change
            step.prepared.stackResult.after.sigma =
              sigmaPrefix ++ [step.prepared.stackResult.rawAge]
                at sigmaDecomposition
          rw [sigmaDecomposition, prefixLengths] at sigmaAt
          simp at sigmaAt
          exact sigmaAt.symm
        simp only [List.mem_cons] at member
        rcases member with head | tail
        · exact Or.inr ⟨rawAgeEquation, head⟩
        · left
          apply FutureWorkAt.ready sigmaAt
          · change
              step.prepared.stackResult.after.ready[
                step.prependStep.readyPrefix.length]? =
                  some step.prependStep.activeReady
            rw [step.prependStep.ready_eq]
            simp
          · exact tail
  | @waiting _ payload _ waitingAt member =>
      left
      apply FutureWorkAt.waiting
      · rw [afterStack, step.prependStep.after_eq] at waitingAt
        exact waitingAt
      · exact member

end FutureWorkAt

/-- The exact structural data of a future `new` candidate created by the par
conclusion inserted during one successful `forward`.

The active raw-age boundary and head are fixed by the enclosing forward step,
so this record stores only the tensor-below witness and its prepared-middle
mate mark. It contains no desired source-region separation. -/
structure ForwardCreatedCandidate (certificate : Certificate)
    {before after : ReservationState}
    (step : ForwardStep certificate before after) : Type where
  tensor : TensorBelow
  tensor_valid :
    tensor.Valid certificate certificate.consumerIndex
      step.consumer.conclusion
  mate_unmarked :
    step.prepared.after.core.marks[tensor.mate]? = some none

/-- Additional geometry required for candidates introduced by one active-ready
prepend during `forward`.

The comparison is made in the prepared middle state. The production par queue
preserves its union-find parents, and only strictly older current
representatives are constrained. -/
def ForwardCreatedRegionSeparated
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (prior : CanonicalTagHistory certificate history)
    (step : ForwardStep certificate before after) : Prop :=
  ∀ {event : ReservationEvent certificate},
    event ∈ prior.reservationLedger →
    ∀ created : ForwardCreatedCandidate certificate step,
      step.prepared.after.core.representative event.rawAge <
          step.prepared.after.core.representative
            step.prepared.stackResult.rawAge →
        SourceLeftRegionsDisjoint certificate event.start
          created.tensor.mate

namespace ForwardStep

/-- A canonical `forward` history extension preserves older-source-region
separation provided the newly inserted par conclusion satisfies the explicit
created-candidate geometry premise.

Candidates inherited from the prepared middle state are discharged by prior
separation plus stable-prefix transport. Candidates whose work witness uses the
inserted conclusion are discharged only by
`ForwardCreatedRegionSeparated`. -/
theorem olderSourceRegionSeparated_of_created
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch :
      DispatchStep certificate before invariant ⟨.forward, after⟩}
    (step : ForwardStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderSourceRegionSeparated prior)
    (createdSeparated : ForwardCreatedRegionSeparated prior step) :
    OlderSourceRegionSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.forward step)) := by
  refine { event_candidate := ?_ }
  intro event eventMembership candidate older
  have oldEventMembership : event ∈ prior.reservationLedger := by
    simpa [CanonicalTagHistory.reservationLedger,
      DispatchTagEvidence.reservationEvents] using eventMembership
  rcases candidate.work.beforeForwardOrInserted step with
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
        have afterCore : after.core = step.coreAfter :=
          congrArg (fun state : ReservationState ↦ state.core) step.output_eq
        rw [afterCore] at mateUnmarked
        change step.coreAfter.marks[candidate.tensor.mate]? = some none
          at mateUnmarked
        rw [step.queueStep.after_eq] at mateUnmarked
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
        ← step.prepared.after_representative_eq_before candidate.rawAge]
      rw [← step.after_representative_eq_prepared event.rawAge,
        ← step.after_representative_eq_prepared candidate.rawAge]
      exact older
    have oldDisjoint :=
      separated.event_candidate oldEventMembership beforeCandidate olderBefore
    simpa [beforeCandidate, middleCandidate,
      FutureNewCandidateAt.beforePrepared] using oldDisjoint
  · let created : ForwardCreatedCandidate certificate step := {
      tensor := candidate.tensor
      tensor_valid := by
        rw [← candidateHead]
        exact candidate.tensor_valid
      mate_unmarked := by
        have mateUnmarked := candidate.mate_unmarked
        have afterCore : after.core = step.coreAfter :=
          congrArg (fun state : ReservationState ↦ state.core) step.output_eq
        rw [afterCore] at mateUnmarked
        change step.coreAfter.marks[candidate.tensor.mate]? = some none
          at mateUnmarked
        rw [step.queueStep.after_eq] at mateUnmarked
        exact mateUnmarked }
    have olderMiddle :
        step.prepared.after.core.representative event.rawAge <
          step.prepared.after.core.representative
            step.prepared.stackResult.rawAge := by
      rw [← candidateAge]
      rw [← step.after_representative_eq_prepared event.rawAge,
        ← step.after_representative_eq_prepared candidate.rawAge]
      exact older
    simpa [created] using
      createdSeparated oldEventMembership created olderMiddle

end ForwardStep

end SequentialFigure7

end ProofNetIR
