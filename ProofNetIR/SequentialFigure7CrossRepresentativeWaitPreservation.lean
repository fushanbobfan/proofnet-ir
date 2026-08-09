import ProofNetIR.SequentialFigure7CrossRepresentativeStablePreservation

namespace ProofNetIR

/-!
# Figure-7 wait preservation of cross-representative source separation

A successful `wait` has two effects on future work: its synchronized prefix
removes the selected ready head, and its destination prepends one conclusion
to an existing waiting cell.  Consequently, every future-work occurrence in
the output either already existed in the prepared middle state or is the
inserted conclusion at the exact destination boundary.  The alternatives are
not claimed to be disjoint because the low-level prepend primitive does not
enforce global queue uniqueness.

Existing candidates reduce to the stable-prefix preservation theorem.
Inserted candidates require the explicit `WaitCreatedRegionSeparated`
premise below.  This module does not claim that the premise follows from the
current scheduler invariant, nor does it prove unconditional wait
preservation, progress, or completeness.
-/

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

namespace SequentialSchedulerBridge.WaitDestinationStep

/-- A waiting destination changes no union-find parent, so every current
representative is identical before and after the destination update. -/
theorem after_representative_eq_before
    {before after : ReservationState} {mateRawAge : RawTokenAge}
    {conclusion : Vertex}
    (step : WaitDestinationStep before after mateRawAge conclusion)
    (token : RawTokenAge) :
    after.core.representative token = before.core.representative token := by
  rcases step.exact with
    ⟨_payload, _initialized, _updated, _marks, _nextAge, _sigma, _ready,
      coreEquation, _tags⟩
  rw [coreEquation]

end SequentialSchedulerBridge.WaitDestinationStep

namespace SequentialFigure7

namespace FutureWorkAt

/-- Every output future-work occurrence of a successful `wait` either
already existed in the prepared middle state or is the conclusion inserted
at the exact destination boundary.

The disjunction is intentionally not exclusive: the low-level waiting
prepend does not itself prohibit the inserted conclusion from already being
present in the old payload. -/
theorem beforeWaitOrInserted
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt after rawAge vertex) :
    FutureWorkAt step.prepared.after rawAge vertex ∨
      (rawAge = step.destination.boundary ∧
        vertex = step.consumer.conclusion) := by
  rcases step.destination.exact with
    ⟨oldPayload, oldInitialized, newInitialized, _marks, _nextAge,
      sigmaEquation, readyEquation, _core, _tags⟩
  cases work with
  | @ready position _ bucket _ sigmaAt readyAt member =>
      left
      apply FutureWorkAt.ready
      · rw [sigmaEquation] at sigmaAt
        exact sigmaAt
      · rw [readyEquation] at readyAt
        exact readyAt
      · exact member
  | @waiting _ payload _ waitingAt member =>
      by_cases sameBoundary : rawAge = step.destination.boundary
      · subst rawAge
        have payloadEquation :
            payload = step.consumer.conclusion :: oldPayload := by
          have exactCell := waitingAt.symm.trans newInitialized
          simpa using exactCell
        subst payload
        simp only [List.mem_cons] at member
        rcases member with head | tail
        · exact Or.inr ⟨rfl, head⟩
        · exact Or.inl (FutureWorkAt.waiting oldInitialized tail)
      · left
        apply FutureWorkAt.waiting
        · have waitingEquation :=
              SequentialStackState.prependWaiting?_of_ne
                step.destination.stack_eq sameBoundary
          rw [step.destination.output_eq] at waitingAt
          change step.destination.stackAfter.waiting[rawAge]? = _ at waitingAt
          exact waitingEquation.symm.trans waitingAt
        · exact member

end FutureWorkAt

/-- The exact structural data of a future `new` candidate created by the
conclusion inserted during one successful `wait`.

Its raw-age boundary and head are fixed by the enclosing wait step, so this
record stores only the tensor-below witness and its middle-state mate mark.
It carries no claim that the created region is separated from older events. -/
structure WaitCreatedCandidate (certificate : Certificate)
    {before after : ReservationState}
    (step : WaitStep certificate before after) : Type where
  tensor : TensorBelow
  tensor_valid :
    tensor.Valid certificate certificate.consumerIndex
      step.consumer.conclusion
  mate_unmarked :
    step.prepared.after.core.marks[tensor.mate]? = some none

/-- Additional geometry required for candidates introduced by one waiting
prepend.

The comparison is made in the prepared middle state, whose union-find carrier
is unchanged by the destination update.  Only strictly older current
representatives are constrained. -/
def WaitCreatedRegionSeparated
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (prior : CanonicalTagHistory certificate history)
    (step : WaitStep certificate before after) : Prop :=
  ∀ {event : ReservationEvent certificate},
    event ∈ prior.reservationLedger →
    ∀ created : WaitCreatedCandidate certificate step,
      step.prepared.after.core.representative event.rawAge <
          step.prepared.after.core.representative
            step.destination.boundary →
        SourceLeftRegionsDisjoint certificate event.start
          created.tensor.mate

namespace WaitStep

/-- A canonical `wait` history extension preserves older-source-region
separation provided the newly inserted conclusion satisfies the explicit
created-candidate geometry premise.

Candidates inherited from the prepared middle state are discharged by the
prior invariant and stable-prefix transport.  Candidates whose work witness
uses the inserted conclusion are discharged only by
`WaitCreatedRegionSeparated`. -/
theorem olderSourceRegionSeparated_of_created
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.wait, after⟩}
    (step : WaitStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderSourceRegionSeparated prior)
    (createdSeparated : WaitCreatedRegionSeparated prior step) :
    OlderSourceRegionSeparated
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
    have oldDisjoint :=
      separated.event_candidate oldEventMembership beforeCandidate olderBefore
    simpa [beforeCandidate, middleCandidate,
      FutureNewCandidateAt.beforePrepared] using oldDisjoint
  · let created : WaitCreatedCandidate certificate step := {
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
    have olderMiddle :
        step.prepared.after.core.representative event.rawAge <
          step.prepared.after.core.representative
            step.destination.boundary := by
      rw [← candidateAge]
      rw [← step.destination.after_representative_eq_before event.rawAge,
        ← step.destination.after_representative_eq_before candidate.rawAge]
      exact older
    simpa [created] using
      createdSeparated oldEventMembership created olderMiddle

end WaitStep

end SequentialFigure7

end ProofNetIR
