import ProofNetIR.SequentialFigure7OlderRawMarkedRegionSeparation

namespace ProofNetIR

open SequentialFigure7
open SequentialSchedulerBridge
open SequentialUnification

#check OlderRawMarksSeparatedFrom
#check OlderRawMarkedRegionSeparated
#check SchedulerInvariant.exactMarkedOccurrenceOwner_iff_exists_rawMark
#check empty_olderRawMarkedRegionSeparated
#check InitialReservationStep.olderRawMarkedRegionSeparated
#check PreparedStep.olderRawMarkedRegionSeparated
#check ConclStep.olderRawMarkedRegionSeparated
#check NopStep.olderRawMarkedRegionSeparated
#check NewGuard.marked_representative_le_active
#check OlderRawMarkedRegionSeparated.active_sourceLeftRegion_no_rawMark
#check OlderRawMarkedRegionSeparated.active_clearOwner

/- Build the generic primitive from its raw-age and mate-indexed contract. -/
example {certificate : Certificate} {state : ReservationState}
    {candidateRawAge : SequentialSchedulerState.RawTokenAge}
    {candidateMate : Vertex}
    (separated :
      ∀ rawAge vertex,
        state.core.marks[vertex]? = some (some rawAge) →
          state.core.representative rawAge <
              state.core.representative candidateRawAge →
            ¬ SourceLeftRegionVertex certificate candidateMate vertex) :
    OlderRawMarksSeparatedFrom certificate state candidateRawAge
      candidateMate :=
  separated

/- Build and project the future-candidate bundle as a downstream client. -/
example {certificate : Certificate} {state : ReservationState}
    (candidateSeparation :
      ∀ candidate : FutureNewCandidateAt certificate state,
        OlderRawMarksSeparatedFrom certificate state candidate.rawAge
          candidate.tensor.mate) :
    OlderRawMarkedRegionSeparated certificate state :=
  { candidate := candidateSeparation }

/- Project one queued candidate into the generic separation primitive. -/
example {certificate : Certificate} {state : ReservationState}
    (separated : OlderRawMarkedRegionSeparated certificate state)
    (candidate : FutureNewCandidateAt certificate state) :
    OlderRawMarksSeparatedFrom certificate state candidate.rawAge
      candidate.tensor.mate :=
  separated.candidate candidate

/- Consume the occurrence-owner equivalence through a complete invariant. -/
example {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {vertex : Vertex} :
    ExactMarkedOccurrenceOwner certificate state.core vertex ↔
      ∃ rawAge, state.core.marks[vertex]? = some (some rawAge) :=
  SchedulerInvariant.exactMarkedOccurrenceOwner_iff_exists_rawMark invariant

/- Consume the empty-state constructor without a reachability assumption. -/
example (certificate : Certificate) :
    OlderRawMarkedRegionSeparated certificate
      (ReservationState.empty certificate) :=
  empty_olderRawMarkedRegionSeparated certificate

/- Consume the initial-step constructor on its exact output state. -/
example {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    OlderRawMarkedRegionSeparated certificate after :=
  InitialReservationStep.olderRawMarkedRegionSeparated step

/- Consume unconditional synchronized-prefix preservation. -/
example {certificate : Certificate} {before : ReservationState}
    (step : PreparedStep before)
    (invariant : SchedulerInvariant certificate before)
    (separated : OlderRawMarkedRegionSeparated certificate before) :
    OlderRawMarkedRegionSeparated certificate step.after :=
  step.olderRawMarkedRegionSeparated invariant separated

/- Consume exact `concl` preservation directly. -/
example {certificate : Certificate} {before after : ReservationState}
    (step : ConclStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (separated : OlderRawMarkedRegionSeparated certificate before) :
    OlderRawMarkedRegionSeparated certificate after :=
  step.olderRawMarkedRegionSeparated invariant separated

/- Consume exact `nop` preservation directly. -/
example {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (separated : OlderRawMarkedRegionSeparated certificate before) :
    OlderRawMarkedRegionSeparated certificate after :=
  step.olderRawMarkedRegionSeparated invariant separated

/- Consume the active representative upper bound for one concrete mark. -/
example {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {vertex rawAge : Nat}
    (marked : before.core.marks[vertex]? = some (some rawAge)) :
    before.core.representative rawAge ≤
      before.core.representative guard.head.rawAge :=
  guard.marked_representative_le_active invariant marked

/- Consume active source-region raw-mark exclusion directly. -/
example {certificate : Certificate} {before : ReservationState}
    (separated : OlderRawMarkedRegionSeparated certificate before)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {vertex : Vertex}
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex) :
    ¬ ∃ rawAge, before.core.marks[vertex]? = some (some rawAge) :=
  separated.active_sourceLeftRegion_no_rawMark
    correct invariant guard region

/- Consume the pointwise owner-clear theorem directly. -/
example {certificate : Certificate} {before : ReservationState}
    (separated : OlderRawMarkedRegionSeparated certificate before)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {vertex : Vertex}
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex) :
    ¬ ExactMarkedOccurrenceOwner certificate before.core vertex :=
  separated.active_clearOwner correct invariant guard region

/- Consume the owner-clear theorem in the actual active-availability API. -/
example {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (eventSeparated : OlderEventTouchSeparated tagHistory)
    (rawSeparated : OlderRawMarkedRegionSeparated certificate before) :
    NewEnabled certificate before :=
  tagHistory.active_newEnabled_of_no_exactMarkedOwner
    correct invariant guard eventSeparated
      (rawSeparated.active_clearOwner correct invariant guard)

end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 older raw-marked region separation consumer passed."
