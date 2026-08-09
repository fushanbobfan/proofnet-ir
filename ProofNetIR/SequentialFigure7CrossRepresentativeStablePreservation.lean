import ProofNetIR.SequentialFigure7ActiveRegionTouchOrder

namespace ProofNetIR

/-!
# Stable Figure-7 preservation of cross-representative source separation

This module transports `OlderSourceRegionSeparated` through the synchronized
pop/raw-mark prefix and then through the exact `concl` and `nop` dispatcher
branches.  The prefix removes one ready head, preserves the exact boundary of
every remaining ready or waiting occurrence, changes no union-find parent,
and cannot turn a previously marked tensor mate into an unmarked one.

The `PreparedStep` theorem keeps the history transition explicit through an
output equation and equality of reservation ledgers: a prepared prefix is not
itself an `ExecutedHistory` edge.  The `concl` and `nop` corollaries instantiate
that helper with their canonical stable history extensions.  No preservation
claim for `new`, `wait`, `forward`, or `unifyPayload` is made here.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

namespace FutureWorkAt

/-- Every exact future-work occurrence remaining after the synchronized
prefix already existed at the same raw-age boundary before the prefix.

For the active ready bucket, the old witness uses the original bucket with
the selected head restored; waiting cells and all other ready buckets are
unchanged. -/
theorem beforePrepared
    {before : ReservationState} (step : PreparedStep before)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt step.after rawAge vertex) :
    FutureWorkAt before rawAge vertex := by
  rcases SequentialStackState.popReadyMark?_exact step.stack_eq with
    ⟨topEquation, _sigmaTop, _unmarked, _marks, _nextAge,
      sigmaEquation, readyEquation, waitingEquation, _marked⟩
  rcases List.getLast?_eq_some_iff.mp topEquation with
    ⟨readyPrefix, readyDecomposition⟩
  have afterReady :
      step.after.stack.ready =
        readyPrefix ++ [step.stackResult.remainingTop] := by
    change step.stackResult.after.ready = _
    rw [readyEquation, readyDecomposition]
    simp
  have afterSigma : step.after.stack.sigma = before.stack.sigma := by
    change step.stackResult.after.sigma = before.stack.sigma
    exact sigmaEquation
  have afterWaiting : step.after.stack.waiting = before.stack.waiting := by
    change step.stackResult.after.waiting = before.stack.waiting
    exact waitingEquation
  cases work with
  | @ready position _ bucket _ sigmaAt readyAt member =>
      have positionBound :
          position < (readyPrefix ++ [step.stackResult.remainingTop]).length := by
        rw [← afterReady]
        exact (List.getElem?_eq_some_iff.mp readyAt).1
      have oldSigmaAt : before.stack.sigma[position]? = some rawAge := by
        rw [afterSigma] at sigmaAt
        exact sigmaAt
      by_cases inPrefix : position < readyPrefix.length
      · apply FutureWorkAt.ready oldSigmaAt
        · rw [readyDecomposition, List.getElem?_append_left inPrefix]
          rw [afterReady, List.getElem?_append_left inPrefix] at readyAt
          exact readyAt
        · exact member
      · have positionTop : position = readyPrefix.length := by
          simp at positionBound
          omega
        subst position
        have bucketEquation : bucket = step.stackResult.remainingTop := by
          rw [afterReady] at readyAt
          simp at readyAt
          exact readyAt.symm
        subst bucket
        apply FutureWorkAt.ready
            (position := readyPrefix.length)
            (bucket :=
              step.stackResult.vertex :: step.stackResult.remainingTop)
            oldSigmaAt
        · rw [readyDecomposition]
          simp
        · exact List.mem_cons_of_mem _ member
  | @waiting _ payload _ waitingAt member =>
      apply FutureWorkAt.waiting
      · rw [afterWaiting] at waitingAt
        exact waitingAt
      · exact member

end FutureWorkAt

namespace PreparedStep

/-- The synchronized prefix changes no union-find parent, hence every token
has the same current representative before and after the prefix. -/
theorem after_representative_eq_before
    {before : ReservationState} (step : PreparedStep before)
    (token : RawTokenAge) :
    step.after.core.representative token = before.core.representative token := by
  have parentsEquation :=
    (UnificationState.markReadyRaw?_carriers step.core_mark_eq).1
  simp [PreparedStep.after, UnificationState.representative, parentsEquation]

end PreparedStep

namespace FutureNewCandidateAt

/-- A future `new` candidate surviving the synchronized prefix was already a
candidate before it, at the same exact boundary and tensor occurrence.

The only new raw mark belongs to the consumed ready head.  Since the
post-prefix candidate mate is unmarked, it is distinct from that head and its
pre-prefix mark was also empty. -/
def beforePrepared
    {certificate : Certificate} {before : ReservationState}
    (step : PreparedStep before)
    (candidate : FutureNewCandidateAt certificate step.after) :
    FutureNewCandidateAt certificate before where
  rawAge := candidate.rawAge
  head := candidate.head
  work := candidate.work.beforePrepared step
  tensor := candidate.tensor
  tensor_valid := candidate.tensor_valid
  mate_unmarked := by
    rcases UnificationState.markReadyRaw?_exact step.core_mark_eq with
      ⟨_oldSelected, afterMarks, _parents, _components, _started, _fired,
        selectedMarked⟩
    have selectedNeMate :
        step.stackResult.vertex ≠ candidate.tensor.mate := by
      intro same
      have mateUnmarked := candidate.mate_unmarked
      change step.coreMarked.marks[candidate.tensor.mate]? = some none at mateUnmarked
      rw [← same, selectedMarked] at mateUnmarked
      simp at mateUnmarked
    have mateUnmarked := candidate.mate_unmarked
    change step.coreMarked.marks[candidate.tensor.mate]? = some none at mateUnmarked
    rw [afterMarks] at mateUnmarked
    simpa [Array.getElem?_setIfInBounds, selectedNeMate] using mateUnmarked

end FutureNewCandidateAt

namespace PreparedStep

/-- Cross-representative source-region separation transports through a
synchronized prefix whenever the output history records the same reservation
ledger.

The explicit output equation and ledger equality are essential: a
`PreparedStep` alone is not an `ExecutedHistory` edge and cannot manufacture a
canonical history for its middle state. -/
theorem olderSourceRegionSeparated
    {certificate : Certificate} {before after : ReservationState}
    (step : PreparedStep before) (outputEquation : after = step.after)
    {beforeHistory : ExecutedHistory certificate before}
    (beforeTags : CanonicalTagHistory certificate beforeHistory)
    (separated : OlderSourceRegionSeparated beforeTags)
    {afterHistory : ExecutedHistory certificate after}
    (afterTags : CanonicalTagHistory certificate afterHistory)
    (ledgerEquation :
      afterTags.reservationLedger = beforeTags.reservationLedger) :
    OlderSourceRegionSeparated afterTags := by
  subst after
  refine { event_candidate := ?_ }
  intro event eventMembership candidate older
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
  have oldDisjoint :=
    separated.event_candidate oldEventMembership beforeCandidate olderBefore
  simpa [beforeCandidate, FutureNewCandidateAt.beforePrepared] using oldDisjoint

end PreparedStep

namespace ConclStep

/-- A canonical `concl` history extension preserves
`OlderSourceRegionSeparated`.  It contributes no reservation event and its
output is exactly the prepared middle state. -/
theorem olderSourceRegionSeparated
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch :
      DispatchStep certificate before invariant ⟨.concl, after⟩}
    (step : ConclStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderSourceRegionSeparated prior) :
    OlderSourceRegionSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.concl step)) := by
  apply step.prepared.olderSourceRegionSeparated step.output_eq prior separated
  simp [CanonicalTagHistory.reservationLedger,
    DispatchTagEvidence.reservationEvents]

end ConclStep

namespace NopStep

/-- A canonical `nop` history extension preserves
`OlderSourceRegionSeparated`.  Like `concl`, it contributes no reservation
event and its output is exactly the prepared middle state. -/
theorem olderSourceRegionSeparated
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.nop, after⟩}
    (step : NopStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderSourceRegionSeparated prior) :
    OlderSourceRegionSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.nop step)) := by
  apply step.prepared.olderSourceRegionSeparated step.output_eq prior separated
  simp [CanonicalTagHistory.reservationLedger,
    DispatchTagEvidence.reservationEvents]

end NopStep

end SequentialFigure7

end ProofNetIR
