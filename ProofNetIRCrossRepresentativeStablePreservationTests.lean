import ProofNetIR.SequentialFigure7CrossRepresentativeStablePreservation

namespace ProofNetIRCrossRepresentativeStablePreservationTests

open ProofNetIR
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialSchedulerState

/-! ## Prepared-prefix transport consumers -/

example {before : ReservationState} (step : PreparedStep before)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt step.after rawAge vertex) :
    FutureWorkAt before rawAge vertex :=
  work.beforePrepared step

example {before : ReservationState} (step : PreparedStep before)
    (rawAge : RawTokenAge) :
    step.after.core.representative rawAge =
      before.core.representative rawAge :=
  step.after_representative_eq_before rawAge

example {certificate : Certificate} {before : ReservationState}
    (step : PreparedStep before)
    (candidate : FutureNewCandidateAt certificate step.after) :
    FutureNewCandidateAt certificate before :=
  candidate.beforePrepared step

example {certificate : Certificate} {before after : ReservationState}
    (step : PreparedStep before) (outputEquation : after = step.after)
    {beforeHistory : ExecutedHistory certificate before}
    (beforeTags : CanonicalTagHistory certificate beforeHistory)
    (separated : OlderSourceRegionSeparated beforeTags)
    {afterHistory : ExecutedHistory certificate after}
    (afterTags : CanonicalTagHistory certificate afterHistory)
    (ledgerEquation :
      afterTags.reservationLedger = beforeTags.reservationLedger) :
    OlderSourceRegionSeparated afterTags :=
  step.olderSourceRegionSeparated outputEquation beforeTags separated afterTags
    ledgerEquation

/-! ## Canonical stable-branch consumers -/

example {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.concl, after⟩}
    (step : ConclStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderSourceRegionSeparated prior) :
    OlderSourceRegionSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.concl step)) :=
  step.olderSourceRegionSeparated prior separated

example {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.nop, after⟩}
    (step : NopStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderSourceRegionSeparated prior) :
    OlderSourceRegionSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.nop step)) :=
  step.olderSourceRegionSeparated prior separated

end ProofNetIRCrossRepresentativeStablePreservationTests

def main : IO Unit :=
  IO.println "Figure-7 cross-representative stable-preservation consumers passed"
