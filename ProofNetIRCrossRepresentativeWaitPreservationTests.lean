import ProofNetIR.SequentialFigure7CrossRepresentativeWaitPreservation

open ProofNetIR
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialSchedulerState

/-!
# Cross-representative wait-preservation consumer

This narrow consumer type-checks the complete public API of the conditional
wait-preservation layer.  Its structural examples construct only the explicit
created-candidate record and conditional preservation theorem; they do not
assert unconditional source-region geometry.
-/

#check WaitDestinationStep.after_representative_eq_before
#check FutureWorkAt.beforeWaitOrInserted
#check WaitCreatedCandidate
#check WaitCreatedRegionSeparated
#check WaitStep.olderSourceRegionSeparated_of_created

example {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after) (tensor : TensorBelow)
    (tensorValid :
      tensor.Valid certificate certificate.consumerIndex
        step.consumer.conclusion)
    (mateUnmarked :
      step.prepared.after.core.marks[tensor.mate]? = some none) :
    WaitCreatedCandidate certificate step := {
  tensor
  tensor_valid := tensorValid
  mate_unmarked := mateUnmarked }

example {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.wait, after⟩}
    (step : WaitStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderSourceRegionSeparated prior)
    (createdSeparated : WaitCreatedRegionSeparated prior step) :
    OlderSourceRegionSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.wait step)) :=
  step.olderSourceRegionSeparated_of_created prior separated createdSeparated

def main : IO Unit :=
  IO.println "Figure-7 cross-representative Wait-preservation consumers passed"
