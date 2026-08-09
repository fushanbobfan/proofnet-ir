import ProofNetIR.SequentialFigure7CrossRepresentativeForwardPreservation

open ProofNetIR
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialSchedulerState

/-!
# Cross-representative forward-preservation consumer

This narrow consumer type-checks the complete public API of the conditional
forward-preservation layer. Its structural examples construct only the explicit
created-candidate record and conditional preservation theorem; they do not
assert unconditional source-region geometry.
-/

#check ForwardStep.after_representative_eq_prepared
#check FutureWorkAt.beforeForwardOrInserted
#check ForwardCreatedCandidate
#check ForwardCreatedRegionSeparated
#check ForwardStep.olderSourceRegionSeparated_of_created

example {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) (tensor : TensorBelow)
    (tensorValid :
      tensor.Valid certificate certificate.consumerIndex
        step.consumer.conclusion)
    (mateUnmarked :
      step.prepared.after.core.marks[tensor.mate]? = some none) :
    ForwardCreatedCandidate certificate step := {
  tensor
  tensor_valid := tensorValid
  mate_unmarked := mateUnmarked }

example {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.forward, after⟩}
    (step : ForwardStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderSourceRegionSeparated prior)
    (createdSeparated : ForwardCreatedRegionSeparated prior step) :
    OlderSourceRegionSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.forward step)) :=
  step.olderSourceRegionSeparated_of_created prior separated createdSeparated

def main : IO Unit :=
  IO.println "Figure-7 cross-representative Forward-preservation consumers passed"
