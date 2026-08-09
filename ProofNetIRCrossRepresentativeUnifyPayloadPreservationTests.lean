import ProofNetIR.SequentialFigure7CrossRepresentativeUnifyPayloadPreservation

open ProofNetIR
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialSchedulerState

/-!
# Cross-representative UnifyPayload-preservation consumer

This consumer checks the public API of the conditional `unifyPayload`
preservation layer.  It supplies the created-region premise explicitly and
makes no unconditional preservation, progress, or completeness claim.
-/

#check UnifyPayloadStep.after_marks_eq_prepared
#check UnifyPayloadStep.after_representative_eq_prepared_if
#check FutureNewCandidateAt.rawAge_le_previousBoundary_of_unifyPayload
#check FutureWorkAt.beforeUnifyPayloadOrMovedOrCreated
#check UnifyPayloadCreatedCandidate
#check UnifyPayloadCreatedRegionSeparated
#check UnifyPayloadStep.olderSourceRegionSeparated_of_created

example {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (tensor : TensorBelow)
    (tensorValid :
      tensor.Valid certificate certificate.consumerIndex
        step.consumer.conclusion)
    (mateUnmarked :
      step.prepared.after.core.marks[tensor.mate]? = some none) :
    UnifyPayloadCreatedCandidate certificate step := {
  tensor
  tensor_valid := tensorValid
  mate_unmarked := mateUnmarked }

example {certificate : Certificate} {before after : ReservationState}
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
        (DispatchTagEvidence.unifyPayload step)) :=
  step.olderSourceRegionSeparated_of_created prior separated createdSeparated

def main : IO Unit :=
  IO.println "Figure-7 cross-representative UnifyPayload consumers passed"
