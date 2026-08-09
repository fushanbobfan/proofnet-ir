import ProofNetIR.SequentialFigure7CrossRepresentativeNewPreservation

open ProofNetIR
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialSchedulerState

/-!
# Cross-representative new-preservation consumer

This consumer checks the complete public API of the conditional
`new` preservation layer.  It does not assume that created source regions are
automatically separated and makes no progress or completeness claim.
-/

#check NewStep.preparedPrefix
#check NewStep.markedMiddle_nextAge_eq_event_rawAge
#check NewStep.after_nextAge_eq_event_rawAge_add_one
#check NewStep.after_representative_eq_markedMiddle
#check NewStep.after_marks_eq_markedMiddle
#check FutureWorkAt.beforeNewOrInserted
#check NewCreatedCandidate
#check NewCreatedRegionSeparated
#check NewStep.freshEvent_not_strictly_older
#check NewStep.olderSourceRegionSeparated_of_created

example {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) (head : Vertex)
    (endpoint : head = step.reached ∨ head = step.partner)
    (tensor : TensorBelow)
    (tensorValid :
      tensor.Valid certificate certificate.consumerIndex head)
    (mateUnmarked :
      step.markedMiddle.core.marks[tensor.mate]? = some none) :
    NewCreatedCandidate certificate step := {
  head
  endpoint
  tensor
  tensor_valid := tensorValid
  mate_unmarked := mateUnmarked }

example {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.new, after⟩}
    (step : NewStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderSourceRegionSeparated prior)
    (createdSeparated : NewCreatedRegionSeparated prior step) :
    OlderSourceRegionSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.new step)) :=
  step.olderSourceRegionSeparated_of_created prior separated createdSeparated

def main : IO Unit :=
  IO.println "Figure-7 cross-representative New-preservation consumers passed"
