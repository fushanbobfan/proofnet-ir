import ProofNetIR.SequentialFigure7CommitmentEdgeTargetAvoidance

namespace ProofNetIR

/-!
# Figure-7 commitment-edge target-avoidance consumer

This consumer invokes the exact two-item public surface.  The theorem call
supplies the child-event untouched law explicitly and consumes the resulting
target-avoiding adjacent commitment path.
-/

open SequentialFigure7
open SequentialSchedulerBridge
open SequentialSchedulerState

#check CanonicalTagHistory.CommitmentEdgeTargetAvoidingPath
#check CanonicalTagHistory.commitmentEdge_referencePath_avoiding

/-- Invoke the public result predicate directly. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (parent child : RawTokenAge) (target : Vertex) : Prop :=
  tagHistory.CommitmentEdgeTargetAvoidingPath parent child target

/-- Invoke the theorem with its exact future-candidate and untouched inputs. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (candidate : FutureNewCandidateAt certificate state)
    {position parent child : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt : state.stack.sigma[position + 1]? = some child)
    (childUntouched : ∀ {event : ReservationEvent certificate},
      event ∈ tagHistory.reservationLedger → event.rawAge = child →
        ¬ event.Touched candidate.tensor.conclusion) :
    tagHistory.CommitmentEdgeTargetAvoidingPath parent child
      candidate.tensor.conclusion := by
  exact tagHistory.commitmentEdge_referencePath_avoiding invariant candidate
    parentAt childAt childUntouched

end ProofNetIR

/- Run the standalone commitment-edge target-avoidance API smoke consumer. -/
def main : IO Unit :=
  IO.println "Figure-7 commitment-edge target-avoidance API consumer passed."
