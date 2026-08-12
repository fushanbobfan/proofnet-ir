import ProofNetIR.SequentialFigure7CommitmentIntervalTargetAvoidance

namespace ProofNetIR

/-!
# Figure-7 commitment-interval target-avoidance consumer

This consumer explicitly turns each supplied child-event untouched law into
one adjacent avoiding path and then invokes the interval-composition theorem.
-/

open SequentialFigure7
open SequentialSchedulerBridge
open SequentialSchedulerState

#check CanonicalTagHistory.CommitmentEdgeTargetAvoidingPath
#check CanonicalTagHistory.commitmentInterval_referencePath_avoiding

/-- Consume the interval theorem without deriving the per-child untouched
premises from any global history invariant. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (candidate : FutureNewCandidateAt certificate state)
    {position edgeCount : Nat} {first last : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : state.stack.sigma[position]? = some first)
    (lastAt : state.stack.sigma[position + edgeCount]? = some last)
    (childrenUntouched :
      ∀ {offset : Nat} {parent child : RawTokenAge},
        offset < edgeCount →
        state.stack.sigma[position + offset]? = some parent →
        state.stack.sigma[position + offset + 1]? = some child →
        ∀ {event : ReservationEvent certificate},
          event ∈ tagHistory.reservationLedger → event.rawAge = child →
            ¬ event.Touched candidate.tensor.conclusion) :
    tagHistory.CommitmentEdgeTargetAvoidingPath first last
      candidate.tensor.conclusion := by
  exact tagHistory.commitmentInterval_referencePath_avoiding positive firstAt
    lastAt (fun offsetLt parentAt childAt ↦
      tagHistory.commitmentEdge_referencePath_avoiding invariant candidate
        parentAt childAt (childrenUntouched offsetLt parentAt childAt))

end ProofNetIR

/- Run the standalone commitment-interval target-avoidance API consumer. -/
def main : IO Unit :=
  IO.println "Figure-7 commitment-interval target-avoidance API consumer passed."
