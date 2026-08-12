import ProofNetIR.SequentialFigure7CommitmentSpine

namespace ProofNetIR

/-!
# Canonical Figure-7 commitment-spine consumer

This consumer exercises exactly the public commitment-spine surface.  The
surface records retained `sigma` allocation ancestry; it supplies no vertex
path, target-avoidance, raw-mark-separation, or progress theorem.
-/

open SequentialFigure7
open SequentialSchedulerBridge
open SequentialSchedulerState

#check ReservationEvent.Commits
#check ReservationEvent.Commits.new
#check CanonicalTagHistory.CommitmentSpine
#check CanonicalTagHistory.commitmentSpine

/- Consume the exact proof-relevant parent-child relation. -/
example {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    (ReservationEvent.new step).Commits step.stackResult.rawAge
      (ReservationEvent.new step).rawAge :=
  ReservationEvent.Commits.new step

/- Consume one adjacent retained commitment at its exact child ledger slot. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (spine : tagHistory.CommitmentSpine)
    {position parent child : Nat}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt : state.stack.sigma[position + 1]? = some child) :
    ∃ event : ReservationEvent certificate,
      tagHistory.reservationLedger[child]? = some event ∧
        event.Commits parent child :=
  spine position parent child parentAt childAt

/- Consume the history-wide theorem at an arbitrary canonical history. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history) :
    tagHistory.CommitmentSpine :=
  tagHistory.commitmentSpine

end ProofNetIR

/-- Run the standalone commitment-spine API smoke consumer. -/
def main : IO Unit :=
  IO.println "Figure-7 canonical commitment-spine API consumer passed."
