import ProofNetIR.SequentialFigure7TagHistory

namespace ProofNetIRTagHistoryCountTests

open ProofNetIR
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerBridge

/- Compile-only consumer fixture: downstream code can recover the exact
reservation-event/raw-age equation from an arbitrary certified tag history. -/
example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history) :
    tagHistory.linkIndices.length = state.stack.nextAge :=
  tagHistory.linkIndices_length_eq_nextAge

/- The per-event accounting lemma is independently usable by later history
invariants without assuming another dispatcher success. -/
example
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result) :
    evidence.linkIndices.length + before.stack.nextAge =
      result.after.stack.nextAge :=
  evidence.linkIndices_length_add_nextAge

end ProofNetIRTagHistoryCountTests

def main : IO Unit :=
  IO.println "Figure-7 tag-history count consumer fixture passed"
