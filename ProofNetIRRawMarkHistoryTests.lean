import ProofNetIR.SequentialFigure7RawMarkHistory

namespace ProofNetIR

open SequentialFigure7
open SequentialSchedulerBridge
open SequentialSchedulerState

#check DispatchTagEvidence.prepared
#check DispatchTagEvidence.RawMarked
#check DispatchTagEvidence.final_rawMarked_iff_old_or_event
#check CanonicalTagHistory.RawMarked
#check CanonicalTagHistory.final_rawMarked_iff
#check ExecutedHistory.final_rawMarked_has_event
#check ReachableByImplementedDispatcher.final_rawMarked_has_event

/- Consume the common prepared prefix retained by every branch witness. -/
example {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result) :
    PreparedStep before :=
  evidence.prepared

/- Consume the exact one-event raw-mark predicate. -/
example {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result)
    (rawAge : RawTokenAge) (vertex : Vertex) :
    evidence.RawMarked rawAge vertex ↔
      rawAge = evidence.prepared.stackResult.rawAge ∧
        vertex = evidence.prepared.stackResult.vertex :=
  Iff.rfl

/- Consume the one-step old-mark-or-current-event characterization. -/
example {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result)
    {rawAge : RawTokenAge} {vertex : Vertex} :
    result.after.core.marks[vertex]? = some (some rawAge) ↔
      before.core.marks[vertex]? = some (some rawAge) ∨
        evidence.RawMarked rawAge vertex :=
  evidence.final_rawMarked_iff_old_or_event

/- Consume the history-wide raw-mark predicate as a proposition. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (rawAge : RawTokenAge) (vertex : Vertex) :
    tagHistory.RawMarked rawAge vertex →
      tagHistory.RawMarked rawAge vertex :=
  fun marked ↦ marked

/- Consume the exact final-state characterization. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {rawAge : RawTokenAge} {vertex : Vertex} :
    state.core.marks[vertex]? = some (some rawAge) ↔
      tagHistory.RawMarked rawAge vertex :=
  tagHistory.final_rawMarked_iff

/- Recover an authentic event from a concrete final mark in one history. -/
example {certificate : Certificate} {state : ReservationState}
    (history : ExecutedHistory certificate state)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (marked : state.core.marks[vertex]? = some (some rawAge)) :
    ∃ tagHistory : CanonicalTagHistory certificate history,
      tagHistory.RawMarked rawAge vertex :=
  history.final_rawMarked_has_event marked

/- Recover both history carriers from the reachability facade. -/
example {certificate : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate state)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (marked : state.core.marks[vertex]? = some (some rawAge)) :
    ∃ history : ExecutedHistory certificate state,
      ∃ tagHistory : CanonicalTagHistory certificate history,
        tagHistory.RawMarked rawAge vertex :=
  reachable.final_rawMarked_has_event marked

end ProofNetIR

/-- Run the standalone raw-mark-history API smoke test. -/
def main : IO Unit :=
  IO.println "Figure-7 canonical raw-mark history API consumer passed."
