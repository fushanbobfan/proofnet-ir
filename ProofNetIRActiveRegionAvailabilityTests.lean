import ProofNetIR.SequentialFigure7ActiveRegionAvailability

namespace ProofNetIR

open SequentialFigure7
open SequentialSchedulerBridge
open SequentialUnification

#check CanonicalTagHistory.active_newSourceRegionInput_or_exactMarkedOwner
#check CanonicalTagHistory.active_newEnabled_or_exactMarkedOwner
#check CanonicalTagHistory.active_newEnabled_of_no_exactMarkedOwner

/- Consume the complete source-region-input versus old-owner dichotomy. -/
example {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (separated : OlderEventTouchSeparated tagHistory) :
    Nonempty (NewSourceRegionInput certificate before) ∨
      ∃ vertex,
        SourceLeftRegionVertex certificate guard.tensor.mate vertex ∧
          ExactMarkedOccurrenceOwner certificate before.core vertex :=
  tagHistory.active_newSourceRegionInput_or_exactMarkedOwner
    correct invariant guard separated

/- Consume the input-only `NewEnabled` versus old-owner dichotomy. -/
example {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (separated : OlderEventTouchSeparated tagHistory) :
    NewEnabled certificate before ∨
      ∃ vertex,
        SourceLeftRegionVertex certificate guard.tensor.mate vertex ∧
          ExactMarkedOccurrenceOwner certificate before.core vertex :=
  tagHistory.active_newEnabled_or_exactMarkedOwner
    correct invariant guard separated

/- Consume the owner-clear corollary through an explicit pointwise premise. -/
example {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (separated : OlderEventTouchSeparated tagHistory)
    (clearOwner :
      ∀ {vertex},
        SourceLeftRegionVertex certificate guard.tensor.mate vertex →
          ¬ ExactMarkedOccurrenceOwner certificate before.core vertex) :
    NewEnabled certificate before :=
  tagHistory.active_newEnabled_of_no_exactMarkedOwner
    correct invariant guard separated clearOwner

end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 active-region availability API consumer passed."
