import ProofNetIR.SequentialFigure7ActiveTopDebtParentExternalTemporalOutcome

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

private inductive ExternalObservation : Prop where
  | raw (sibling : Vertex)
  | future (conclusion : Vertex) (boundary : RawTokenAge)
  | marked (conclusion : Vertex) (rawAge : RawTokenAge)

private theorem observeExternal
    {certificate : Certificate} {state : ReservationState}
    {activeRawAge : RawTokenAge} {owned : List Vertex}
    (outcome : ActiveCarrierParentExternalTemporalOutcome certificate state
      activeRawAge owned) :
    ExternalObservation := by
  have _forgotten := outcome.temporalOutcome (selected := 0)
  cases outcome with
  | rawOutside sibling unmarked outside =>
      have _ := unmarked
      have _ := outside
      exact .raw sibling
  | olderFuture conclusion boundary work older outside =>
      have _ := work
      have _ := older
      have _ := outside
      exact .future conclusion boundary
  | olderMarked conclusion rawAge marked older outside =>
      have _ := marked
      have _ := older
      have _ := outside
      exact .marked conclusion rawAge

private theorem consumeNop
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (step : NopStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (noTail :
      ¬ ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) :
    Nonempty ExternalObservation := by
  rcases step.externalParentTemporalOutcome_of_no_readyTail
      tagHistory correct invariant noTail with
    ⟨_component, _usedLinks, _owned, _lookup, _occurrence, _accounted,
      outcome⟩
  exact ⟨observeExternal outcome⟩

private theorem consumeWait
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (noTail :
      ¬ ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) :
    Nonempty ExternalObservation := by
  rcases step.externalParentTemporalOutcome_of_no_readyTail
      tagHistory correct invariant noTail with
    ⟨_component, _usedLinks, _owned, _lookup, _occurrence, _accounted,
      outcome⟩
  exact ⟨observeExternal outcome⟩

#print axioms ActiveCarrierParentExternalTemporalOutcome
#print axioms ActiveCarrierParentExternalTemporalOutcome.temporalOutcome
#print axioms NopStep.externalParentTemporalOutcome_of_no_readyTail
#print axioms WaitStep.externalParentTemporalOutcome_of_no_readyTail

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "active-top debt external parent temporal outcome: kernel-green"
