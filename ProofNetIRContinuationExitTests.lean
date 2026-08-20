/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ContinuationExit

/-!
# Consumer checks for endpoint-localized continuation exits

This executable consumer destructs every public carrier field, applies every
public theorem, and prints the trusted dependencies before `main` runs.
-/

namespace ProofNetIR.SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

private theorem consumeMarkedConclusionChain
    {certificate : Certificate} {state : ReservationState}
    {origin terminal : Vertex}
    (chain : MarkedConclusionChain certificate state origin terminal) :
    True := by
  induction chain with
  | refl vertex =>
      have self : vertex = vertex := rfl
      cases self
      trivial
  | @step vertex terminal rawAge consumer marked notConclusion tail consumed =>
      have receipt :
          state.core.marks[consumer.conclusion]? = some (some rawAge) ∧
            consumer.conclusion ∉ certificate.conclusions ∧ True :=
        ⟨marked, notConclusion, consumed⟩
      exact receipt.2.2

private theorem consumeContinuationExit
    {certificate : Certificate} {state : ReservationState}
    {origin : Vertex}
    (exit : ContinuationExit certificate state origin) : True := by
  cases exit with
  | rawMate chain consumer mateUnmarked =>
      have receipt :
          state.core.marks[consumer.mate]? = some none ∧ True :=
        ⟨mateUnmarked, consumeMarkedConclusionChain chain⟩
      exact receipt.2
  | futureConclusion chain consumer boundary work =>
      have receipt :
          FutureWorkAt state boundary consumer.conclusion ∧ True :=
        ⟨work, consumeMarkedConclusionChain chain⟩
      exact receipt.2
  | markedGlobalConclusion chain consumer rawAge marked global =>
      have receipt :
          state.core.marks[consumer.conclusion]? = some (some rawAge) ∧
            consumer.conclusion ∈ certificate.conclusions ∧ True :=
        ⟨marked, global, consumeMarkedConclusionChain chain⟩
      exact receipt.2.2

private theorem consumeLocalizedContinuationExit
    {certificate : Certificate} {state : ReservationState}
    {origin : Vertex} {component : UnificationComponent}
    (localized :
      LocalizedContinuationExit certificate state origin component) :
    True := by
  cases localized with
  | rawMate chain consumer mateFrontier mateUnmarked =>
      have receipt :
          consumer.mate ∈ component.frontier ∧
            state.core.marks[consumer.mate]? = some none ∧ True :=
        ⟨mateFrontier, mateUnmarked, consumeMarkedConclusionChain chain⟩
      exact receipt.2.2
  | futureConclusion chain consumer boundary work conclusionFrontier
      conclusionNotGlobal =>
      have receipt :
          FutureWorkAt state boundary consumer.conclusion ∧
            consumer.conclusion ∈ component.frontier ∧
              consumer.conclusion ∉ certificate.conclusions ∧ True :=
        ⟨work, conclusionFrontier, conclusionNotGlobal,
          consumeMarkedConclusionChain chain⟩
      exact receipt.2.2.2

private theorem consumeActiveTopLocalization
    {certificate : Certificate} {state : ReservationState}
    (localized : ActiveTopContinuationExitLocalized certificate state)
    {rawAge markedAge : RawTokenAge}
    {component : UnificationComponent} {markedVertex : Vertex}
    (activeTop : state.stack.sigma.getLast? = some rawAge)
    (componentLookup :
      state.core.components[rawAge]? = some (some component))
    (markedFrontier : markedVertex ∈ component.frontier)
    (marked : state.core.marks[markedVertex]? = some (some markedAge))
    (notConclusion : markedVertex ∉ certificate.conclusions) : True :=
  consumeLocalizedContinuationExit
    (localized activeTop componentLookup markedFrontier marked notConclusion)

example
    {certificate : Certificate} {state : ReservationState}
    (continuation : MarkedNonconclusionContinuation certificate state)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (marked : state.core.marks[vertex]? = some (some rawAge))
    (notConclusion : vertex ∉ certificate.conclusions) : True :=
  consumeContinuationExit
    (continuation.continuationExit marked notConclusion)

example
    {certificate : Certificate} {state : ReservationState}
    {rawAge active : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt state rawAge vertex)
    (invariant : SchedulerInvariant certificate state)
    (drained : ActiveTopDrained state)
    (activeTop : state.stack.sigma.getLast? = some active) :
    rawAge < active :=
  work.rawAge_lt_active_of_activeTopDrained invariant drained activeTop

example
    {certificate : Certificate} {state : ReservationState}
    {origin : Vertex} {active : RawTokenAge}
    (exit : ContinuationExit certificate state origin)
    (invariant : SchedulerInvariant certificate state)
    (drained : ActiveTopDrained state)
    (activeTop : state.stack.sigma.getLast? = some active) : True := by
  apply exit.elim_of_activeTopDrained invariant drained activeTop
  · intro terminal chain consumer mateNotConclusion mateUnmarked
    have receipt :
        consumer.mate ∉ certificate.conclusions ∧
          state.core.marks[consumer.mate]? = some none :=
      ⟨mateNotConclusion, mateUnmarked⟩
    have combined :
        (consumer.mate ∉ certificate.conclusions ∧
          state.core.marks[consumer.mate]? = some none) ∧ True :=
      ⟨receipt, consumeMarkedConclusionChain chain⟩
    exact combined.2
  · intro terminal chain consumer boundary work older unmarked
    have receipt :
        FutureWorkAt state boundary consumer.conclusion ∧
          boundary < active ∧
            state.core.marks[consumer.conclusion]? = some none :=
      ⟨work, older, unmarked⟩
    have combined :
        (FutureWorkAt state boundary consumer.conclusion ∧
          boundary < active ∧
            state.core.marks[consumer.conclusion]? = some none) ∧ True :=
      ⟨receipt, consumeMarkedConclusionChain chain⟩
    exact combined.2
  · intro terminal chain consumer rawAge marked global
    have receipt :
        state.core.marks[consumer.conclusion]? = some (some rawAge) ∧
          consumer.conclusion ∈ certificate.conclusions :=
      ⟨marked, global⟩
    have combined :
        (state.core.marks[consumer.conclusion]? = some (some rawAge) ∧
          consumer.conclusion ∈ certificate.conclusions) ∧ True :=
      ⟨receipt, consumeMarkedConclusionChain chain⟩
    exact combined.2

example
    {certificate : Certificate} {state : ReservationState}
    {origin : Vertex} {component : UnificationComponent}
    (localized :
      LocalizedContinuationExit certificate state origin component) : True :=
  consumeContinuationExit localized.continuationExit

example
    {certificate : Certificate} {state : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (queuedUnmarked : QueuedVerticesUnmarked state)
    (localized : ActiveTopContinuationExitLocalized certificate state) :
    ActiveTopMarkedNonconclusionDebt certificate state :=
  activeTopMarkedNonconclusionDebt_of_continuationExitLocalized
    structural queuedUnmarked localized

example
    {certificate : Certificate} {state : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (drained : ActiveTopDrained state)
    (localized : ActiveTopContinuationExitLocalized certificate state) :
    state.core.allMarked = true :=
  SchedulerInvariant.allMarked_of_activeTopDrained_of_continuationExitLocalized
    correct invariant drained localized

example
    {certificate : Certificate} {state : ReservationState}
    (localized : ActiveTopContinuationExitLocalized certificate state)
    {rawAge markedAge : RawTokenAge}
    {component : UnificationComponent} {markedVertex : Vertex}
    (activeTop : state.stack.sigma.getLast? = some rawAge)
    (componentLookup :
      state.core.components[rawAge]? = some (some component))
    (markedFrontier : markedVertex ∈ component.frontier)
    (marked : state.core.marks[markedVertex]? = some (some markedAge))
    (notConclusion : markedVertex ∉ certificate.conclusions) : True :=
  consumeActiveTopLocalization localized activeTop componentLookup
    markedFrontier marked notConclusion

#print axioms MarkedNonconclusionContinuation.continuationExit
#print axioms FutureWorkAt.rawAge_lt_active_of_activeTopDrained
#print axioms ContinuationExit.elim_of_activeTopDrained
#print axioms LocalizedContinuationExit.continuationExit
#print axioms activeTopMarkedNonconclusionDebt_of_continuationExitLocalized
#print axioms SchedulerInvariant.allMarked_of_activeTopDrained_of_continuationExitLocalized

end ProofNetIR.SequentialFigure7

def main : IO Unit :=
  IO.println "Figure-7 endpoint-localized continuation reduction: kernel-green"
