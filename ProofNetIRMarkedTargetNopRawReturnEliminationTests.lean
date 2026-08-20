/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetNopRawReturnElimination

/-!
# Figure-7 marked-target Nop raw-return-elimination consumer

This compile-time consumer exercises the terminal-mark theorem, removes the
exact raw return from a supplied Nop target, destructs every remaining exit,
and calls the integrated commitment-interval theorem.
-/

namespace ProofNetIR
namespace SequentialFigure7
namespace Consumer

open SequentialSchedulerState
open SequentialSchedulerBridge

private theorem observeNoExactReturnTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationNoExactReturnTarget
        tagHistory input component owned current) : True := by
  rcases target with
    ⟨path, directed, markedAge, pathStart, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetNeMate, targetMarked, authentic,
      representativeEq, targetConsumer, targetConsumerMateNeSelected,
      sourceConsumer, targetConclusionOutside, status⟩
  have _pathEndpoints := path.walk.toChain
  have _pathStart := pathStart
  have _finishOwned := finishOwned
  have _directedMembership := directedMembership
  have _parentEdge := parentEdge
  have _targetNeSelected := targetNeSelected
  have _targetNeMate := targetNeMate
  have _targetMarked := targetMarked
  have _authentic := authentic
  have _representativeEq := representativeEq
  have _targetConsumerMateNeSelected := targetConsumerMateNeSelected
  have _sourceConsumer := sourceConsumer
  have _targetConclusionOutside := targetConclusionOutside
  rcases status with raw | future | marked
  · rcases raw with
      ⟨terminal, chain, terminalConsumer, mateUnmarked, mateOutside⟩
    have _chain := chain
    have _terminalConsumer := terminalConsumer
    have _mateUnmarked := mateUnmarked
    have _mateOutside := mateOutside
    trivial
  · rcases future with
      ⟨terminal, chain, terminalConsumer, boundary, work,
        conclusionOutside, older⟩
    have _chain := chain
    have _terminalConsumer := terminalConsumer
    have _work := work
    have _conclusionOutside := conclusionOutside
    have _older := older
    trivial
  · rcases marked with
      ⟨terminal, chain, terminalConsumer, conclusionAge, conclusionMarked,
        conclusionGlobal, conclusionOutside, older⟩
    have _chain := chain
    have _terminalConsumer := terminalConsumer
    have _conclusionMarked := conclusionMarked
    have _conclusionGlobal := conclusionGlobal
    have _conclusionOutside := conclusionOutside
    have _older := older
    trivial

private theorem observeCommitmentOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state}
    {consumer : ConnectiveBelow certificate input.vertex}
    {position edgeCount : Nat} {first : RawTokenAge} {status : Prop}
    (outcome : tagHistory.CommitmentIntervalParTraceOutcome input consumer
      position edgeCount first status)
    (observe : status → True) : True := by
  cases outcome with
  | avoiding path =>
      have _path := path
      trivial
  | equalSelected offset parent child event offsetLt parentAt childAt
      notAvoiding membership eventAge childEq side beforeTrace afterTrace trace =>
      have _offsetLt := offsetLt
      have _parentAt := parentAt
      have _childAt := childAt
      have _notAvoiding := notAvoiding
      have _membership := membership
      have _eventAge := eventAge
      have _childEq := childEq
      have _side := side
      have _trace := trace
      trivial
  | equalMate offset parent child event offsetLt parentAt childAt notAvoiding
      membership eventAge childEq side beforeTrace afterTrace trace =>
      have _offsetLt := offsetLt
      have _parentAt := parentAt
      have _childAt := childAt
      have _notAvoiding := notAvoiding
      have _membership := membership
      have _eventAge := eventAge
      have _childEq := childEq
      have _side := side
      have _trace := trace
      trivial
  | olderMate offset parent child event offsetLt parentAt childAt notAvoiding
      membership eventAge childLt side beforeTrace afterTrace trace exactStatus =>
      have _offsetLt := offsetLt
      have _parentAt := parentAt
      have _childAt := childAt
      have _notAvoiding := notAvoiding
      have _membership := membership
      have _eventAge := eventAge
      have _childLt := childLt
      have _side := side
      have _trace := trace
      exact observe exactStatus

example {certificate : Certificate} {state : ReservationState}
    {origin terminal : Vertex}
    (chain : MarkedConclusionChain certificate state origin terminal)
    (different : origin ≠ terminal) :
    ∃ rawAge, state.core.marks[terminal]? = some (some rawAge) :=
  chain.terminal_marked_of_ne different

example {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {tagHistory : CanonicalTagHistory certificate history}
    (step : NopStep certificate before after)
    {component : UnificationComponent} {owned : List Vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget
        tagHistory step.prepared.readyHeadInput component owned step.consumer) :
    True :=
  observeNoExactReturnTarget (target.nopNoExactReturnTarget step)

example {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (connected : certificate.ReferenceSwitchingConnected)
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (step : NopStep certificate before after)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      before.core.components[step.prepared.stackResult.rawAge]? =
        some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {position edgeCount : Nat} {first : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : before.stack.sigma[position]? = some first)
    (lastAt :
      before.stack.sigma[position + edgeCount]? =
        some step.prepared.stackResult.rawAge)
    (noTail :
      ¬ ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) : True := by
  apply observeCommitmentOutcome
    (step.commitmentInterval_parTraceReentryMarkedContinuationNoExactReturnOutcome
      connected tagHistory invariant componentLookup occurrence positive firstAt
      lastAt noTail)
  rintro ⟨mateOutside, mateUnmarked, target⟩
  have _mateOutside := mateOutside
  have _mateUnmarked := mateUnmarked
  exact observeNoExactReturnTarget target

#print axioms MarkedConclusionChain.terminal_marked_of_ne
#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationNoExactReturnTarget
#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget.nopNoExactReturnTarget
#print axioms
  NopStep.commitmentInterval_parTraceReentryMarkedContinuationNoExactReturnOutcome

end Consumer
end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 Nop raw-return elimination consumer: kernel-green"
