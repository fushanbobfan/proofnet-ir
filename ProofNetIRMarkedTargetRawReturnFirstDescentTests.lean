/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnFirstDescent

/-!
# Figure-7 marked-target raw-return first-descent consumer

This compile-time consumer destructs the authenticated first-step descent,
refines a supplied continuation-exit target, and calls the integrated Wait
theorem. It does not assume that the remaining descent is impossible.
-/

namespace ProofNetIR
namespace SequentialFigure7
namespace Consumer

open SequentialSchedulerState
open SequentialSchedulerBridge

private theorem observeFirstDescent
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin terminal : Vertex} {active : RawTokenAge}
    (descent :
      MarkedConclusionChainFirstRepresentativeDescent certificate state
        tagHistory origin terminal active) : True := by
  rcases descent with
    ⟨originAge, consumer, conclusionAge, originMarked,
      originRepresentative, conclusionMarked, authentic,
      conclusionNotGlobal, older, tail⟩
  have _originMarked := originMarked
  have _originRepresentative := originRepresentative
  have _conclusionMarked := conclusionMarked
  have _authentic := authentic
  have _conclusionNotGlobal := conclusionNotGlobal
  have _older := older
  have _tail := tail
  have _consumer := consumer
  trivial

private theorem observeFirstDescentTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationFirstDescentTarget
        tagHistory input component owned current) : True := by
  rcases target with
    ⟨path, directed, markedAge, pathStart, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetNeMate, targetMarked, authentic,
      representativeEq, targetConsumer, targetConsumerMateNeSelected,
      sourceConsumer, targetConclusionOutside, status⟩
  have _path := path
  have _directed := directed
  have _markedAge := markedAge
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
  rcases status with raw | descent | future | marked
  · rcases raw with
      ⟨terminal, chain, terminalConsumer, mateUnmarked, mateOutside⟩
    have _terminal := terminal
    have _chain := chain
    have _terminalConsumer := terminalConsumer
    have _mateUnmarked := mateUnmarked
    have _mateOutside := mateOutside
    trivial
  · exact observeFirstDescent descent
  · rcases future with
      ⟨terminal, chain, terminalConsumer, boundary, work,
        conclusionOutside, older⟩
    have _terminal := terminal
    have _chain := chain
    have _terminalConsumer := terminalConsumer
    have _boundary := boundary
    have _work := work
    have _conclusionOutside := conclusionOutside
    have _older := older
    trivial
  · rcases marked with
      ⟨terminal, chain, terminalConsumer, conclusionAge, conclusionMarked,
        conclusionGlobal, conclusionOutside, older⟩
    have _terminal := terminal
    have _chain := chain
    have _terminalConsumer := terminalConsumer
    have _conclusionAge := conclusionAge
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
      have _beforeTrace := beforeTrace
      have _afterTrace := afterTrace
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
      have _beforeTrace := beforeTrace
      have _afterTrace := afterTrace
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
      have _beforeTrace := beforeTrace
      have _afterTrace := afterTrace
      have _trace := trace
      exact observe exactStatus

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {origin terminal : Vertex}
    (chain : MarkedConclusionChain certificate state origin terminal)
    (different : origin ≠ terminal)
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {originAge : RawTokenAge}
    (originMarked : state.core.marks[origin]? = some (some originAge))
    (originRepresentative :
      state.core.representative originAge = input.rawAge)
    (originConsumer : ConnectiveBelow certificate origin)
    (originConclusionOutside : originConsumer.conclusion ∉ owned) : True :=
  observeFirstDescent
    (chain.firstRepresentativeDescent_of_ne tagHistory different input invariant
      componentLookup occurrence originMarked originRepresentative
      originConsumer originConclusionOutside)

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (current : ConnectiveBelow certificate input.vertex)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget
        tagHistory input component owned current) : True :=
  observeFirstDescentTarget
    (target.firstDescentTarget input invariant componentLookup occurrence current)

example {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (connected : certificate.ReferenceSwitchingConnected)
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (step : WaitStep certificate before after)
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
    (step.commitmentInterval_parTraceReentryMarkedContinuationFirstDescentOutcome
      connected tagHistory invariant componentLookup occurrence positive firstAt
      lastAt noTail)
  rintro ⟨mateOutside, mateMarked, representativeOlder, target⟩
  have _mateOutside := mateOutside
  have _mateMarked := mateMarked
  have _representativeOlder := representativeOlder
  exact observeFirstDescentTarget target

#print axioms MarkedConclusionChainFirstRepresentativeDescent
#print axioms MarkedConclusionChain.firstRepresentativeDescent_of_ne
#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationFirstDescentTarget
#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget.firstDescentTarget
#print axioms
  WaitStep.commitmentInterval_parTraceReentryMarkedContinuationFirstDescentOutcome

end Consumer
end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 raw-return first-descent consumer: kernel-green"
