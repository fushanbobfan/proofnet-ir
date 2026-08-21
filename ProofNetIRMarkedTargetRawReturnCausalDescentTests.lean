/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnCausalDescent

/-!
# Figure-7 marked-target raw-return causal-descent consumer

This compile-time consumer projects strict raw-mark order, reconstructs the
two-premise causal theorem, destructs the sibling continuation exit, refines a
supplied target, and calls the integrated Wait theorem.  It does not assume
that the causal descent or any retained exit is impossible.
-/

namespace ProofNetIR
namespace SequentialFigure7
namespace Consumer

open SequentialSchedulerState
open SequentialSchedulerBridge

private theorem observeBefore
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {firstAge secondAge : RawTokenAge} {first second : Vertex}
    (before : tagHistory.RawMarkedBefore firstAge first secondAge second) :
    True := by
  have _first := before.first_rawMarked
  have _second := before.second_rawMarked
  have _different := before.vertex_ne
  trivial

private theorem observeExit
    {certificate : Certificate} {state : ReservationState} {origin : Vertex}
    (exit : ContinuationExit certificate state origin) : True := by
  cases exit with
  | rawMate chain consumer mateUnmarked =>
      have _chain := chain
      have _consumer := consumer
      have _mateUnmarked := mateUnmarked
      trivial
  | futureConclusion chain consumer boundary work =>
      have _chain := chain
      have _consumer := consumer
      have _boundary := boundary
      have _work := work
      trivial
  | markedGlobalConclusion chain consumer rawAge marked global =>
      have _chain := chain
      have _consumer := consumer
      have _rawAge := rawAge
      have _marked := marked
      have _global := global
      trivial

private theorem observeCausalDescent
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin terminal : Vertex} {active : RawTokenAge}
    (descent :
      MarkedConclusionChainFirstCausalDescent certificate state tagHistory
        origin terminal active) : True := by
  rcases descent with
    ⟨originAge, consumer, conclusionAge, mateAge, originMarked,
      originRepresentative, conclusionMarked, conclusionEvent,
      conclusionNotGlobal, conclusionOlder, premiseBefore, mateBefore,
      mateExit, tail⟩
  have _originAge := originAge
  have _consumer := consumer
  have _conclusionAge := conclusionAge
  have _mateAge := mateAge
  have _originMarked := originMarked
  have _originRepresentative := originRepresentative
  have _conclusionMarked := conclusionMarked
  have _conclusionEvent := conclusionEvent
  have _conclusionNotGlobal := conclusionNotGlobal
  have _conclusionOlder := conclusionOlder
  have _tail := tail
  have _premiseOrder := observeBefore premiseBefore
  have _mateOrder := observeBefore mateBefore
  exact observeExit mateExit

private theorem observeCausalTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCausalDescentTarget
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
  have _targetConsumer := targetConsumer
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
  · exact observeCausalDescent descent
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
    {vertex : Vertex} (consumer : ConnectiveBelow certificate vertex)
    {conclusionAge : RawTokenAge}
    (event : tagHistory.RawMarked conclusionAge consumer.conclusion) : True := by
  rcases tagHistory.rawMarkedPremisesBefore consumer event with
    ⟨_premiseAge, _mateAge, premiseBefore, mateBefore⟩
  have _premiseOrder := observeBefore premiseBefore
  exact observeBefore mateBefore

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin terminal : Vertex} {active : RawTokenAge}
    (invariant : SchedulerInvariant certificate state)
    (descent :
      MarkedConclusionChainFirstRepresentativeDescent certificate state
        tagHistory origin terminal active) : True :=
  observeCausalDescent (descent.causalDescent invariant)

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationFirstDescentTarget
        tagHistory input component owned current) : True :=
  observeCausalTarget (target.causalDescentTarget input invariant)

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
    (step.commitmentInterval_parTraceReentryMarkedContinuationCausalDescentOutcome
      connected tagHistory invariant componentLookup occurrence positive firstAt
      lastAt noTail)
  rintro ⟨mateOutside, mateMarked, representativeOlder, target⟩
  have _mateOutside := mateOutside
  have _mateMarked := mateMarked
  have _representativeOlder := representativeOlder
  exact observeCausalTarget target

#print axioms CanonicalTagHistory.RawMarkedBefore
#print axioms CanonicalTagHistory.RawMarkedBefore.first_rawMarked
#print axioms CanonicalTagHistory.RawMarkedBefore.second_rawMarked
#print axioms CanonicalTagHistory.RawMarkedBefore.vertex_ne
#print axioms CanonicalTagHistory.rawMarkedPremisesBefore
#print axioms MarkedConclusionChainFirstCausalDescent
#print axioms MarkedConclusionChainFirstRepresentativeDescent.causalDescent
#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCausalDescentTarget
#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationFirstDescentTarget.causalDescentTarget
#print axioms
  WaitStep.commitmentInterval_parTraceReentryMarkedContinuationCausalDescentOutcome

end Consumer
end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 raw-return causal-descent consumer: kernel-green"
