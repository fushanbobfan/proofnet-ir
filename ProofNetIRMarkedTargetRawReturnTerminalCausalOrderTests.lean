/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnTerminalCausalOrder

/-!
# Figure-7 marked-target raw-return terminal-causal-order consumer

This compile-time consumer exercises strict-order transitivity and asymmetry,
finite-chain terminal chronology, both first-descent terminal projections, the
terminal-event target adapter, and the integrated Wait theorem. It does not
assume that the causal descent or any retained continuation exit is impossible.
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

private theorem observeTerminalCausalTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationTerminalCausalTarget
        tagHistory input component owned current) : True := by
  rcases target with ⟨terminalAge, terminalEvent, causalTarget⟩
  have _terminalAge := terminalAge
  have _terminalEvent := terminalEvent
  exact observeCausalTarget causalTarget

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {firstAge middleAge lastAge : RawTokenAge}
    {first middle last : Vertex}
    (firstBefore : tagHistory.RawMarkedBefore
      firstAge first middleAge middle)
    (secondBefore : tagHistory.RawMarkedBefore
      middleAge middle lastAge last) : True :=
  observeBefore (firstBefore.trans secondBefore)

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {firstAge secondAge : RawTokenAge} {first second : Vertex}
    (before : tagHistory.RawMarkedBefore
      firstAge first secondAge second) : True := by
  have _asymmetric := before.asymmetric
  trivial

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {origin terminal : Vertex} {terminalAge : RawTokenAge}
    (chain : MarkedConclusionChain certificate state origin terminal)
    (terminalEvent : tagHistory.RawMarked terminalAge terminal) : True := by
  rcases chain.rawMarkedBefore_or_eq tagHistory terminalEvent with
    same | ⟨originAge, before⟩
  · have _same := same
    trivial
  · have _originAge := originAge
    exact observeBefore before

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin terminal : Vertex} {active terminalAge : RawTokenAge}
    (descent : MarkedConclusionChainFirstCausalDescent certificate state
      tagHistory origin terminal active)
    (terminalEvent : tagHistory.RawMarked terminalAge terminal) : True := by
  rcases descent.originBeforeTerminal terminalEvent with
    ⟨_originAge, before⟩
  exact observeBefore before

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin terminal : Vertex} {active terminalAge : RawTokenAge}
    (descent : MarkedConclusionChainFirstCausalDescent certificate state
      tagHistory origin terminal active)
    (terminalEvent : tagHistory.RawMarked terminalAge terminal) : True := by
  rcases descent.mateBeforeTerminal terminalEvent with
    ⟨consumer, _mateAge, before⟩
  have _consumer := consumer
  exact observeBefore before

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCausalDescentTarget
        tagHistory input component owned current)
    {terminalAge : RawTokenAge}
    (terminalEvent : tagHistory.RawMarked terminalAge current.mate) : True :=
  observeTerminalCausalTarget (target.terminalCausalTarget terminalEvent)

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
    (step.commitmentInterval_parTraceReentryMarkedContinuationTerminalCausalOutcome
      connected tagHistory invariant componentLookup occurrence positive firstAt
      lastAt noTail)
  rintro ⟨mateOutside, mateMarked, representativeOlder, target⟩
  have _mateOutside := mateOutside
  have _mateMarked := mateMarked
  have _representativeOlder := representativeOlder
  exact observeTerminalCausalTarget target

#print axioms CanonicalTagHistory.RawMarkedBefore.trans
#print axioms CanonicalTagHistory.RawMarkedBefore.asymmetric
#print axioms MarkedConclusionChain.rawMarkedBefore_or_eq
#print axioms MarkedConclusionChainFirstCausalDescent.originBeforeTerminal
#print axioms MarkedConclusionChainFirstCausalDescent.mateBeforeTerminal
#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationTerminalCausalTarget
open ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCausalDescentTarget
#print axioms terminalCausalTarget
#print axioms
  WaitStep.commitmentInterval_parTraceReentryMarkedContinuationTerminalCausalOutcome

end Consumer
end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 raw-return terminal-causal-order consumer: kernel-green"
