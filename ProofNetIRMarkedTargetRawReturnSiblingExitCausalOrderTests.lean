/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnSiblingExitCausalOrder

/-!
# Figure-7 sibling-exit causal-order consumer

Consumes the strict comparison, endpoint classifier, descent receipt, target
adapter, and typed Wait theorem without importing unrelated stronger modules.
-/

namespace ProofNetIR.SequentialFigure7.Consumer

open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerBridge

private theorem consumeTotal
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {firstAge secondAge : RawTokenAge} {first second : Vertex}
    (firstEvent : tagHistory.RawMarked firstAge first)
    (secondEvent : tagHistory.RawMarked secondAge second)
    (different : first ≠ second) :
    tagHistory.RawMarked firstAge first ∧
      tagHistory.RawMarked secondAge second := by
  rcases CanonicalTagHistory.RawMarkedBefore.total_of_vertex_ne firstEvent
      secondEvent different with before | after
  · exact ⟨before.first_rawMarked, before.second_rawMarked⟩
  · exact ⟨after.second_rawMarked, after.first_rawMarked⟩

private theorem consumeComparison
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {firstAge secondAge : RawTokenAge} {first second : Vertex}
    (firstEvent : tagHistory.RawMarked firstAge first)
    (secondEvent : tagHistory.RawMarked secondAge second) :
    tagHistory.RawMarked firstAge first ∧
      tagHistory.RawMarked secondAge second := by
  rcases CanonicalTagHistory.RawMarkedBefore.eq_or_before_or_after firstEvent
      secondEvent with same | before | after
  · exact ⟨firstEvent, secondEvent⟩
  · exact ⟨before.first_rawMarked, before.second_rawMarked⟩
  · exact ⟨after.second_rawMarked, after.first_rawMarked⟩

private inductive OutcomeObservation : Prop where
  | raw
  | future
  | globalBefore
  | globalAfter

private theorem observeOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin outer : Vertex} {outerAge : RawTokenAge}
    (outcome : ContinuationExitOuterTerminalCausalOutcome tagHistory origin
      outer outerAge) : OutcomeObservation := by
  cases outcome with
  | rawMate chain consumer mateUnmarked =>
      have _ := chain
      have _ := consumer.link_eq
      have _ := mateUnmarked
      exact .raw
  | futureConclusion chain consumer boundary work =>
      have _ := chain
      have _ := consumer.link_eq
      have _ := boundary
      have _ := work
      exact .future
  | markedGlobalBefore chain consumer conclusionAge marked global before =>
      have _ := chain
      have _ := consumer.link_eq
      have _ := conclusionAge
      have _ := marked
      have _ := global
      have _ := before.first_rawMarked
      exact .globalBefore
  | markedGlobalAfter chain consumer conclusionAge marked global before =>
      have _ := chain
      have _ := consumer.link_eq
      have _ := conclusionAge
      have _ := marked
      have _ := global
      have _ := before.second_rawMarked
      exact .globalAfter

private theorem consumeExit
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin outer : Vertex} {outerAge : RawTokenAge}
    (exit : ContinuationExit certificate state origin)
    (outerEvent : tagHistory.RawMarked outerAge outer)
    (outerNotGlobal : outer ∉ certificate.conclusions) :
    OutcomeObservation := by
  exact observeOutcome
    (exit.outerTerminalCausalOutcome outerEvent outerNotGlobal)

private theorem consumeDescent
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin outer : Vertex} {active outerAge : RawTokenAge}
    (descent : MarkedConclusionChainFirstCausalDescent certificate state
      tagHistory origin outer active)
    (outerEvent : tagHistory.RawMarked outerAge outer)
    (outerNotGlobal : outer ∉ certificate.conclusions) :
    OutcomeObservation := by
  rcases descent.siblingExitOuterTerminalCausalOutcome outerEvent
      outerNotGlobal with ⟨consumer, mateAge, before, outcome⟩
  have _ := consumer.link_eq
  have _ := mateAge
  have _ := before.first_rawMarked
  exact observeOutcome outcome

private theorem observeTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalTarget
        tagHistory input component owned current) : True := by
  rcases target with
    ⟨outerAge, outerEvent, path, directed, markedAge, pathStart, finishOwned,
      directedMembership, parentEdge, targetNeSelected, targetNeMate,
      targetMarked, targetEvent, representativeEq, targetConsumer,
      targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside,
      status⟩
  have _ := outerAge
  have _ := outerEvent
  have _ := pathStart
  have _ := finishOwned
  have _ := directedMembership
  have _ := parentEdge
  have _ := targetNeSelected
  have _ := targetNeMate
  have _ := targetMarked
  have _ := targetEvent
  have _ := representativeEq
  have _ := targetConsumer.link_eq
  have _ := targetConsumerMateNeSelected
  have _ := sourceConsumer
  have _ := targetConclusionOutside
  rcases status with raw | descent | future | marked
  · rcases raw with ⟨terminal, chain, terminalConsumer, mateUnmarked,
        mateOutside⟩
    have _ := terminal
    have _ := chain
    have _ := terminalConsumer.link_eq
    have _ := mateUnmarked
    have _ := mateOutside
    trivial
  · rcases descent with ⟨descent, consumer, mateAge, before, outcome⟩
    have _ := descent
    have _ := consumer.link_eq
    have _ := mateAge
    have _ := before.second_rawMarked
    have _ := observeOutcome outcome
    trivial
  · rcases future with
      ⟨terminal, chain, terminalConsumer, boundary, work, outside, older⟩
    have _ := terminal
    have _ := chain
    have _ := terminalConsumer.link_eq
    have _ := boundary
    have _ := work
    have _ := outside
    have _ := older
    trivial
  · rcases marked with
      ⟨terminal, chain, terminalConsumer, conclusionAge, conclusionMarked,
        global, outside, older⟩
    have _ := terminal
    have _ := chain
    have _ := terminalConsumer.link_eq
    have _ := conclusionAge
    have _ := conclusionMarked
    have _ := global
    have _ := outside
    have _ := older
    trivial

private theorem consumeTargetAdapter
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (structural : certificate.StructurallyWellFormed)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationTerminalCausalTarget
        tagHistory input component owned current) : True := by
  exact observeTarget (target.siblingExitCausalTarget structural)

private theorem consumeWait
    {certificate : Certificate} {before after : ReservationState}
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
  have outcome :=
    step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalOutcome
      connected tagHistory invariant componentLookup occurrence positive firstAt
      lastAt noTail
  cases outcome with
  | avoiding path =>
      have _ := path
      trivial
  | equalSelected offset parent child event offsetLt parentAt childAt
      notAvoiding membership eventAge childEq side beforeTrace afterTrace trace =>
      have _ := trace
      trivial
  | equalMate offset parent child event offsetLt parentAt childAt notAvoiding
      membership eventAge childEq side beforeTrace afterTrace trace =>
      have _ := trace
      trivial
  | olderMate offset parent child event offsetLt parentAt childAt notAvoiding
      membership eventAge childLt side beforeTrace afterTrace trace status =>
      rcases status with ⟨mateOutside, mateMarked, representativeOlder, target⟩
      have _ := mateOutside
      have _ := mateMarked
      have _ := representativeOlder
      have _ := observeTarget target
      trivial

#print axioms CanonicalTagHistory.RawMarkedBefore.total_of_vertex_ne
#print axioms CanonicalTagHistory.RawMarkedBefore.eq_or_before_or_after
#print axioms ContinuationExitOuterTerminalCausalOutcome
#print axioms ContinuationExit.outerTerminalCausalOutcome
#print axioms MarkedConclusionChainFirstCausalDescent.siblingExitOuterTerminalCausalOutcome
#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalTarget
end ProofNetIR.SequentialFigure7.Consumer

namespace ProofNetIR.SequentialFigure7
namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationTerminalCausalTarget
#print axioms siblingExitCausalTarget
end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationTerminalCausalTarget
end ProofNetIR.SequentialFigure7

namespace ProofNetIR.SequentialFigure7.Consumer
#print axioms WaitStep.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalOutcome

end ProofNetIR.SequentialFigure7.Consumer

def main : IO Unit :=
  IO.println "Figure-7 sibling-exit causal-order consumer: kernel-green"
