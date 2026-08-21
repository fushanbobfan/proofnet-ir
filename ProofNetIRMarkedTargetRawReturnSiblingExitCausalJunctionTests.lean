/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnSiblingExitCausalJunction

/-!
# Figure-7 sibling-exit causal/cyclic-junction consumer

Consumes the generic junction reduction, the strengthened sibling target,
its adapter, and the typed Wait theorem without importing unrelated stronger
modules.
-/

namespace ProofNetIR.SequentialFigure7.Consumer

open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerBridge

private inductive OutcomeObservation : Prop where
  | raw
  | future
  | globalBefore
  | globalAfter

private theorem observeCausalOutcome
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

private theorem observeJunction
    {certificate : Certificate} {state : ReservationState}
    {base source : Vertex}
    (outcome : MarkedConclusionRawReturnCyclicJunctionOutcome certificate state
      base source) : True := by
  rcases outcome with
    ⟨retainedPrefix, continuationTail, normalizedBase, reduced, prefixWalk,
      tailWalk, closedWalk, allKept, allForward, tailTargetNodup,
      prefixReduced, tailReduced, reducedWalk, normalization, shape⟩
  have _ := retainedPrefix
  have _ := continuationTail
  have _ := normalizedBase
  have _ := reduced
  have _ := prefixWalk
  have _ := tailWalk
  have _ := closedWalk
  have _ := allKept
  have _ := allForward
  have _ := tailTargetNodup
  have _ := prefixReduced
  have _ := tailReduced
  have _ := reducedWalk
  have _ := normalization
  rcases shape with cancellation | survivingPair
  · rcases cancellation with ⟨reducedEmpty, emptyOrCancellation⟩
    have _ := reducedEmpty
    rcases emptyOrCancellation with empty | complete
    · have _ := empty.1
      have _ := empty.2
      trivial
    · have _ := complete.1
      have _ := complete.2.1
      have _ := complete.2.2.1
      have _ := complete.2.2.2
      trivial
  · rcases survivingPair with
      ⟨before, left, right, conclusion, after, leftOccurrence,
        rightOccurrence, linksEq, leftMem, leftIndex, leftEdge, leftKept,
        rightMem, rightIndex, rightEdge, rightOmitted, leftPrefix,
        rightTail, rightForward, rightRawAge, rightMarked,
        rightNotGlobal⟩
    have _ := before
    have _ := left
    have _ := right
    have _ := conclusion
    have _ := after
    have _ := leftOccurrence
    have _ := rightOccurrence
    have _ := linksEq
    have _ := leftMem
    have _ := leftIndex
    have _ := leftEdge
    have _ := leftKept
    have _ := rightMem
    have _ := rightIndex
    have _ := rightEdge
    have _ := rightOmitted
    have _ := leftPrefix
    have _ := rightTail
    have _ := rightForward
    have _ := rightRawAge
    have _ := rightMarked
    have _ := rightNotGlobal
    trivial

private theorem consumeGeneric
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin outer : Vertex} {active : RawTokenAge}
    (correct : certificate.DeclarativelyCorrect)
    (descent : MarkedConclusionChainFirstCausalDescent certificate state
      tagHistory origin outer active)
    (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (pathStart : path.start = outer)
    (directed : certificate.referenceSwitchingGraph.DirectedEdge)
    (directedMembership : directed ∈ path.traversed)
    (targetConsumer : ConnectiveBelow certificate origin)
    (sourceConsumer : directed.source = targetConsumer.conclusion)
    (different : origin ≠ outer) : True := by
  exact observeJunction
    (descent.rawReturnCyclicJunctionOutcome correct path pathStart directed
      directedMembership targetConsumer sourceConsumer different)

private theorem observeTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalJunctionTarget
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
  · rcases raw with
      ⟨terminal, chain, terminalConsumer, mateUnmarked, mateOutside⟩
    have _ := terminal
    have _ := chain
    have _ := terminalConsumer.link_eq
    have _ := mateUnmarked
    have _ := mateOutside
    trivial
  · rcases descent with
      ⟨firstDescent, consumer, mateAge, mateBeforeOuter, causalOutcome,
        junctionOutcome⟩
    have _ := firstDescent
    have _ := consumer.link_eq
    have _ := mateAge
    have _ := mateBeforeOuter.first_rawMarked
    have _ := observeCausalOutcome causalOutcome
    exact observeJunction junctionOutcome
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

private theorem consumeAdapter
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (correct : certificate.DeclarativelyCorrect)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalTarget
        tagHistory input component owned current) : True := by
  exact observeTarget (target.causalJunctionTarget correct)

private theorem consumeWait
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (correct : certificate.DeclarativelyCorrect)
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
    step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalJunctionOutcome
      correct connected tagHistory invariant componentLookup occurrence
      positive firstAt lastAt noTail
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
      exact observeTarget target

#print axioms
  MarkedConclusionChainFirstCausalDescent.rawReturnCyclicJunctionOutcome
#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalJunctionTarget

end ProofNetIR.SequentialFigure7.Consumer

namespace ProofNetIR.SequentialFigure7
namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalTarget
#print axioms causalJunctionTarget
end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalTarget
end ProofNetIR.SequentialFigure7

namespace ProofNetIR.SequentialFigure7.Consumer
#print axioms
  WaitStep.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalJunctionOutcome

end ProofNetIR.SequentialFigure7.Consumer

def main : IO Unit :=
  IO.println "Figure-7 sibling-exit causal/cyclic-junction consumer: kernel-green"
