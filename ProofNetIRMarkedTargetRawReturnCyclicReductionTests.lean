/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnCyclicReduction

/-!
# Figure-7 marked-target raw-return cyclic-reduction consumer

This compile-time consumer exercises the generic raw-return reduction and its
integration with the marked target continuation exit. It also destructs both
cyclic outcomes, including the exact splice-junction cancellation and the
marked/nonconclusion source of a retained/omitted par pair.
-/

namespace ProofNetIR
namespace SequentialFigure7
namespace Consumer

open SequentialSchedulerState
open SequentialSchedulerBridge

private theorem observeCyclicOutcome
    {certificate : Certificate} {base source : Vertex}
    (outcome :
      MarkedConclusionRawReturnCyclicOutcome certificate base source) : True := by
  rcases outcome with
    ⟨retainedPrefix, continuationTail, normalizedBase, reduced,
      prefixWalk, tailWalk, closedWalk, allKept, allForward,
      tailTargetsNodup, reducedWalk, normalization, status⟩
  have _prefixEndpoint := prefixWalk.toChain
  have _tailEndpoint := tailWalk.toChain
  have _closedEndpoint := closedWalk.toChain
  have _reducedEndpoint := reducedWalk.toChain
  have _normalizationSubset := normalization.membership_subset
  rcases status with cancelled | paired
  · rcases cancelled with ⟨reducedEmpty, spliceStatus⟩
    rw [reducedEmpty] at reducedWalk
    rcases spliceStatus with bothEmpty | cancellationSite
    · rcases bothEmpty with ⟨prefixEmpty, tailEmpty⟩
      rw [prefixEmpty] at allKept
      rw [tailEmpty] at allForward tailTargetsNodup
      exact True.intro
    · have _site := cancellationSite
      exact True.intro
  · rcases paired with
      ⟨before, left, right, conclusion, after,
        leftOccurrence, rightOccurrence, linksEq,
        leftReduced, leftIndex, leftEdge, leftKept,
        rightReduced, rightIndex, rightEdge, rightOmitted,
        leftPrefix, rightTail, rightForward⟩
    have _leftPrefixKept := allKept leftOccurrence leftPrefix
    have _rightTailForward := allForward rightOccurrence rightTail
    have _rightForwardExact := rightForward
    have _leftReducedAgain := leftReduced
    have _rightReducedAgain := rightReduced
    have _leftIndexExact := leftIndex
    have _rightIndexExact := rightIndex
    have _leftEdgeExact := leftEdge
    have _rightEdgeExact := rightEdge
    have _leftKeptExact := leftKept
    have _rightOmittedExact := rightOmitted
    have _linksExact := linksEq
    exact True.intro

private theorem observeCyclicJunctionOutcome
    {certificate : Certificate} {state : ReservationState}
    {base source : Vertex}
    (outcome :
      MarkedConclusionRawReturnCyclicJunctionOutcome certificate state
        base source) : True := by
  rcases outcome with
    ⟨retainedPrefix, continuationTail, normalizedBase, reduced,
      prefixWalk, tailWalk, closedWalk, allKept, allForward,
      tailTargetsNodup, prefixReduced, tailReduced,
      reducedWalk, normalization, status⟩
  have _prefixEndpoint := prefixWalk.toChain
  have _tailEndpoint := tailWalk.toChain
  have _closedEndpoint := closedWalk.toChain
  have _reducedEndpoint := reducedWalk.toChain
  have _normalizationSubset := normalization.membership_subset
  have _prefixReduced := prefixReduced
  have _tailReduced := tailReduced
  rcases status with cancelled | paired
  · rcases cancelled with ⟨reducedEmpty, spliceStatus⟩
    rw [reducedEmpty] at reducedWalk
    rcases spliceStatus with bothEmpty | junction
    · rcases bothEmpty with ⟨prefixEmpty, tailEmpty⟩
      rw [prefixEmpty] at allKept
      rw [tailEmpty] at allForward tailTargetsNodup
      exact True.intro
    · rcases junction with ⟨prefixNonempty, tailNonempty, reverse⟩
      have _prefixNonempty := prefixNonempty
      have _tailNonempty := tailNonempty
      have _junctionReverse := reverse
      exact True.intro
  · rcases paired with
      ⟨before, left, right, conclusion, after,
        leftOccurrence, rightOccurrence, linksEq,
        leftReduced, leftIndex, leftEdge, leftKept,
        rightReduced, rightIndex, rightEdge, rightOmitted,
        leftPrefix, rightTail, rightForward,
        rightRawAge, rightMarked, rightNotConclusion⟩
    have _leftPrefixKept := allKept leftOccurrence leftPrefix
    have _rightTailForward := allForward rightOccurrence rightTail
    have _rightForwardExact := rightForward
    have _rightMarkedExact := rightMarked
    have _rightNotConclusionExact := rightNotConclusion
    have _rightRawAge := rightRawAge
    have _leftReducedAgain := leftReduced
    have _rightReducedAgain := rightReduced
    have _leftIndexExact := leftIndex
    have _rightIndexExact := rightIndex
    have _leftEdgeExact := leftEdge
    have _rightEdgeExact := rightEdge
    have _leftKeptExact := leftKept
    have _rightOmittedExact := rightOmitted
    have _linksExact := linksEq
    exact True.intro

example
    {certificate : Certificate} {state : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    {base origin : Vertex}
    (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (pathStart : path.start = base)
    (directed : certificate.referenceSwitchingGraph.DirectedEdge)
    (directedMembership : directed ∈ path.traversed)
    (targetConsumer : ConnectiveBelow certificate origin)
    (sourceConsumer : directed.source = targetConsumer.conclusion)
    (originNeBase : origin ≠ base)
    (chain : MarkedConclusionChain certificate state origin base) : True := by
  exact observeCyclicOutcome
    (chain.rawReturnCyclicReduction correct path pathStart directed
      directedMembership targetConsumer sourceConsumer originNeBase)

example
    {certificate : Certificate} {state : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    {base origin : Vertex}
    (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (pathStart : path.start = base)
    (directed : certificate.referenceSwitchingGraph.DirectedEdge)
    (directedMembership : directed ∈ path.traversed)
    (targetConsumer : ConnectiveBelow certificate origin)
    (sourceConsumer : directed.source = targetConsumer.conclusion)
    (originNeBase : origin ≠ base)
    (chain : MarkedConclusionChain certificate state origin base) : True := by
  exact observeCyclicJunctionOutcome
    (chain.rawReturnCyclicJunctionReduction correct path pathStart directed
      directedMembership targetConsumer sourceConsumer originNeBase)

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (correct : certificate.DeclarativelyCorrect)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCyclicReductionTarget
      tagHistory input component owned current :=
  target.continuationCyclicReductionTarget correct

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (correct : certificate.DeclarativelyCorrect)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCyclicReductionTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCyclicJunctionTarget
      tagHistory input component owned current :=
  target.cyclicJunctionTarget correct

#print axioms MarkedConclusionRawReturnCyclicOutcome
#print axioms MarkedConclusionChain.rawReturnCyclicReduction
#print axioms MarkedConclusionRawReturnCyclicJunctionOutcome
#print axioms MarkedConclusionChain.rawReturnCyclicJunctionReduction
#print axioms ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCyclicReductionTarget
#print axioms ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCyclicJunctionTarget

end Consumer

namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget
#print axioms continuationCyclicReductionTarget
end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget

namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCyclicReductionTarget
#print axioms cyclicJunctionTarget
end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCyclicReductionTarget

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 marked-target raw-return cyclic reduction: kernel-green"
