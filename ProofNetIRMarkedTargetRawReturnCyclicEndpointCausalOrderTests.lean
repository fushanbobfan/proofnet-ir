/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnCyclicEndpointCausalOrder

/-!
# Figure-7 cyclic-junction endpoint causal-order consumer

This runnable consumer exercises the simultaneous endpoint-junction theorem,
the cyclic source causal classification, the target adapter, and the typed
Wait wrapper. It imports only the production owner module.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

private theorem Consumer.endpointJunctions
    {certificate : Certificate} {state : ReservationState}
    {base source : Vertex}
    {retainedPrefix continuationTail :
      List certificate.fullGraph.DirectedEdge}
    (complete :
      MarkedConclusionRawReturnCompleteCancellationTraversal state
        retainedPrefix continuationTail)
    (prefixWalk : certificate.fullGraph.EdgeWalk base retainedPrefix source)
    (tailWalk : certificate.fullGraph.EdgeWalk source continuationTail base)
    (prefixNonempty : retainedPrefix ≠ []) :
    MarkedConclusionRawReturnCompleteCancellationEndpointJunctions
      base source retainedPrefix continuationTail := by
  have endpoints := complete.endpointJunctions prefixWalk tailWalk
    prefixNonempty
  rcases endpoints with
    ⟨prefixLast, tailHead, prefixHead, tailLast, prefixLastLookup,
      tailHeadLookup, tailHeadEq, prefixLastBackward, tailHeadForward,
      prefixHeadLookup, tailLastLookup, prefixHeadEq, prefixHeadBackward,
      tailLastForward, prefixLastTarget, tailHeadSource, prefixHeadSource,
      tailLastTarget⟩
  exact ⟨prefixLast, tailHead, prefixHead, tailLast, prefixLastLookup,
    tailHeadLookup, tailHeadEq, prefixLastBackward, tailHeadForward,
    prefixHeadLookup, tailLastLookup, prefixHeadEq, prefixHeadBackward,
    tailLastForward, prefixLastTarget, tailHeadSource, prefixHeadSource,
    tailLastTarget⟩

private theorem Consumer.causalOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin outer : Vertex} {active outerAge : RawTokenAge}
    (correct : certificate.DeclarativelyCorrect)
    (descent : MarkedConclusionChainFirstCausalDescent certificate state
      tagHistory origin outer active)
    (outerEvent : tagHistory.RawMarked outerAge outer)
    (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (pathStart : path.start = outer)
    (directed : certificate.referenceSwitchingGraph.DirectedEdge)
    (directedMembership : directed ∈ path.traversed)
    (targetConsumer : ConnectiveBelow certificate origin)
    (sourceConsumer : directed.source = targetConsumer.conclusion)
    (different : origin ≠ outer) :
    MarkedConclusionRawReturnCyclicJunctionCausalOutcome certificate state
      tagHistory outer targetConsumer.conclusion outerAge := by
  rcases descent.rawReturnCyclicJunctionCausalOutcome correct outerEvent path
      pathStart directed directedMembership targetConsumer sourceConsumer
      different with ⟨cyclic, causal⟩
  rcases causal with same | ⟨sourceAge, before⟩
  · exact ⟨cyclic, Or.inl same⟩
  · exact ⟨cyclic, Or.inr ⟨sourceAge, before⟩⟩

private theorem Consumer.target
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (correct : certificate.DeclarativelyCorrect)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalJunctionTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalEndpointTarget
      tagHistory input component owned current := by
  exact target.causalEndpointTarget correct

private theorem Consumer.wait
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
          pending ∉ certificate.conclusions) :
    tagHistory.CommitmentIntervalParTraceOutcome
      step.prepared.readyHeadInput step.consumer position edgeCount first
        (step.consumer.mate ∉ owned ∧
          before.core.marks[step.consumer.mate]? =
            some (some step.mateRawAge) ∧
          before.core.representative step.mateRawAge <
            step.prepared.stackResult.rawAge ∧
          ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalEndpointTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  exact step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalEndpointOutcome
    correct connected tagHistory invariant componentLookup occurrence positive
    firstAt lastAt noTail

#print axioms MarkedConclusionRawReturnCompleteCancellationTraversal.endpointJunctions
#print axioms MarkedConclusionChainFirstCausalDescent.rawReturnCyclicJunctionCausalOutcome

namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalJunctionTarget
#print axioms causalEndpointTarget
end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalJunctionTarget

namespace WaitStep
#print axioms
  commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalEndpointOutcome
end WaitStep

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 cyclic-junction endpoint causal order: kernel-green"
