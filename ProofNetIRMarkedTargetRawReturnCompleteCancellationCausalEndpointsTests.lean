/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnCompleteCancellationCausalEndpoints

/-!
# Figure-7 complete-cancellation causal-endpoint consumer

This runnable consumer exercises the nonempty complete-cancellation source
separation theorem and the combined exact-endpoint and causal-order theorem.
It imports only the production owner module.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

private theorem Consumer.sourceNeBase
    {certificate : Certificate} {state : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    {base source : Vertex}
    {retainedPrefix continuationTail :
      List certificate.fullGraph.DirectedEdge}
    (complete :
      MarkedConclusionRawReturnCompleteCancellationTraversal state
        retainedPrefix continuationTail)
    (prefixWalk : certificate.fullGraph.EdgeWalk base retainedPrefix source)
    (allKept : ∀ directed ∈ retainedPrefix,
      certificate.referenceSwitchingMask[directed.index]? = some true)
    (prefixReduced : Graph.EdgeWalk.NoImmediateReverse retainedPrefix)
    (prefixNonempty : retainedPrefix ≠ []) :
    source ≠ base := by
  exact complete.source_ne_base correct prefixWalk allKept prefixReduced
    prefixNonempty

private theorem Consumer.completeEndpoints
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (correct : certificate.DeclarativelyCorrect)
    {base source : Vertex} {baseAge : RawTokenAge}
    (outcome :
      MarkedConclusionRawReturnCyclicJunctionCausalOutcome certificate state
        tagHistory base source baseAge)
    {retainedPrefix continuationTail :
      List certificate.fullGraph.DirectedEdge}
    (prefixWalk : certificate.fullGraph.EdgeWalk base retainedPrefix source)
    (tailWalk : certificate.fullGraph.EdgeWalk source continuationTail base)
    (allKept : ∀ directed ∈ retainedPrefix,
      certificate.referenceSwitchingMask[directed.index]? = some true)
    (prefixReduced : Graph.EdgeWalk.NoImmediateReverse retainedPrefix)
    (complete :
      MarkedConclusionRawReturnCompleteCancellationTraversal state
        retainedPrefix continuationTail)
    (prefixNonempty : retainedPrefix ≠ []) :
    MarkedConclusionRawReturnCompleteCancellationEndpointJunctions
        base source retainedPrefix continuationTail ∧
      ∃ sourceAge,
        tagHistory.RawMarkedBefore sourceAge source baseAge base := by
  rcases outcome.completeEndpoints correct prefixWalk tailWalk allKept
      prefixReduced complete prefixNonempty with
    ⟨endpoints, sourceAge, before⟩
  rcases endpoints with
    ⟨prefixLast, tailHead, prefixHead, tailLast, prefixLastLookup,
      tailHeadLookup, tailHeadEq, prefixLastBackward, tailHeadForward,
      prefixHeadLookup, tailLastLookup, prefixHeadEq, prefixHeadBackward,
      tailLastForward, prefixLastTarget, tailHeadSource, prefixHeadSource,
      tailLastTarget⟩
  exact
    ⟨⟨prefixLast, tailHead, prefixHead, tailLast, prefixLastLookup,
        tailHeadLookup, tailHeadEq, prefixLastBackward, tailHeadForward,
        prefixHeadLookup, tailLastLookup, prefixHeadEq, prefixHeadBackward,
        tailLastForward, prefixLastTarget, tailHeadSource, prefixHeadSource,
        tailLastTarget⟩,
      sourceAge, before⟩

#print axioms
  MarkedConclusionRawReturnCompleteCancellationTraversal.source_ne_base
#print axioms
  MarkedConclusionRawReturnCyclicJunctionCausalOutcome.completeEndpoints

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 complete-cancellation causal endpoints: kernel-green"
