/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnCyclicEndpointCausalOrder

/-!
# Figure-7 complete-cancellation causal endpoints

A nonempty complete-cancellation prefix is a retained, internally reduced
exact-occurrence walk with duplicate-free edge indices. If its source equaled
its base, these facts would yield a nonempty cyclically nonbacktracking closed
walk in the correct reference switching, contradicting the tree contract.

Consequently the cyclic source is strictly before the authenticated outer
endpoint in the nonempty complete-cancellation branch. Both exact reverse
endpoint junctions remain available on the same witnesses.

This checkpoint eliminates only the source-equals-base subcase inside nonempty
complete cancellation. It does not eliminate complete cancellation, either
junction, the surviving par-pair residual, any sibling exit, either marked-
global order, the descent, or any other endpoint. It derives no ready-tail
witness, history-tail law, completion, or progress theorem.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

private theorem cyclicNoImmediateReverse_of_indexNodup
    {graph : Graph} {traversed : List graph.DirectedEdge}
    (indexNodup : (traversed.map Graph.DirectedEdge.index).Nodup)
    (reduced : Graph.EdgeWalk.NoImmediateReverse traversed) :
    Graph.EdgeWalk.CyclicNoImmediateReverse traversed := by
  refine ⟨reduced, ?_⟩
  intro first last firstHead lastLast reversed
  have firstMembership : first ∈ traversed := List.mem_of_head? firstHead
  have lastMembership : last ∈ traversed := List.mem_of_getLast? lastLast
  have sameIndex : first.index = last.index := by
    rw [reversed]
    simp [Graph.DirectedEdge.reverse]
  have sameDirected := Graph.eq_of_map_eq_of_mem_of_nodup indexNodup
    firstMembership lastMembership sameIndex
  subst last
  exact first.ne_reverse reversed

/-- A nonempty retained-prefix complete cancellation cannot have the same
source and base in a correct reference switching. -/
theorem
    MarkedConclusionRawReturnCompleteCancellationTraversal.source_ne_base
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
  intro same
  have closedWalk :
      certificate.fullGraph.EdgeWalk base retainedPrefix base := by
    simpa [same] using prefixWalk
  have cyclicReduced :
      Graph.EdgeWalk.CyclicNoImmediateReverse retainedPrefix :=
    cyclicNoImmediateReverse_of_indexNodup complete.1.1 prefixReduced
  have aligned :
      certificate.fullGraph.edges.length =
        certificate.referenceSwitchingMask.length := by
    change (Certificate.linkFullEdges certificate.links).length =
      certificate.referenceSwitchingMask.length
    exact certificate.referenceFullSwitchingSelection.mask_length.symm
  rcases Graph.EdgeWalk.retainEdgesCyclicNoImmediateReverse closedWalk aligned
      prefixNonempty allKept cyclicReduced with
    ⟨retainedTraversal, retainedNonempty, retainedWalk, retainedReduced⟩
  have referenceWalk :
      certificate.referenceSwitchingGraph.EdgeWalk base retainedTraversal base :=
    by simpa [Certificate.referenceSwitchingGraph] using retainedWalk
  exact correct.referenceSwitchingTree.no_cyclicNoImmediateReverse
    retainedNonempty referenceWalk retainedReduced

/-- In a nonempty complete-cancellation branch, the cyclic source is strictly
before the authenticated base and both exact endpoint junctions are present. -/
theorem MarkedConclusionRawReturnCyclicJunctionCausalOutcome.completeEndpoints
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
  have endpoints := complete.endpointJunctions prefixWalk tailWalk
    prefixNonempty
  have different := complete.source_ne_base correct prefixWalk allKept
    prefixReduced prefixNonempty
  rcases outcome.2 with same | ⟨sourceAge, before⟩
  · exact False.elim (different same)
  · exact ⟨endpoints, sourceAge, before⟩

end SequentialFigure7
end ProofNetIR
