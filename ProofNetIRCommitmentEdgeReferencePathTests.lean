import ProofNetIR.SequentialFigure7CommitmentEdgeReferencePath

namespace ProofNetIR

/-!
# Figure-7 commitment-edge reference-path consumer

This consumer invokes and destructures the two-item public surface.  It checks
one adjacent retained sigma edge and consumes the parent anchor, committed
path, child anchor, canonical left-to-left path, and exact final owned
accounting.  It consumes no target-avoidance, raw-seam, or progress theorem.
-/

open SequentialFigure7
open SequentialSchedulerBridge
open SequentialSchedulerState

#check CanonicalTagHistory.CommitmentEdgeReferencePath
#check CanonicalTagHistory.commitmentEdge_referencePath

/- Consume the exact adjacent-edge path package and its final ownership
accounting. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    {position parent child : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt : state.stack.sigma[position + 1]? = some child) :
    ∃ (before after : ReservationState)
        (step : NewStep certificate before after)
        (parentEvent : ReservationEvent certificate)
        (parentComponent childComponent : UnificationComponent)
        (parentOwned childOwned : List Nat)
        (parentAnchor committedPath childAnchor canonicalPath :
          certificate.referenceSwitchingGraph.EdgeSimplePath),
      tagHistory.reservationLedger[parent]? = some parentEvent ∧
        tagHistory.reservationLedger[child]? =
          some (ReservationEvent.new step) ∧
        parent = step.stackResult.rawAge ∧
        child = (ReservationEvent.new step).rawAge ∧
        state.core.marks[step.stackResult.vertex]? = some (some parent) ∧
        state.core.components[state.core.representative parent]? =
          some (some parentComponent) ∧
        Certificate.OwnedOccurrenceAccounted state.core
          (state.core.representative parent) parentComponent parentOwned ∧
        step.stackResult.vertex ∈ parentOwned ∧
        parentEvent.search.result.left ∈ parentOwned ∧
        state.core.components[state.core.representative child]? =
          some (some childComponent) ∧
        Certificate.OwnedOccurrenceAccounted state.core
          (state.core.representative child) childComponent childOwned ∧
        step.reached ∈ childOwned ∧
        parentAnchor.start = step.stackResult.vertex ∧
        parentAnchor.finish = parentEvent.search.result.left ∧
        (∀ vertex ∈ parentAnchor.vertices, vertex ∈ parentOwned) ∧
        committedPath.start = step.stackResult.vertex ∧
        committedPath.finish = step.reached ∧
        childAnchor.start = step.reached ∧
        childAnchor.finish =
          (ReservationEvent.new step).search.result.left ∧
        (∀ vertex ∈ childAnchor.vertices, vertex ∈ childOwned) ∧
        canonicalPath.start = parentEvent.search.result.left ∧
        canonicalPath.finish =
          (ReservationEvent.new step).search.result.left ∧
        (step.reached = step.search.left ∨
          step.reached = step.search.right) := by
  rcases tagHistory.commitmentEdge_referencePath invariant parentAt childAt with
    ⟨before, after, step, parentEvent, parentComponent, childComponent,
      _parentEventUsed, _parentForestUsed, parentOwned, _childEventUsed,
      _childForestUsed, childOwned, parentAnchor, committedPath, childAnchor,
      canonicalPath, parentLookup, childLookup, _parentRawAge, parentEq,
      childEq, selectedMarked, parentComponentLookup, _parentDerivation,
      _parentLink, _parentWitness, parentAccounted, selectedOwned,
      parentLeftOwned, childComponentLookup, _childDerivation, _childLink,
      _childWitness, childAccounted, reachedOwned, parentAnchorStarts,
      parentAnchorFinishes, parentAnchorWithin, committedStarts,
      committedFinishes, childAnchorStarts, childAnchorFinishes,
      childAnchorWithin, canonicalStarts, canonicalFinishes, reachedEndpoint⟩
  exact ⟨before, after, step, parentEvent, parentComponent, childComponent,
    parentOwned, childOwned, parentAnchor, committedPath, childAnchor,
    canonicalPath, parentLookup, childLookup, parentEq, childEq,
    selectedMarked, parentComponentLookup, parentAccounted, selectedOwned,
    parentLeftOwned, childComponentLookup, childAccounted, reachedOwned,
    parentAnchorStarts, parentAnchorFinishes, parentAnchorWithin,
    committedStarts, committedFinishes, childAnchorStarts,
    childAnchorFinishes, childAnchorWithin, canonicalStarts,
    canonicalFinishes, reachedEndpoint⟩

end ProofNetIR

/-- Run the standalone commitment-edge reference-path API smoke consumer. -/
def main : IO Unit :=
  IO.println "Figure-7 commitment-edge reference-path API consumer passed."
