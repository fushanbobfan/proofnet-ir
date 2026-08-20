/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtParentExternalEndpointCrossing

/-!
# Active-top debt external parent endpoint-crossing consumer

This runnable consumer applies the endpoint-crossing reduction, destructs
every public carrier field, and audits the three production declarations.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

namespace Consumer

private theorem observeCrossing
    {certificate : Certificate} {owned : List Vertex} {endpoint : Vertex}
    (crossing : ActiveCarrierExternalEndpointCrossing certificate owned endpoint) :
    Nonempty certificate.referenceSwitchingGraph.EdgeSimplePath := by
  rcases crossing with
    ⟨path, directed, startsOwned, finishes, traversed, sourceOwned,
      targetOutside⟩
  have _ := startsOwned
  have _ := finishes
  have _ := traversed
  have _ := sourceOwned
  have _ := targetOutside
  exact ⟨path⟩

private theorem endpointCrossingRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {activeRawAge : RawTokenAge} {owned : List Vertex}
    (outcome : ActiveCarrierParentExternalCommitmentOutcome tagHistory
      activeRawAge owned)
    (connected : certificate.ReferenceSwitchingConnected)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks : List Nat}
    (componentLookup :
      state.core.components[activeRawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned) :
    ActiveCarrierParentExternalCommitmentCrossingOutcome tagHistory
      activeRawAge owned := by
  have normalized := outcome.endpointCrossing connected invariant
    componentLookup occurrence
  cases normalized with
  | rawOutside sibling unmarked outside =>
      exact .rawOutside sibling unmarked outside
  | olderFuture conclusion boundary work older split outside crossing =>
      have _ := observeCrossing crossing
      exact .olderFuture conclusion boundary work older split outside crossing
  | olderMarked conclusion age marked older split outside crossing =>
      have _ := observeCrossing crossing
      exact .olderMarked conclusion age marked older split outside crossing

end Consumer

end SequentialFigure7
end ProofNetIR

#print axioms ProofNetIR.SequentialFigure7.ActiveCarrierExternalEndpointCrossing
#print axioms
  ProofNetIR.SequentialFigure7.ActiveCarrierParentExternalCommitmentCrossingOutcome
#print axioms
  ProofNetIR.SequentialFigure7.ActiveCarrierParentExternalCommitmentOutcome.endpointCrossing

def main : IO Unit :=
  IO.println "active-top debt external endpoint crossing: kernel-green"
