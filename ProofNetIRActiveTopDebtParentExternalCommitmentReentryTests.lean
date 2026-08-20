/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtParentExternalCommitmentReentry

/-!
# Active-top debt external parent commitment re-entry consumer

This runnable consumer composes a positive commitment interval, destructs the
exact re-entry path and all four normalized outcome cases, and audits the five
production declarations directly.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

namespace Consumer

private theorem intervalRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    {position edgeCount : Nat} {first last : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : state.stack.sigma[position]? = some first)
    (lastAt : state.stack.sigma[position + edgeCount]? = some last) :
    tagHistory.CommitmentIntervalReferencePath first last := by
  rcases tagHistory.commitmentInterval_referencePath invariant positive
      firstAt lastAt with
    ⟨firstEvent, lastEvent, path, firstEventAt, lastEventAt,
      starts, finishes⟩
  exact ⟨firstEvent, lastEvent, path, firstEventAt, lastEventAt,
    starts, finishes⟩

private theorem observeReentry
    {certificate : Certificate} {owned : List Vertex} {endpoint : Vertex}
    (reentry : ActiveCarrierExternalEndpointReentry certificate owned endpoint) :
    Nonempty certificate.referenceSwitchingGraph.EdgeSimplePath := by
  rcases reentry with
    ⟨path, directed, starts, finishOwned, traversed, sourceOutside,
      targetOwned⟩
  have _ := directed
  have _ := starts
  have _ := finishOwned
  have _ := traversed
  have _ := sourceOutside
  have _ := targetOwned
  exact ⟨path⟩

private theorem reentryOutcomeRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {activeRawAge : RawTokenAge} {owned : List Vertex}
    (outcome : ActiveCarrierParentExternalCommitmentOutcome tagHistory
      activeRawAge owned)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks : List Nat}
    (componentLookup :
      state.core.components[activeRawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned) :
    ActiveCarrierParentExternalCommitmentReentryOutcome tagHistory
      activeRawAge owned := by
  have normalized := outcome.reentryOutcome invariant componentLookup occurrence
  cases normalized with
  | rawOutside sibling unmarked outside =>
      exact .rawOutside sibling unmarked outside
  | olderReady conclusion boundary position bucket sigmaAt readyAt member
      older split outside reentry =>
      have _ := observeReentry reentry
      exact .olderReady conclusion boundary position bucket sigmaAt readyAt
        member older split outside reentry
  | olderWaiting conclusion boundary payload waitingAt member older split
      outside =>
      exact .olderWaiting conclusion boundary payload waitingAt member older
        split outside
  | olderMarked conclusion age marked older split outside reentry =>
      have _ := observeReentry reentry
      exact .olderMarked conclusion age marked older split outside reentry

end Consumer

end SequentialFigure7
end ProofNetIR

#print axioms
  ProofNetIR.SequentialFigure7.CanonicalTagHistory.CommitmentIntervalReferencePath
#print axioms
  ProofNetIR.SequentialFigure7.CanonicalTagHistory.commitmentInterval_referencePath
#print axioms ProofNetIR.SequentialFigure7.ActiveCarrierExternalEndpointReentry
#print axioms
  ProofNetIR.SequentialFigure7.ActiveCarrierParentExternalCommitmentReentryOutcome
#print axioms
  ProofNetIR.SequentialFigure7.ActiveCarrierParentExternalCommitmentOutcome.reentryOutcome

def main : IO Unit :=
  IO.println "active-top debt external commitment re-entry: kernel-green"
