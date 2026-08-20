/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtParentEscapeTemporal

/-!
# Active-top debt parent-escape temporal consumer

This consumer reconstructs every public temporal carrier, applies the
failure-conditioned normalizer, and audits the complete public surface.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

private theorem Consumer.anchorRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (component : UnificationComponent) (owned : List Vertex)
    (premise : Vertex) (markedAge : RawTokenAge)
    (anchor :
      ActiveRawMarkReservationAnchor tagHistory component owned premise
        markedAge) :
    ActiveRawMarkReservationAnchor tagHistory component owned premise
      markedAge := by
  rcases anchor with
    ⟨event, eventUsed, leftPath, rightPath, eventLookup, eventRawAge,
      derivation, eventLink, premiseOwned, leftOwned, rightOwned,
      leftStarts, leftFinishes, leftWithin, rightStarts, rightFinishes,
      rightWithin⟩
  exact ⟨event, eventUsed, leftPath, rightPath, eventLookup, eventRawAge,
    derivation, eventLink, premiseOwned, leftOwned, rightOwned, leftStarts,
    leftFinishes, leftWithin, rightStarts, rightFinishes, rightWithin⟩

private theorem Consumer.parContinuationRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {activeRawAge : RawTokenAge} {selected : Vertex} {owned : List Vertex}
    {premise : Vertex} {linkIndex : Nat} {conclusion : Vertex}
    (continuation :
      ActiveParParentContinuation certificate state activeRawAge selected owned
        premise linkIndex conclusion) :
    ActiveParParentContinuation certificate state activeRawAge selected owned
      premise linkIndex conclusion := by
  cases continuation with
  | rawSibling consumer sameIndex sameConclusion mateUnmarked mateLocation =>
      exact .rawSibling consumer sameIndex sameConclusion mateUnmarked
        mateLocation
  | olderFuture boundary work older =>
      exact .olderFuture boundary work older
  | olderMarked conclusionAge marked olderRepresentative =>
      exact .olderMarked conclusionAge marked olderRepresentative

private theorem Consumer.parResidualRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex)
    (residual :
      ActiveParCarrierTemporalResidual tagHistory input component owned) :
    ActiveParCarrierTemporalResidual tagHistory input component owned := by
  rcases residual with
    ⟨premise, markedAge, linkIndex, storedLeft, storedRight, conclusion,
      premiseNeSelected, premiseFrontier, premiseOwned, premiseMarked,
      authentic, representativeEq, premiseNotGlobal, linkLookup,
      premiseMembership, conclusionNotOwned, anchor, continuation⟩
  exact ⟨premise, markedAge, linkIndex, storedLeft, storedRight, conclusion,
    premiseNeSelected, premiseFrontier, premiseOwned, premiseMarked,
    authentic, representativeEq, premiseNotGlobal, linkLookup,
    premiseMembership, conclusionNotOwned,
    Consumer.anchorRoundTrip tagHistory component owned premise markedAge
      anchor,
    Consumer.parContinuationRoundTrip continuation⟩

private theorem Consumer.tensorResidualRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex)
    (residual :
      tagHistory.ActiveCarrierTensorSameBoundaryResidual input component
        owned) :
    tagHistory.ActiveCarrierTensorSameBoundaryResidual input component
      owned := by
  rcases residual with
    ⟨premise, markedAge, linkIndex, storedLeft, storedRight, conclusion,
      sibling, event, eventUsed, forestUsed, leftPath, rightPath,
      premiseNeSelected, premiseFrontier, premiseMarked, authentic,
      premiseNotGlobal, linkLookup, premiseMembership, conclusionNotOwned,
      premiseOwned, representativeEq, boundaryEq, siblingOrientation,
      siblingNotOwned, eventLookup, eventRawAge, eventDerivation,
      eventLinkUsed, eventWitness, eventAccounted, eventLeftOwned,
      eventRightOwned, leftStarts, leftFinishes, leftWithin, rightStarts,
      rightFinishes, rightWithin⟩
  exact ⟨premise, markedAge, linkIndex, storedLeft, storedRight, conclusion,
    sibling, event, eventUsed, forestUsed, leftPath, rightPath,
    premiseNeSelected, premiseFrontier, premiseMarked, authentic,
    premiseNotGlobal, linkLookup, premiseMembership, conclusionNotOwned,
    premiseOwned, representativeEq, boundaryEq, siblingOrientation,
    siblingNotOwned, eventLookup, eventRawAge, eventDerivation,
    eventLinkUsed, eventWitness, eventAccounted, eventLeftOwned,
    eventRightOwned, leftStarts, leftFinishes, leftWithin, rightStarts,
    rightFinishes, rightWithin⟩

private theorem Consumer.temporalResidualRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex)
    (residual :
      ActiveCarrierParentTemporalResidual tagHistory input component owned) :
    ActiveCarrierParentTemporalResidual tagHistory input component owned := by
  cases residual with
  | par parResidual =>
      exact .par
        (Consumer.parResidualRoundTrip tagHistory input component owned
          parResidual)
  | tensor tensorResidual olderMarkedTensor =>
      exact .tensor
        (Consumer.tensorResidualRoundTrip tagHistory input component owned
          tensorResidual)
        olderMarkedTensor

private theorem Consumer.normalizeNoTail
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core input.rawAge
        component owned)
    (escape :
      ActiveCarrierParentEscape certificate state component owned input.vertex)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierParentTemporalResidual tagHistory input component owned := by
  exact Consumer.temporalResidualRoundTrip tagHistory input component owned
    (escape.temporalResidual_of_no_readyTail tagHistory correct input invariant
      componentLookup occurrence accounted noTail)

#print axioms ActiveRawMarkReservationAnchor
#print axioms ActiveParParentContinuation
#print axioms ActiveParCarrierTemporalResidual
#print axioms CanonicalTagHistory.ActiveCarrierTensorSameBoundaryResidual
#print axioms ActiveCarrierParentTemporalResidual
#print axioms ActiveCarrierParentEscape.temporalResidual_of_no_readyTail

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "active-top debt parent-escape temporal consumer: kernel-green"
