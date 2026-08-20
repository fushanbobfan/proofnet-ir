/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtParentExternalReentryTarget

/-!
# Active-top debt external re-entry target consumer

This runnable consumer calls the occurrence-carrier geometry, destructs and
reconstructs the exact inbound parent edge, observes every target-status and
historical-mark case, consumes the conclusion-avoiding reduction, and audits
the production declarations directly.
-/

namespace ProofNetIR

namespace Certificate
namespace OccurrenceDerivation
namespace Consumer

private theorem premisesOwned
    {certificate : Certificate} (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness : OccurrenceDerivation certificate tree frontier usedLinks owned)
    {linkIndex left right conclusion : Nat}
    (conclusionOwned : conclusion ∈ owned)
    (submitted :
      certificate.links[linkIndex]? = some (.tensor left right conclusion) ∨
        certificate.links[linkIndex]? = some (.par left right conclusion)) :
    left ∈ owned ∧ right ∈ owned :=
  connectivePremises_owned_of_conclusion_owned structural witness
    conclusionOwned submitted

private theorem conclusionOwned
    {certificate : Certificate} (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness : OccurrenceDerivation certificate tree frontier usedLinks owned)
    {linkIndex left right conclusion premise : Nat}
    (submitted :
      certificate.links[linkIndex]? = some (.tensor left right conclusion) ∨
        certificate.links[linkIndex]? = some (.par left right conclusion))
    (premiseMembership : premise ∈ [left, right])
    (premiseOwned : premise ∈ owned)
    (premiseNotFrontier : premise ∉ frontier) :
    conclusion ∈ owned :=
  connectiveConclusion_owned_of_premise_owned_not_frontier structural witness
    submitted premiseMembership premiseOwned premiseNotFrontier

end Consumer
end OccurrenceDerivation
end Certificate

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

namespace Consumer

private theorem premiseNotConclusion
    {certificate : Certificate} (structural : certificate.StructurallyWellFormed)
    {linkIndex : Nat} {link : Link} {premise : Vertex}
    (lookup : certificate.links[linkIndex]? = some link)
    (premiseMembership : premise ∈ link.premises) :
    premise ∉ certificate.conclusions :=
  submittedPremise_not_conclusion structural lookup premiseMembership

private theorem inboundParentEdgeRoundTrip
    {certificate : Certificate} {component : UnificationComponent}
    {owned : List Vertex}
    {directed : certificate.referenceSwitchingGraph.DirectedEdge}
    (edge :
      ActiveCarrierInboundParentEdge certificate component owned directed) :
    ActiveCarrierInboundParentEdge certificate component owned directed := by
  rcases edge with
    ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
      targetFrontier, targetNotGlobal, linkLookup, targetPremise,
      conclusionOutside⟩
  exact ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
    targetFrontier, targetNotGlobal, linkLookup, targetPremise,
    conclusionOutside⟩

private theorem targetStatusRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {endpoint : Vertex}
    (status :
      ActiveCarrierExternalReentryTargetStatus certificate state input
        component owned endpoint) :
    ActiveCarrierExternalReentryTargetStatus certificate state input component
      owned endpoint := by
  rcases status with
    ⟨path, directed, pathStarts, finishOwned, directedMembership,
      parentEdge, selected | tail | marked⟩
  · exact ⟨path, directed, pathStarts, finishOwned, directedMembership,
      inboundParentEdgeRoundTrip parentEdge, Or.inl selected⟩
  · exact ⟨path, directed, pathStarts, finishOwned, directedMembership,
      inboundParentEdgeRoundTrip parentEdge, Or.inr (Or.inl tail)⟩
  · exact ⟨path, directed, pathStarts, finishOwned, directedMembership,
      inboundParentEdgeRoundTrip parentEdge, Or.inr (Or.inr marked)⟩

private theorem targetFailureStatusRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {endpoint : Vertex}
    (status :
      ActiveCarrierExternalReentryFailureTargetStatus certificate state input
        component owned endpoint) :
    ActiveCarrierExternalReentryFailureTargetStatus certificate state input
      component owned endpoint := by
  rcases status with
    ⟨path, directed, pathStarts, finishOwned, directedMembership,
      parentEdge, selected | marked⟩
  · exact ⟨path, directed, pathStarts, finishOwned, directedMembership,
      inboundParentEdgeRoundTrip parentEdge, Or.inl selected⟩
  · exact ⟨path, directed, pathStarts, finishOwned, directedMembership,
      inboundParentEdgeRoundTrip parentEdge, Or.inr marked⟩

private theorem classifyTarget
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned)
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core input.rawAge component owned)
    {endpoint : Vertex}
    (reentry :
      ActiveCarrierExternalEndpointReentry certificate owned endpoint) :
    ActiveCarrierExternalReentryTargetStatus certificate state input component
      owned endpoint :=
  targetStatusRoundTrip
    (reentry.targetStatus input invariant componentLookup occurrence accounted)

private theorem classifyFailureTarget
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned)
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core input.rawAge component owned)
    {endpoint : Vertex}
    (reentry :
      ActiveCarrierExternalEndpointReentry certificate owned endpoint)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryFailureTargetStatus certificate state input
      component owned endpoint :=
  targetFailureStatusRoundTrip
    (reentry.targetFailureStatus input invariant componentLookup occurrence
      accounted noTail)

private theorem avoidingRoundTrip
    {certificate : Certificate} {owned : List Vertex}
    {endpoint forbidden : Vertex}
    (reentry :
      ActiveCarrierExternalEndpointReentryAvoiding certificate owned endpoint
        forbidden) :
    ActiveCarrierExternalEndpointReentryAvoiding certificate owned endpoint
      forbidden := by
  rcases reentry with
    ⟨path, directed, pathStarts, finishOwned, directedMembership,
      sourceOutside, targetOwned, forbiddenAvoided⟩
  exact ⟨path, directed, pathStarts, finishOwned, directedMembership,
    sourceOutside, targetOwned, forbiddenAvoided⟩

private theorem historicalStatusRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {endpoint : Vertex}
    (status :
      ActiveCarrierExternalReentryFailureHistoricalStatus tagHistory input
        component owned endpoint) :
    ActiveCarrierExternalReentryFailureHistoricalStatus tagHistory input
      component owned endpoint := by
  rcases status with
    ⟨path, directed, pathStarts, finishOwned, directedMembership,
      parentEdge, selected | marked⟩
  · exact ⟨path, directed, pathStarts, finishOwned, directedMembership,
      inboundParentEdgeRoundTrip parentEdge, Or.inl selected⟩
  · rcases marked with
      ⟨markedAge, targetNeSelected, targetMarked, authentic, representative⟩
    exact ⟨path, directed, pathStarts, finishOwned, directedMembership,
      inboundParentEdgeRoundTrip parentEdge,
      Or.inr ⟨markedAge, targetNeSelected, targetMarked, authentic,
        representative⟩⟩

private theorem markedHistoricalTargetRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {endpoint : Vertex}
    (status :
      ActiveCarrierExternalReentryMarkedHistoricalTarget tagHistory input
        component owned endpoint) :
    ActiveCarrierExternalReentryMarkedHistoricalTarget tagHistory input
      component owned endpoint := by
  rcases status with
    ⟨path, directed, markedAge, pathStarts, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetMarked, authentic, representative⟩
  exact ⟨path, directed, markedAge, pathStarts, finishOwned,
    directedMembership, inboundParentEdgeRoundTrip parentEdge, targetNeSelected,
    targetMarked, authentic, representative⟩

private theorem classifyHistoricalFailureTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned)
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core input.rawAge component owned)
    {endpoint : Vertex}
    (reentry : ActiveCarrierExternalEndpointReentry certificate owned endpoint)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryFailureHistoricalStatus tagHistory input
      component owned endpoint :=
  historicalStatusRoundTrip
    (reentry.targetFailureHistoricalStatus tagHistory input invariant
      componentLookup occurrence accounted noTail)

private theorem classifyAvoidingFailureTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    (consumer : ConnectiveBelow certificate input.vertex)
    (parEq : consumer.kind = .par)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned)
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core input.rawAge component owned)
    {endpoint : Vertex}
    (reentry :
      ActiveCarrierExternalEndpointReentryAvoiding certificate owned endpoint
        consumer.conclusion)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryMarkedHistoricalTarget tagHistory input
      component owned endpoint :=
  markedHistoricalTargetRoundTrip
    (reentry.markedHistoricalTarget tagHistory input invariant consumer parEq
      componentLookup occurrence accounted noTail)

end Consumer

end SequentialFigure7
end ProofNetIR

namespace ProofNetIR.Certificate.OccurrenceDerivation

#print axioms connectivePremises_owned_of_conclusion_owned
#print axioms connectiveConclusion_owned_of_premise_owned_not_frontier

end ProofNetIR.Certificate.OccurrenceDerivation

#print axioms ProofNetIR.SequentialFigure7.submittedPremise_not_conclusion
#print axioms ProofNetIR.SequentialFigure7.ActiveCarrierInboundParentEdge
#print axioms ProofNetIR.SequentialFigure7.ActiveCarrierExternalReentryTargetStatus
#print axioms
  ProofNetIR.SequentialFigure7.ActiveCarrierExternalReentryFailureTargetStatus
#print axioms
  ProofNetIR.SequentialFigure7.ActiveCarrierExternalEndpointReentry.targetStatus
#print axioms
  ProofNetIR.SequentialFigure7.ActiveCarrierExternalEndpointReentry.targetFailureStatus
#print axioms
  ProofNetIR.SequentialFigure7.ActiveCarrierExternalEndpointReentryAvoiding
#print axioms
  ProofNetIR.SequentialFigure7.ActiveCarrierExternalReentryFailureHistoricalStatus
#print axioms
  ProofNetIR.SequentialFigure7.ActiveCarrierExternalReentryMarkedHistoricalTarget
#print axioms
  ProofNetIR.SequentialFigure7.ActiveCarrierExternalEndpointReentry.targetFailureHistoricalStatus
#print axioms
  ProofNetIR.SequentialFigure7.ActiveCarrierExternalEndpointReentryAvoiding.markedHistoricalTarget

def main : IO Unit :=
  IO.println "active-top debt external re-entry target: kernel-green"
