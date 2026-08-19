/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderMarkedTensorPredecessorWaitPreservation
import ProofNetIR.SequentialFigure7CrossRepresentativeForwardPreservation
import ProofNetIR.SequentialComponentSourceLeftGeometry
import ProofNetIR.SequentialFigure7OlderMarkedTensorPredecessorInvariant

/-!
# Forward preservation of the older marked-tensor predecessor invariant

A successful forward keeps marks, representatives, and sigma fixed after its
prepared prefix. Retained work therefore transports directly. The only new
case is the submitted par conclusion at the active boundary. Its boundary
event reaches that conclusion inside the queue-par output component, while
component separation makes every strictly older event leave it untouched.
The Wait-preservation module's conditional child-anchor bridge then identifies
the marked outer tensor mate with the immediate sigma predecessor.

Only `CanonicalTagHistory.forward_olderMarkedTensorPredecessorInvariant` is
public in this module. The proof uses neither a future-candidate
mate-unmarked premise nor a global raw seam. It proves no rule applicability,
dispatcher progress or totality, fallback removal, sequentialization, or
complexity bound.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialUnification
open SequentialSchedulerBridge
open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState

/-- Exact created-conclusion obligation in the prepared middle state. -/
private def ForwardCreatedOlderMarkedTensorPredecessor
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) : Prop :=
  ∀ (outer : ConnectiveBelow certificate step.consumer.conclusion),
    outer.kind = .tensor →
      ∀ {mateRawAge},
        step.prepared.after.core.marks[outer.mate]? =
            some (some mateRawAge) →
          step.prepared.after.core.representative mateRawAge <
              step.prepared.after.core.representative
                step.prepared.stackResult.rawAge →
            ∃ previousBoundary,
              Nonempty
                (SigmaImmediatePredecessorAt
                  step.prepared.after.stack.sigma
                  step.prepared.stackResult.rawAge mateRawAge
                  previousBoundary)

private theorem ForwardStep.createdConclusion_futureWorkAt
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) :
    FutureWorkAt after step.prepared.stackResult.rawAge
      step.consumer.conclusion := by
  have afterStack : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState ↦ state.stack) step.output_eq
  have middleInvariant :
      ReservationInvariant certificate step.prepared.after :=
    step.prepared.reservationInvariant step.before_invariant
  rcases SequentialStackState.popReadyMark?_exact step.prepared.stack_eq with
    ⟨_top, sigmaTop, _unmarked, _marks, _nextAge, sigmaEquation,
      _ready, _waiting, _marked⟩
  have middleSigmaTop :
      step.prepared.after.stack.sigma.getLast? =
        some step.prepared.stackResult.rawAge := by
    change step.prepared.stackResult.after.sigma.getLast? = _
    rw [sigmaEquation]
    exact sigmaTop
  rcases List.getLast?_eq_some_iff.mp middleSigmaTop with
    ⟨sigmaPrefix, sigmaDecomposition⟩
  have prefixLengths :
      step.prependStep.readyPrefix.length = sigmaPrefix.length := by
    have aligned := middleInvariant.stack_wellShaped.ready_aligned
    change
      step.prepared.stackResult.after.ready.length =
        step.prepared.stackResult.after.sigma.length at aligned
    rw [step.prependStep.ready_eq] at aligned
    change
      step.prepared.stackResult.after.sigma =
        sigmaPrefix ++ [step.prepared.stackResult.rawAge]
          at sigmaDecomposition
    rw [sigmaDecomposition] at aligned
    simp at aligned
    omega
  have afterSigma :
      after.stack.sigma = step.prepared.after.stack.sigma := by
    have prependSigma :
        step.stackAfter.sigma = step.prepared.after.stack.sigma := by
      simpa [PreparedStep.after] using
        congrArg SequentialStackState.sigma step.prependStep.after_eq
    calc
      after.stack.sigma = step.stackAfter.sigma :=
        congrArg SequentialStackState.sigma afterStack
      _ = step.prepared.after.stack.sigma := prependSigma
  have afterReady :
      after.stack.ready =
        step.prependStep.readyPrefix ++
          [step.consumer.conclusion :: step.prependStep.activeReady] := by
    calc
      after.stack.ready = step.stackAfter.ready :=
        congrArg SequentialStackState.ready afterStack
      _ = _ :=
        congrArg SequentialStackState.ready step.prependStep.after_eq
  apply FutureWorkAt.ready
    (position := step.prependStep.readyPrefix.length)
    (bucket := step.consumer.conclusion :: step.prependStep.activeReady)
  · rw [afterSigma, sigmaDecomposition, prefixLengths]
    simp
  · rw [afterReady]
    simp
  · simp

private theorem mem_liveFrontierVertices_of_forwardAnchor
    {state : UnificationState} {token : Nat}
    {component : UnificationComponent} {vertex : Vertex}
    (componentLookup : state.components[token]? = some (some component))
    (vertexMembership : vertex ∈ component.frontier) :
    vertex ∈ state.liveFrontierVertices := by
  unfold UnificationState.liveFrontierVertices
  apply List.mem_flatMap.mpr
  refine ⟨some component, ?_, ?_⟩
  · exact List.mem_of_getElem? (by simpa using componentLookup)
  · simpa using vertexMembership

private theorem tensorConclusion_not_produced_of_forwardWork
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (work : FutureWorkAt state candidateRawAge candidateVertex)
    (outer : TensorBelow)
    (outerValid :
      outer.Valid certificate certificate.consumerIndex candidateVertex) :
    ¬ Produced state outer.conclusion := by
  intro produced
  have tensorMembership :
      Link.tensor outer.storedLeft outer.storedRight outer.conclusion ∈
        certificate.links :=
    List.mem_of_getElem? outerValid.2.1
  have premises :=
    invariant.produced_premises_marked tensorMembership produced
  have candidateUnmarked :
      state.core.marks[candidateVertex]? = some none :=
    invariant.queued_vertices_unmarked candidateVertex work.mem_queued
  have premise := outerValid.2.2.2
  cases sideEquation : outer.side with
  | storedLeft =>
      rcases premises.1 with ⟨rawAge, marked⟩
      have candidateEq : candidateVertex = outer.storedLeft := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using premise
      rw [← candidateEq, candidateUnmarked] at marked
      simp at marked
  | storedRight =>
      rcases premises.2 with ⟨rawAge, marked⟩
      have candidateEq : candidateVertex = outer.storedRight := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using premise
      rw [← candidateEq, candidateUnmarked] at marked
      simp at marked

private theorem tensorConclusion_not_owned_of_forwardWork
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (work : FutureWorkAt state candidateRawAge candidateVertex)
    (outer : TensorBelow)
    (outerValid :
      outer.Valid certificate certificate.consumerIndex candidateVertex)
    {index : Nat} {component : UnificationComponent} {owned : List Vertex}
    (componentLookup :
      state.core.components[index]? = some (some component))
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core index component owned) :
    outer.conclusion ∉ owned := by
  intro conclusionOwned
  apply tensorConclusion_not_produced_of_forwardWork invariant work outer
    outerValid
  rcases accounted outer.conclusion conclusionOwned with
    ⟨rawAge, marked, _representative⟩ | ⟨_unmarked, frontier⟩
  · exact Or.inl ⟨rawAge, marked⟩
  · exact Or.inr
      (mem_liveFrontierVertices_of_forwardAnchor componentLookup frontier)

private def ForwardCreatedConclusionTensorChildAnchor
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate after}
    (step : ForwardStep certificate before after)
    (tagHistory : CanonicalTagHistory certificate history)
    (outer : TensorBelow) : Prop :=
  ∀ childEvent : ReservationEvent certificate,
    tagHistory.reservationLedger[step.prepared.stackResult.rawAge]? =
        some childEvent →
      ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
        path.start = childEvent.search.result.left ∧
          path.finish = step.consumer.conclusion ∧
            outer.conclusion ∉ path.vertices

private theorem ForwardStep.createdConclusionTensorChildAnchor
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate after}
    (step : ForwardStep certificate before after)
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (beforeInvariant : SchedulerInvariant certificate before)
    (afterInvariant : SchedulerInvariant certificate after)
    (outer : TensorBelow)
    (outerValid :
      outer.Valid certificate certificate.consumerIndex
        step.consumer.conclusion) :
    ForwardCreatedConclusionTensorChildAnchor step tagHistory outer := by
  intro childEvent childLookup
  have work : FutureWorkAt after step.prepared.stackResult.rawAge
      step.consumer.conclusion :=
    step.createdConclusion_futureWorkAt
  have boundaryBound :
      step.prepared.stackResult.rawAge < after.stack.nextAge :=
    work.rawAge_lt_nextAge afterInvariant
  have childRawAge :
      childEvent.rawAge = step.prepared.stackResult.rawAge := by
    have mapped := tagHistory.reservationLedger_getElem?_rawAge
      step.prepared.stackResult.rawAge boundaryBound
    simpa [childLookup] using mapped
  have childMembership : childEvent ∈ tagHistory.reservationLedger :=
    List.mem_of_getElem? childLookup
  rcases tagHistory.reservationLedger_axiomEndpoints_accounted
      correct.1 childMembership with
    ⟨childComponent, _childUsed, _childForest, childOwned,
      childComponentLookup, childDerivation, _childLink, childWitness,
      childAccounted, childLeftOwned, _childRightOwned⟩
  have activeRootAfter :
      after.core.representative step.prepared.stackResult.rawAge =
        step.prepared.stackResult.rawAge :=
    work.representative_eq_rawAge afterInvariant
  have childComponentLookupAtActive :
      after.core.components[step.prepared.stackResult.rawAge]? =
        some (some childComponent) := by
    simpa [childRawAge, activeRootAfter] using childComponentLookup
  have middleInvariant :
      SchedulerInvariant certificate step.prepared.after :=
    step.prepared.schedulerInvariant beforeInvariant
  have tokenGuards :=
    UnificationState.forwardToken?_success step.queueStep.token_guard
  have outputRoot :
      step.prepared.coreMarked.representative step.queueStep.outputToken =
        step.queueStep.outputToken :=
    middleInvariant.core_abstractable.tokenAt?_root tokenGuards.2.1
  have activeMiddleLookup :
      step.prepared.coreMarked.components[step.queueStep.outputToken]? =
        some (some step.queueStep.component) := by
    have rawLookup :=
      UnificationState.componentAt?_some_raw step.queueStep.component_lookup
    simpa [outputRoot] using rawLookup
  have outputBound :
      step.queueStep.outputToken <
        step.prepared.coreMarked.components.size :=
    (Array.getElem?_eq_some_iff.mp activeMiddleLookup).1
  let nextComponent : UnificationComponent := {
    tree := .par step.queueStep.leftFocus step.queueStep.rightFocus
      step.queueStep.component.tree
    frontier := step.queueStep.context ++ [step.consumer.conclusion] }
  have afterCore : after.core = step.coreAfter :=
    congrArg (fun state : ReservationState ↦ state.core) step.output_eq
  have afterComponents :
      after.core.components =
        step.prepared.coreMarked.components.setIfInBounds
          step.queueStep.outputToken (some nextComponent) := by
    calc
      after.core.components = step.coreAfter.components :=
        congrArg UnificationState.components afterCore
      _ = _ := by
        simpa [nextComponent] using
          congrArg UnificationState.components step.queueStep.after_eq
  have outputLookup :
      after.core.components[step.prepared.stackResult.rawAge]? =
        some (some nextComponent) := by
    rw [afterComponents, ← step.output_token_eq_active]
    simp [outputBound]
  have childComponentEq : childComponent = nextComponent :=
    Option.some.inj
      (Option.some.inj
        (childComponentLookupAtActive.symm.trans outputLookup))
  subst childComponent
  rcases middleInvariant.component_forest_provenance with
    ⟨usedAt, ownedAt, live, _separated, _markedOwned⟩
  have activeFacts := live activeMiddleLookup
  have outputDerivation :
      certificate.OccurrenceDerivation
        (.par step.queueStep.leftFocus step.queueStep.rightFocus
          step.queueStep.component.tree)
        (step.queueStep.context ++ [step.consumer.conclusion])
        (step.consumer.linkIndex :: usedAt step.queueStep.outputToken)
        (step.consumer.conclusion :: ownedAt step.queueStep.outputToken) :=
    Certificate.OccurrenceDerivation.ofQueueParStep step.queueStep
      activeFacts.1.derivation step.consumer.linkIndex step.submitted_par
  have childOwnedEq :
      childOwned =
        step.consumer.conclusion :: ownedAt step.queueStep.outputToken := by
    exact Certificate.OccurrenceDerivation.owned_unique correct.1
      childDerivation (by simpa [nextComponent] using outputDerivation)
  have conclusionChildOwned : step.consumer.conclusion ∈ childOwned := by
    rw [childOwnedEq]
    simp
  rcases childWitness.referencePath_within_owned childLeftOwned
      conclusionChildOwned with
    ⟨path, pathStarts, pathFinishes, pathWithin⟩
  have outerNotChildOwned : outer.conclusion ∉ childOwned :=
    tensorConclusion_not_owned_of_forwardWork afterInvariant work outer
      outerValid childComponentLookupAtActive (by
        simpa [childRawAge, activeRootAfter] using childAccounted)
  have pathAvoids : outer.conclusion ∉ path.vertices := by
    intro membership
    exact outerNotChildOwned (pathWithin outer.conclusion membership)
  exact ⟨path, pathStarts, pathFinishes, pathAvoids⟩

private theorem ForwardStep.createdConclusionTouchSeparated
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : ForwardStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed) :
    ∀ event : ReservationEvent certificate,
      event ∈ prior.reservationLedger →
        step.prepared.after.core.representative event.rawAge <
            step.prepared.after.core.representative
              step.prepared.stackResult.rawAge →
          ¬ event.Touched step.consumer.conclusion := by
  have invariant : SchedulerInvariant certificate before :=
    history.schedulerInvariant structural
  intro event eventMembership older touched
  rcases prior.reservationLedger_axiomEndpoints_accounted
      structural eventMembership with
    ⟨eventComponent, eventUsed, eventForestUsed, eventOwned,
      eventLookup, eventDerivation, eventLink, eventWitness,
      eventAccounted, eventLeftOwned, eventRightOwned⟩
  rcases invariant.component_forest_provenance with
    ⟨usedAt, ownedAt, live, separated, markedOwned⟩
  have eventFacts := live eventLookup
  have eventOwnedEq :
      eventOwned = ownedAt (before.core.representative event.rawAge) :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      eventDerivation eventFacts.1.derivation
  have eventLeftForestOwned :
      event.search.result.left ∈
        ownedAt (before.core.representative event.rawAge) := by
    rw [← eventOwnedEq]
    exact eventLeftOwned
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have tokenGuards :=
    UnificationState.forwardToken?_success step.queueStep.token_guard
  have activeRoot :
      step.prepared.coreMarked.representative step.queueStep.outputToken =
        step.queueStep.outputToken :=
    middleInvariant.core_abstractable.tokenAt?_root tokenGuards.2.1
  have activeMiddleLookup :
      step.prepared.coreMarked.components[step.queueStep.outputToken]? =
        some (some step.queueStep.component) := by
    have rawLookup :=
      UnificationState.componentAt?_some_raw step.queueStep.component_lookup
    simpa [activeRoot] using rawLookup
  have componentsEq :
      step.prepared.coreMarked.components = before.core.components :=
    (UnificationState.markReadyRaw?_exact
      step.prepared.core_mark_eq).2.2.2.1
  have activeBeforeLookup :
      before.core.components[step.queueStep.outputToken]? =
        some (some step.queueStep.component) := by
    rw [← componentsEq]
    exact activeMiddleLookup
  have activeFacts := live activeBeforeLookup
  have outputDerivation :
      certificate.OccurrenceDerivation
        (.par step.queueStep.leftFocus step.queueStep.rightFocus
          step.queueStep.component.tree)
        (step.queueStep.context ++ [step.consumer.conclusion])
        (step.consumer.linkIndex :: usedAt step.queueStep.outputToken)
        (step.consumer.conclusion :: ownedAt step.queueStep.outputToken) :=
    Certificate.OccurrenceDerivation.ofQueueParStep step.queueStep
      activeFacts.1.derivation step.consumer.linkIndex step.submitted_par
  have eventLeftRegion :
      SourceLeftRegionVertex certificate step.consumer.conclusion
        event.search.result.left :=
    event.leftEndpoint_sourceLeftRegion_of_touched touched
  have eventLeftOutputOwned :
      event.search.result.left ∈
        step.consumer.conclusion :: ownedAt step.queueStep.outputToken :=
    outputDerivation.sourceLeftRegion_owned invariant.structural
      (by simp) eventLeftRegion
  have eventAxiomMembership :
      Link.axiom event.search.result.left event.search.result.right ∈
        certificate.links :=
    List.mem_of_getElem? event.search.result.exactLink
  have forwardParMembership :
      Link.par step.consumer.storedLeft step.consumer.storedRight
          step.consumer.conclusion ∈ certificate.links :=
    List.mem_of_getElem? step.submitted_par
  have eventLeftNeConclusion :
      event.search.result.left ≠ step.consumer.conclusion := by
    intro same
    exact invariant.structural.axiomEndpoint_ne_connectiveConclusion
      eventAxiomMembership (Or.inl rfl) forwardParMembership
      (by simpa [Link.produces] using same.symm)
  have eventLeftActiveOwned :
      event.search.result.left ∈ ownedAt step.queueStep.outputToken := by
    rcases List.mem_cons.mp eventLeftOutputOwned with same | membership
    · exact False.elim (eventLeftNeConclusion same)
    · exact membership
  have olderBefore :
      before.core.representative event.rawAge <
        before.core.representative step.prepared.stackResult.rawAge := by
    rw [← step.prepared.after_representative_eq_before event.rawAge,
      ← step.prepared.after_representative_eq_before
        step.prepared.stackResult.rawAge]
    exact older
  have activeBeforeRoot :
      before.core.representative step.prepared.stackResult.rawAge =
        step.queueStep.outputToken := by
    rw [← step.prepared.after_representative_eq_before
      step.prepared.stackResult.rawAge]
    change
      step.prepared.coreMarked.representative
          step.prepared.stackResult.rawAge = step.queueStep.outputToken
    simpa [step.output_token_eq_active] using activeRoot
  have differentSlots :
      before.core.representative event.rawAge ≠
        step.queueStep.outputToken := by
    intro same
    rw [← activeBeforeRoot] at same
    exact (Nat.ne_of_lt olderBefore) same
  have ownedDisjoint :=
    (separated eventLookup activeBeforeLookup differentSlots).2
  exact ownedDisjoint event.search.result.left eventLeftForestOwned
    eventLeftActiveOwned

/-- A successful forward preserves the invariant once the exact created
conclusion obligation is supplied in the prepared middle state. -/
private theorem ForwardStep.olderMarkedTensorPredecessorInvariant_of_created
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (prior : OlderMarkedTensorPredecessorInvariant certificate before)
    (created : ForwardCreatedOlderMarkedTensorPredecessor step) :
    OlderMarkedTensorPredecessorInvariant certificate after := by
  have middle :
      OlderMarkedTensorPredecessorInvariant certificate
        step.prepared.after :=
    step.prepared.olderMarkedTensorPredecessorInvariant invariant prior
  intro candidateRawAge candidateVertex work outer tensorKind
    mateRawAge mateMarkedAfter representativeLt
  have afterCore : after.core = step.coreAfter :=
    congrArg (fun state : ReservationState ↦ state.core) step.output_eq
  have afterStack : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState ↦ state.stack) step.output_eq
  have mateMarkedMiddle :
      step.prepared.after.core.marks[outer.mate]? =
        some (some mateRawAge) := by
    rw [afterCore] at mateMarkedAfter
    change step.coreAfter.marks[outer.mate]? = some (some mateRawAge)
      at mateMarkedAfter
    rw [step.queueStep.after_eq] at mateMarkedAfter
    exact mateMarkedAfter
  have representativeLtMiddle :
      step.prepared.after.core.representative mateRawAge <
        step.prepared.after.core.representative candidateRawAge := by
    rw [← step.after_representative_eq_prepared mateRawAge]
    rw [← step.after_representative_eq_prepared candidateRawAge]
    exact representativeLt
  have sigmaEq : after.stack.sigma = step.prepared.after.stack.sigma := by
    rw [afterStack, step.prependStep.after_eq]
    rfl
  rcases work.beforeForwardOrInserted step with
    oldWork | ⟨candidateAge, candidateHead⟩
  · rcases middle oldWork outer tensorKind mateMarkedMiddle
        representativeLtMiddle with
      ⟨previousBoundary, ⟨predecessor⟩⟩
    refine ⟨previousBoundary, ⟨?_⟩⟩
    simpa [sigmaEq] using predecessor
  · subst candidateRawAge
    subst candidateVertex
    rcases created outer tensorKind mateMarkedMiddle
        representativeLtMiddle with
      ⟨previousBoundary, ⟨predecessor⟩⟩
    refine ⟨previousBoundary, ⟨?_⟩⟩
    simpa [sigmaEq] using predecessor

end SequentialFigure7
end ProofNetIR

namespace ProofNetIR
namespace SequentialFigure7

open SequentialUnification
open SequentialSchedulerBridge
open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState

private theorem ForwardStep.createdConclusion_olderMarkedTensorPredecessorMiddle
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.forward, after⟩}
    (step : ForwardStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (outer : ConnectiveBelow certificate step.consumer.conclusion)
    (outerTensor : outer.kind = .tensor)
    {mateRawAge : RawTokenAge}
    (mateMarkedMiddle :
      step.prepared.after.core.marks[outer.mate]? =
        some (some mateRawAge))
    (olderMiddle :
      step.prepared.after.core.representative mateRawAge <
        step.prepared.after.core.representative
          step.prepared.stackResult.rawAge) :
    ∃ previousBoundary,
      Nonempty
        (SigmaImmediatePredecessorAt step.prepared.after.stack.sigma
          step.prepared.stackResult.rawAge mateRawAge previousBoundary) := by
  let afterHistory : ExecutedHistory certificate after :=
    ExecutedHistory.later history invariant dispatch
  let afterTags : CanonicalTagHistory certificate afterHistory :=
    CanonicalTagHistory.later prior (DispatchTagEvidence.forward step)
  have afterInvariant : SchedulerInvariant certificate after :=
    step.schedulerInvariant invariant
  have work : FutureWorkAt after step.prepared.stackResult.rawAge
      step.consumer.conclusion :=
    step.createdConclusion_futureWorkAt
  let tensor : TensorBelow := connectiveBelowToTensor outer outerTensor
  have tensorValid :
      tensor.Valid certificate certificate.consumerIndex
        step.consumer.conclusion := by
    refine ⟨outer.consumer_eq, ?_, ?_, ?_⟩
    · simpa [tensor, connectiveBelowToTensor, outerTensor,
        SequentialConnectiveKind.asLink] using outer.link_eq
    · simpa [tensor, connectiveBelowToTensor, outerTensor,
        SequentialConnectiveKind.asLink] using outer.wellFormed
    · simpa [tensor, connectiveBelowToTensor, TensorBelow.premise] using
        outer.premise_eq
  have afterCore : after.core = step.coreAfter :=
    congrArg (fun state : ReservationState ↦ state.core) step.output_eq
  have mateMarkedAfter :
      after.core.marks[tensor.mate]? = some (some mateRawAge) := by
    rw [afterCore, step.queueStep.after_eq]
    simpa [tensor, connectiveBelowToTensor, TensorBelow.mate,
      ConnectiveBelow.mate, PreparedStep.after] using mateMarkedMiddle
  have olderAfter :
      after.core.representative mateRawAge <
        after.core.representative step.prepared.stackResult.rawAge := by
    rw [step.after_representative_eq_prepared mateRawAge,
      step.after_representative_eq_prepared
        step.prepared.stackResult.rawAge]
    exact olderMiddle
  have headSeparated : ∀ event : ReservationEvent certificate,
      event ∈ afterTags.reservationLedger →
      after.core.representative event.rawAge <
          after.core.representative step.prepared.stackResult.rawAge →
      ¬ event.Touched step.consumer.conclusion := by
    intro event eventMembership eventOlder
    have priorMembership : event ∈ prior.reservationLedger := by
      simpa [afterTags, CanonicalTagHistory.reservationLedger,
        DispatchTagEvidence.reservationEvents] using eventMembership
    have eventOlderMiddle :
        step.prepared.after.core.representative event.rawAge <
          step.prepared.after.core.representative
            step.prepared.stackResult.rawAge := by
      rw [← step.after_representative_eq_prepared event.rawAge,
        ← step.after_representative_eq_prepared
          step.prepared.stackResult.rawAge]
      exact eventOlder
    exact step.createdConclusionTouchSeparated prior correct.1 event
      priorMembership eventOlderMiddle
  have childAnchor :
      ForwardCreatedConclusionTensorChildAnchor step afterTags tensor :=
    step.createdConclusionTensorChildAnchor afterTags correct invariant
      afterInvariant tensor tensorValid
  rcases afterTags.markedMate_sigmaImmediatePredecessor_of_childAnchor
      correct afterInvariant work tensor tensorValid mateMarkedAfter olderAfter
      headSeparated childAnchor with
    ⟨predecessor⟩
  have afterStack : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState ↦ state.stack) step.output_eq
  have sigmaEq : after.stack.sigma = step.prepared.after.stack.sigma := by
    have prependSigma :
        step.stackAfter.sigma = step.prepared.after.stack.sigma := by
      simpa [PreparedStep.after] using
        congrArg SequentialStackState.sigma step.prependStep.after_eq
    exact (congrArg SequentialStackState.sigma afterStack).trans
      prependSigma
  refine ⟨mateRawAge, ⟨{
    position := predecessor.position
    previous_at := ?_
    candidate_at := ?_
    mate_boundary := ?_ }⟩⟩
  · simpa [sigmaEq] using predecessor.previous_at
  · simpa [sigmaEq] using predecessor.candidate_at
  · simpa [sigmaEq] using predecessor.mate_boundary

namespace CanonicalTagHistory

/-- A canonical successful `forward` preserves the all-future-work older
marked-tensor predecessor invariant. Retained work transports through the
prepared prefix, while the inserted par conclusion is discharged by the
conditional child-anchor bridge after private Forward-specific history,
component, and touch geometry.

This theorem assumes an already-successful typed dispatcher branch. It proves
no branch applicability, dispatcher progress or totality, global raw seam,
fallback removal, sequentialization, or complexity bound. -/
theorem forward_olderMarkedTensorPredecessorInvariant
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.forward, after⟩}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (step : ForwardStep certificate before after)
    (prior : OlderMarkedTensorPredecessorInvariant certificate before) :
    OlderMarkedTensorPredecessorInvariant certificate after := by
  apply step.olderMarkedTensorPredecessorInvariant_of_created invariant prior
  intro outer outerTensor mateRawAge mateMarkedMiddle olderMiddle
  exact step.createdConclusion_olderMarkedTensorPredecessorMiddle
    (invariant := invariant) (dispatch := dispatch) tagHistory correct outer
      outerTensor mateMarkedMiddle olderMiddle

end CanonicalTagHistory
end SequentialFigure7
end ProofNetIR
