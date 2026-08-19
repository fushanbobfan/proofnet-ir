/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderMarkedTensorPredecessorWaitPreservation
import ProofNetIR.SequentialFigure7CrossRepresentativeUnifyPayloadPreservation
import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchUnifyPayloadDischarge
import ProofNetIR.SequentialComponentReferenceGeometry
import ProofNetIR.SequentialFigure7OlderMarkedTensorPredecessorInvariant

/-!
# UnifyPayload preservation of the older marked-tensor predecessor invariant

A successful `unifyPayload` retires the active boundary into the preceding
boundary, preserves retained future work, moves the active ready bucket, and
inserts the selected tensor conclusion. Retained predecessor evidence survives
the final sigma pop. A moved active occurrence would force its marked mate to
resolve both to and strictly below the surviving boundary, so that case is
impossible. The inserted conclusion is discharged by the public conditional
child-anchor bridge using final component provenance and the carrier-free
UnifyPayload touch theorem.

Only
`CanonicalTagHistory.unifyPayload_olderMarkedTensorPredecessorInvariant` is
public in this module. The proof assumes an already-successful typed branch
and proves no applicability, dispatcher progress or totality, global raw seam,
fallback removal, sequentialization, or complexity bound.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialUnification
open SequentialSchedulerBridge
open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState

namespace UnifyPayloadStep

private theorem activeBoundary_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.mergeStep.activeBoundary =
      step.prepared.stackResult.rawAge := by
  have mergeTop :
      step.prepared.stackResult.after.sigma.getLast? =
        some step.mergeStep.activeBoundary := by
    rw [step.mergeStep.sigma_eq]
    simp
  have preparedTop :
      step.prepared.stackResult.after.sigma.getLast? =
        some step.prepared.stackResult.rawAge := by
    rcases SequentialStackState.popReadyMark?_exact step.prepared.stack_eq with
      ⟨_, sigmaTop, _, _, _, sigmaAfter, _, _, _⟩
    rw [sigmaAfter]
    exact sigmaTop
  exact Option.some.inj (mergeTop.symm.trans preparedTop)

private theorem middleSigma_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.prepared.after.stack.sigma =
      step.mergeStep.sigmaPrefix ++
        [step.previousBoundary, step.prepared.stackResult.rawAge] := by
  simpa [PreparedStep.after, step.activeBoundary_eq] using
    step.mergeStep.sigma_eq

private theorem afterSigma_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    after.stack.sigma =
      step.mergeStep.sigmaPrefix ++ [step.previousBoundary] := by
  have afterStack : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState ↦ state.stack) step.output_eq
  rw [afterStack]
  simpa using congrArg SequentialStackState.sigma step.mergeStep.after_eq

private theorem previous_lt_active
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.previousBoundary < step.prepared.stackResult.rawAge :=
  Nat.lt_of_le_of_lt step.lower step.upper

private theorem middle_previous_root
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.after.core.representative step.previousBoundary =
      step.previousBoundary := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have previousMembership :
      step.previousBoundary ∈ step.prepared.after.stack.sigma := by
    rw [step.middleSigma_eq]
    simp
  have previousBound :
      step.previousBoundary < step.prepared.after.stack.nextAge :=
    middleInvariant.stack_wellShaped.sigma_partition.boundary_lt _
      previousMembership
  have lookup :
      sigmaBoundary? step.prepared.after.stack.sigma
          step.previousBoundary = some step.previousBoundary :=
    middleInvariant.stack_wellShaped.sigma_partition
      |>.sigmaBoundary?_eq_previous_of_between step.middleSigma_eq
        (Nat.le_refl _) step.previous_lt_active
  have realized :=
    middleInvariant.realizesSigma.representative_eq_boundary previousBound
  exact Option.some.inj (realized.symm.trans lookup)

private theorem rawAge_le_previousBoundary_of_unifyPayload
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt after rawAge vertex) :
    rawAge ≤ step.previousBoundary := by
  have afterInvariant := step.schedulerInvariant invariant
  have membership := work.rawAge_mem_sigma afterInvariant
  have increasing :=
    afterInvariant.stack_wellShaped.sigma_partition.strictIncreasing
  rw [step.afterSigma_eq] at membership increasing
  simp only [List.mem_append, List.mem_singleton] at membership
  rcases membership with inPrefix | same
  · exact Nat.le_of_lt
      ((List.pairwise_append.mp increasing).2.2 rawAge inPrefix
        step.previousBoundary (by simp))
  · exact Nat.le_of_eq same

private theorem event_rawAge_lt_nextAge
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (prior : CanonicalTagHistory certificate history)
    {event : ReservationEvent certificate}
    (membership : event ∈ prior.reservationLedger) :
    event.rawAge < before.stack.nextAge := by
  have mapped :
      event.rawAge ∈ prior.reservationLedger.map ReservationEvent.rawAge :=
    List.mem_map_of_mem
      (f := fun e : ReservationEvent certificate ↦ e.rawAge) membership
  rw [prior.reservationLedger_rawAges] at mapped
  exact List.mem_range.mp mapped

private theorem middleNextAge_eq_before
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.prepared.after.stack.nextAge = before.stack.nextAge := by
  rcases SequentialStackState.popReadyMark?_exact step.prepared.stack_eq with
    ⟨_, _, _, _, nextAge, _, _, _, _⟩
  exact nextAge

private theorem event_representative_eq_prepared_of_olderWork
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (prior : CanonicalTagHistory certificate history)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ prior.reservationLedger)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (work : FutureWorkAt after candidateRawAge candidateVertex)
    (older :
      after.core.representative event.rawAge <
        after.core.representative candidateRawAge) :
    after.core.representative event.rawAge =
      step.prepared.after.core.representative event.rawAge := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have eventBeforeBound := event_rawAge_lt_nextAge prior eventMembership
  have eventMiddleBound :
      event.rawAge < step.prepared.after.core.parents.size := by
    rw [middleInvariant.realizesSigma.horizon_eq,
      step.middleNextAge_eq_before]
    exact eventBeforeBound
  have mapped :=
    step.after_representative_eq_prepared_if eventMiddleBound
  by_cases retired :
      step.prepared.after.core.representative event.rawAge =
        step.prepared.stackResult.rawAge
  · have afterEvent :
        after.core.representative event.rawAge =
          step.previousBoundary := by
      simpa [retired] using mapped
    have afterCandidate :=
      work.representative_eq_rawAge (step.schedulerInvariant invariant)
    have candidateLe :=
      step.rawAge_le_previousBoundary_of_unifyPayload invariant work
    have impossible : step.previousBoundary < candidateRawAge := by
      rw [afterEvent, afterCandidate] at older
      exact older
    exact (Nat.not_lt_of_ge candidateLe impossible).elim
  · simpa [retired] using mapped

private theorem markedMate_representative_eq_prepared_of_older
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (work : FutureWorkAt after candidateRawAge candidateVertex)
    {mateVertex : Vertex} {mateRawAge : RawTokenAge}
    (mateMarked :
      after.core.marks[mateVertex]? = some (some mateRawAge))
    (older :
      after.core.representative mateRawAge <
        after.core.representative candidateRawAge) :
    after.core.representative mateRawAge =
      step.prepared.after.core.representative mateRawAge := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have middleMarked :
      step.prepared.after.core.marks[mateVertex]? =
        some (some mateRawAge) := by
    rw [← step.after_marks_eq_prepared]
    exact mateMarked
  have middleStackMarked :
      step.prepared.after.stack.marks[mateVertex]? =
        some (some mateRawAge) := by
    rw [← middleInvariant.realizesSigma.marks_eq]
    exact middleMarked
  have mateMiddleAgeBound :
      mateRawAge < step.prepared.after.stack.nextAge :=
    middleInvariant.stack_wellShaped.assigned_age_bound
      mateVertex mateRawAge middleStackMarked
  have mateMiddleCoreBound :
      mateRawAge < step.prepared.after.core.parents.size := by
    rw [middleInvariant.realizesSigma.horizon_eq]
    exact mateMiddleAgeBound
  have mapped :=
    step.after_representative_eq_prepared_if mateMiddleCoreBound
  by_cases retired :
      step.prepared.after.core.representative mateRawAge =
        step.prepared.stackResult.rawAge
  · have afterMate :
        after.core.representative mateRawAge =
          step.previousBoundary := by
      simpa [retired] using mapped
    have afterCandidate :=
      work.representative_eq_rawAge (step.schedulerInvariant invariant)
    have candidateLe :=
      step.rawAge_le_previousBoundary_of_unifyPayload invariant work
    have impossible : step.previousBoundary < candidateRawAge := by
      rw [afterMate, afterCandidate] at older
      exact older
    exact (Nat.not_lt_of_ge candidateLe impossible).elim
  · simpa [retired] using mapped

private theorem retained_predecessor_lookups
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    {candidateRawAge mateRawAge previousBoundary : RawTokenAge}
    (candidateLe : candidateRawAge ≤ step.previousBoundary)
    (predecessor :
      SigmaImmediatePredecessorAt step.prepared.after.stack.sigma
        candidateRawAge mateRawAge previousBoundary) :
    after.stack.sigma[predecessor.position]? = some previousBoundary ∧
      after.stack.sigma[predecessor.position + 1]? =
        some candidateRawAge := by
  rcases predecessor with
    ⟨position, previousAt, candidateAt, _mateBoundary⟩
  let retainedSigma :=
    step.mergeStep.sigmaPrefix ++ [step.previousBoundary]
  have middleSigma :
      step.prepared.after.stack.sigma =
        retainedSigma ++ [step.prepared.stackResult.rawAge] := by
    rw [step.middleSigma_eq]
    simp [retainedSigma, List.append_assoc]
  have afterSigma : after.stack.sigma = retainedSigma := by
    simpa [retainedSigma] using step.afterSigma_eq
  have candidateMiddleBound :
      position + 1 <
        step.prepared.after.stack.sigma.length :=
    (List.getElem?_eq_some_iff.mp candidateAt).1
  have candidateLeLast :
      position + 1 ≤ retainedSigma.length := by
    rw [middleSigma] at candidateMiddleBound
    simp at candidateMiddleBound
    omega
  have candidateNeLast :
      position + 1 ≠ retainedSigma.length := by
    intro candidateLast
    have candidateAtActive := candidateAt
    rw [middleSigma, candidateLast] at candidateAtActive
    simp at candidateAtActive
    have candidateEqActive :
        candidateRawAge = step.prepared.stackResult.rawAge :=
      candidateAtActive.symm
    have activeLePrevious :
        step.prepared.stackResult.rawAge ≤ step.previousBoundary := by
      rw [← candidateEqActive]
      exact candidateLe
    exact (Nat.not_le_of_gt step.previous_lt_active) activeLePrevious
  have candidateRetainedBound :
      position + 1 < retainedSigma.length :=
    Nat.lt_of_le_of_ne candidateLeLast candidateNeLast
  have previousRetainedBound :
      position < retainedSigma.length := by
    omega
  constructor
  · rw [afterSigma]
    rw [middleSigma,
      List.getElem?_append_left previousRetainedBound] at previousAt
    exact previousAt
  · rw [afterSigma]
    rw [middleSigma,
      List.getElem?_append_left candidateRetainedBound] at candidateAt
    exact candidateAt

private theorem active_predecessor_previous_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {mateRawAge previousBoundary : RawTokenAge}
    (predecessor :
      SigmaImmediatePredecessorAt step.prepared.after.stack.sigma
        step.prepared.stackResult.rawAge mateRawAge previousBoundary) :
    previousBoundary = step.previousBoundary := by
  rcases predecessor with
    ⟨position, previousAt, candidateAt, _mateBoundary⟩
  let retainedSigma :=
    step.mergeStep.sigmaPrefix ++ [step.previousBoundary]
  have middleSigma :
      step.prepared.after.stack.sigma =
        retainedSigma ++ [step.prepared.stackResult.rawAge] := by
    rw [step.middleSigma_eq]
    simp [retainedSigma, List.append_assoc]
  have candidateBound :
      position + 1 <
        step.prepared.after.stack.sigma.length :=
    (List.getElem?_eq_some_iff.mp candidateAt).1
  have candidateLeLast :
      position + 1 ≤ retainedSigma.length := by
    rw [middleSigma] at candidateBound
    simp at candidateBound
    omega
  have activeAtLast :
      step.prepared.after.stack.sigma[retainedSigma.length]? =
        some step.prepared.stackResult.rawAge := by
    rw [middleSigma]
    simp
  have candidateIndex :
      position + 1 = retainedSigma.length := by
    by_cases same : position + 1 = retainedSigma.length
    · exact same
    · have candidateLtLast : position + 1 < retainedSigma.length :=
        Nat.lt_of_le_of_ne candidateLeLast same
      rcases List.getElem?_eq_some_iff.mp candidateAt with
        ⟨candidateBound', candidateValue⟩
      rcases List.getElem?_eq_some_iff.mp activeAtLast with
        ⟨activeBound, activeValue⟩
      have middleIncreasing :=
        (step.prepared.schedulerInvariant invariant)
          |>.stack_wellShaped.sigma_partition.strictIncreasing
      have strict :=
        (List.pairwise_iff_getElem.mp middleIncreasing)
          (position + 1) retainedSigma.length candidateBound'
            activeBound candidateLtLast
      rw [candidateValue, activeValue] at strict
      exact False.elim (Nat.lt_irrefl _ strict)
  have previousIndex :
      position = step.mergeStep.sigmaPrefix.length := by
    simp [retainedSigma] at candidateIndex
    omega
  rw [step.middleSigma_eq, previousIndex] at previousAt
  simpa using previousAt.symm

private theorem middleMateRepresentative_eq_previous
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {mateVertex : Vertex} {mateRawAge previousBoundary candidateRawAge : Nat}
    (mateMarked :
      step.prepared.after.core.marks[mateVertex]? =
        some (some mateRawAge))
    (predecessor :
      SigmaImmediatePredecessorAt step.prepared.after.stack.sigma
        candidateRawAge mateRawAge previousBoundary) :
    step.prepared.after.core.representative mateRawAge =
      previousBoundary := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have stackMarked :
      step.prepared.after.stack.marks[mateVertex]? =
        some (some mateRawAge) := by
    rw [← middleInvariant.realizesSigma.marks_eq]
    exact mateMarked
  have mateAgeBound : mateRawAge < step.prepared.after.stack.nextAge :=
    middleInvariant.stack_wellShaped.assigned_age_bound
      mateVertex mateRawAge stackMarked
  have realized :=
    middleInvariant.realizesSigma.representative_eq_boundary mateAgeBound
  exact Option.some.inj
    (realized.symm.trans predecessor.mate_boundary)

private theorem afterMateBoundary_eq_previous
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {mateVertex : Vertex} {mateRawAge previousBoundary : Nat}
    (mateMarked : after.core.marks[mateVertex]? = some (some mateRawAge))
    (representativeEq :
      after.core.representative mateRawAge = previousBoundary) :
    sigmaBoundary? after.stack.sigma mateRawAge = some previousBoundary := by
  have afterInvariant := step.schedulerInvariant invariant
  have stackMarked :
      after.stack.marks[mateVertex]? = some (some mateRawAge) := by
    rw [← afterInvariant.realizesSigma.marks_eq]
    exact mateMarked
  have mateAgeBound : mateRawAge < after.stack.nextAge :=
    afterInvariant.stack_wellShaped.assigned_age_bound
      mateVertex mateRawAge stackMarked
  exact (afterInvariant.realizesSigma.representative_eq_boundary
    mateAgeBound).trans (congrArg some representativeEq)

private theorem afterReady_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    after.stack.ready =
      step.mergeStep.readyPrefix ++
        [step.consumer.conclusion ::
          (step.payload ++ step.mergeStep.previousReady ++
            step.mergeStep.activeReady)] := by
  have afterStack : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState ↦ state.stack) step.output_eq
  rw [afterStack]
  exact step.exact.2.1

private theorem prefixLengths
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.mergeStep.sigmaPrefix.length =
      step.mergeStep.readyPrefix.length := by
  have middleInvariant :
      ReservationInvariant certificate step.prepared.after :=
    step.prepared.reservationInvariant step.before_invariant
  have aligned := middleInvariant.stack_wellShaped.ready_aligned
  change
    step.prepared.stackResult.after.ready.length =
      step.prepared.stackResult.after.sigma.length at aligned
  rw [step.mergeStep.ready_eq, step.mergeStep.sigma_eq] at aligned
  simp at aligned
  omega

private theorem createdConclusion_readyData
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    after.stack.sigma[step.mergeStep.sigmaPrefix.length]? =
        some step.previousBoundary ∧
      after.stack.ready[step.mergeStep.sigmaPrefix.length]? =
        some
          (step.consumer.conclusion ::
            (step.payload ++ step.mergeStep.previousReady ++
              step.mergeStep.activeReady)) ∧
      step.consumer.conclusion ∈
        step.consumer.conclusion ::
          (step.payload ++ step.mergeStep.previousReady ++
            step.mergeStep.activeReady) := by
  constructor
  · rw [step.afterSigma_eq]
    simp
  · constructor
    · rw [step.afterReady_eq, step.prefixLengths]
      simp
    · simp

private theorem createdConclusion_futureWorkAt
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    FutureWorkAt after step.previousBoundary
      step.consumer.conclusion := by
  rcases step.createdConclusion_readyData with
    ⟨sigmaAt, readyAt, member⟩
  exact FutureWorkAt.ready sigmaAt readyAt member

private theorem mem_liveFrontierVertices
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

private theorem tensorConclusion_not_produced_of_work
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

private theorem tensorConclusion_not_owned_of_work
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
  apply tensorConclusion_not_produced_of_work invariant work outer
    outerValid
  rcases accounted outer.conclusion conclusionOwned with
    ⟨rawAge, marked, _representative⟩ | ⟨_unmarked, frontier⟩
  · exact Or.inl ⟨rawAge, marked⟩
  · exact Or.inr
      (mem_liveFrontierVertices componentLookup frontier)

private theorem createdConclusionTensorChildAnchor
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate after}
    (step : UnifyPayloadStep certificate before after)
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (beforeInvariant : SchedulerInvariant certificate before)
    (outer : TensorBelow)
    (outerValid :
      outer.Valid certificate certificate.consumerIndex
        step.consumer.conclusion) :
    ∀ childEvent : ReservationEvent certificate,
      tagHistory.reservationLedger[step.previousBoundary]? =
          some childEvent →
        ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
          path.start = childEvent.search.result.left ∧
            path.finish = step.consumer.conclusion ∧
              outer.conclusion ∉ path.vertices := by
  intro childEvent childLookup
  have afterInvariant := step.schedulerInvariant beforeInvariant
  have work : FutureWorkAt after step.previousBoundary
      step.consumer.conclusion :=
    step.createdConclusion_futureWorkAt
  have boundaryBound : step.previousBoundary < after.stack.nextAge :=
    work.rawAge_lt_nextAge afterInvariant
  have childRawAge : childEvent.rawAge = step.previousBoundary := by
    have mapped := tagHistory.reservationLedger_getElem?_rawAge
      step.previousBoundary boundaryBound
    simpa [childLookup] using mapped
  have childMembership : childEvent ∈ tagHistory.reservationLedger :=
    List.mem_of_getElem? childLookup
  rcases tagHistory.reservationLedger_axiomEndpoints_accounted
      correct.1 childMembership with
    ⟨childComponent, _childUsed, _childForest, childOwned,
      childComponentLookup, childDerivation, _childLink, childWitness,
      childAccounted, childLeftOwned, _childRightOwned⟩
  have boundaryRoot :
      after.core.representative step.previousBoundary =
        step.previousBoundary :=
    work.representative_eq_rawAge afterInvariant
  have childLookupAtBoundary :
      after.core.components[step.previousBoundary]? =
        some (some childComponent) := by
    simpa [childRawAge, boundaryRoot] using childComponentLookup
  rcases step.createdConclusion_readyData with
    ⟨sigmaAt, readyAt, conclusionInBucket⟩
  rcases afterInvariant.ready_bucket_frontier_exact sigmaAt readyAt with
    ⟨readyComponent, readyComponentLookup, exactMembership⟩
  have conclusionInFrontier :
      step.consumer.conclusion ∈ readyComponent.frontier :=
    (exactMembership step.consumer.conclusion).mp conclusionInBucket |>.1
  have componentEq : childComponent = readyComponent :=
    Option.some.inj
      (Option.some.inj
        (childLookupAtBoundary.symm.trans readyComponentLookup))
  subst readyComponent
  have conclusionChildOwned : step.consumer.conclusion ∈ childOwned :=
    childDerivation.frontier_subset_owned step.consumer.conclusion
      conclusionInFrontier
  rcases childWitness.referencePath_within_owned childLeftOwned
      conclusionChildOwned with
    ⟨path, pathStarts, pathFinishes, pathWithin⟩
  have outerNotChildOwned : outer.conclusion ∉ childOwned :=
    tensorConclusion_not_owned_of_work afterInvariant work outer outerValid
      childLookupAtBoundary (by
        simpa [childRawAge, boundaryRoot] using childAccounted)
  have pathAvoids : outer.conclusion ∉ path.vertices := by
    intro membership
    exact outerNotChildOwned (pathWithin outer.conclusion membership)
  exact ⟨path, pathStarts, pathFinishes, pathAvoids⟩

end UnifyPayloadStep

namespace CanonicalTagHistory

/-- A canonical successful `unifyPayload` preserves the all-future-work older
marked-tensor predecessor invariant. Retained work transports across the
active-boundary retirement, moved active work is incompatible with the strict
output ordering, and the inserted tensor conclusion is discharged through the
conditional child-anchor bridge.

This theorem assumes an already-successful typed dispatcher branch. It proves
no branch applicability, dispatcher progress or totality, global raw seam,
fallback removal, sequentialization, or complexity bound. -/
theorem unifyPayload_olderMarkedTensorPredecessorInvariant
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch :
      DispatchStep certificate before invariant ⟨.unifyPayload, after⟩}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (step : UnifyPayloadStep certificate before after)
    (prior : OlderMarkedTensorPredecessorInvariant certificate before) :
    OlderMarkedTensorPredecessorInvariant certificate after := by
  let afterHistory : ExecutedHistory certificate after :=
    ExecutedHistory.later history invariant dispatch
  let afterTags : CanonicalTagHistory certificate afterHistory :=
    CanonicalTagHistory.later tagHistory
      (DispatchTagEvidence.unifyPayload step)
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have afterInvariant := step.schedulerInvariant invariant
  have middlePredecessor :
      OlderMarkedTensorPredecessorInvariant certificate
        step.prepared.after :=
    step.prepared.olderMarkedTensorPredecessorInvariant invariant prior
  intro candidateRawAge candidateVertex work consumer tensorKind
    mateRawAge mateMarked older
  have middleMarked :
      step.prepared.after.core.marks[consumer.mate]? =
        some (some mateRawAge) := by
    rw [← step.after_marks_eq_prepared]
    exact mateMarked
  have mateRepresentativeUnchanged :=
    step.markedMate_representative_eq_prepared_of_older invariant work
      mateMarked older
  have afterCandidateRoot :=
    work.representative_eq_rawAge afterInvariant
  rcases work.beforeUnifyPayloadOrMovedOrCreated step with
    oldWork | ⟨candidateAge, movedWork⟩ |
      ⟨candidateAge, candidateHead⟩
  · have middleCandidateRoot :=
      oldWork.representative_eq_rawAge middleInvariant
    have olderMiddle :
        step.prepared.after.core.representative mateRawAge <
          step.prepared.after.core.representative candidateRawAge := by
      calc
        step.prepared.after.core.representative mateRawAge =
            after.core.representative mateRawAge :=
          mateRepresentativeUnchanged.symm
        _ < after.core.representative candidateRawAge := older
        _ = candidateRawAge := afterCandidateRoot
        _ = step.prepared.after.core.representative candidateRawAge :=
          middleCandidateRoot.symm
    rcases middlePredecessor oldWork consumer tensorKind middleMarked
        olderMiddle with
      ⟨previousBoundary, ⟨predecessor⟩⟩
    have candidateLe :=
      step.rawAge_le_previousBoundary_of_unifyPayload invariant work
    rcases step.retained_predecessor_lookups candidateLe predecessor with
      ⟨previousAt, candidateAt⟩
    have middleMateRepresentative :
        step.prepared.after.core.representative mateRawAge =
          previousBoundary :=
      step.middleMateRepresentative_eq_previous invariant middleMarked
        predecessor
    have afterMateRepresentative :
        after.core.representative mateRawAge = previousBoundary :=
      mateRepresentativeUnchanged.trans middleMateRepresentative
    have mateBoundary :=
      step.afterMateBoundary_eq_previous invariant mateMarked
        afterMateRepresentative
    exact ⟨previousBoundary, ⟨{
      position := predecessor.position
      previous_at := previousAt
      candidate_at := candidateAt
      mate_boundary := mateBoundary }⟩⟩
  · subst candidateRawAge
    have movedRoot :=
      movedWork.representative_eq_rawAge middleInvariant
    have olderMiddle :
        step.prepared.after.core.representative mateRawAge <
          step.prepared.after.core.representative
            step.prepared.stackResult.rawAge := by
      calc
        step.prepared.after.core.representative mateRawAge =
            after.core.representative mateRawAge :=
          mateRepresentativeUnchanged.symm
        _ < after.core.representative step.previousBoundary := older
        _ = step.previousBoundary := afterCandidateRoot
        _ < step.prepared.stackResult.rawAge :=
          step.previous_lt_active
        _ = step.prepared.after.core.representative
            step.prepared.stackResult.rawAge := movedRoot.symm
    rcases middlePredecessor movedWork consumer tensorKind middleMarked
        olderMiddle with
      ⟨previousBoundary, ⟨predecessor⟩⟩
    have previousEq :=
      step.active_predecessor_previous_eq invariant predecessor
    have middleMateRepresentative :
        step.prepared.after.core.representative mateRawAge =
          previousBoundary :=
      step.middleMateRepresentative_eq_previous invariant middleMarked
        predecessor
    have afterMateRepresentative :
        after.core.representative mateRawAge = step.previousBoundary := by
      calc
        after.core.representative mateRawAge =
            step.prepared.after.core.representative mateRawAge :=
          mateRepresentativeUnchanged
        _ = previousBoundary := middleMateRepresentative
        _ = step.previousBoundary := previousEq
    rw [afterMateRepresentative, afterCandidateRoot] at older
    exact False.elim (Nat.lt_irrefl _ older)
  · subst candidateRawAge
    subst candidateVertex
    let tensor : TensorBelow :=
      connectiveBelowToTensor consumer tensorKind
    have tensorValid :
        tensor.Valid certificate certificate.consumerIndex
          step.consumer.conclusion := by
      refine ⟨consumer.consumer_eq, ?_, ?_, ?_⟩
      · simpa [tensor, connectiveBelowToTensor, tensorKind,
          SequentialConnectiveKind.asLink] using consumer.link_eq
      · simpa [tensor, connectiveBelowToTensor, tensorKind,
          SequentialConnectiveKind.asLink] using consumer.wellFormed
      · simpa [tensor, connectiveBelowToTensor, TensorBelow.premise] using
          consumer.premise_eq
    have tensorMateMarked :
        after.core.marks[tensor.mate]? = some (some mateRawAge) := by
      simpa [tensor, connectiveBelowToTensor, TensorBelow.mate,
        ConnectiveBelow.mate] using mateMarked
    have headSeparated : ∀ event : ReservationEvent certificate,
        event ∈ afterTags.reservationLedger →
        after.core.representative event.rawAge <
            after.core.representative step.previousBoundary →
        ¬ event.Touched step.consumer.conclusion := by
      intro event eventMembership eventOlder
      have priorMembership : event ∈ tagHistory.reservationLedger := by
        simpa [afterTags, CanonicalTagHistory.reservationLedger,
          DispatchTagEvidence.reservationEvents] using eventMembership
      have eventUnchanged :=
        step.event_representative_eq_prepared_of_olderWork invariant
          tagHistory priorMembership work eventOlder
      have eventOlderMiddle :
          step.prepared.after.core.representative event.rawAge <
            step.prepared.after.core.representative
              step.previousBoundary := by
        calc
          step.prepared.after.core.representative event.rawAge =
              after.core.representative event.rawAge :=
            eventUnchanged.symm
          _ < after.core.representative step.previousBoundary := eventOlder
          _ = step.previousBoundary := afterCandidateRoot
          _ = step.prepared.after.core.representative
              step.previousBoundary :=
            (step.middle_previous_root invariant).symm
      exact step.createdConclusionTouchSeparated tagHistory correct.1 event
        priorMembership eventOlderMiddle
    have childAnchor :=
      step.createdConclusionTensorChildAnchor afterTags correct invariant
        tensor tensorValid
    rcases afterTags.markedMate_sigmaImmediatePredecessor_of_childAnchor
        correct afterInvariant work tensor tensorValid tensorMateMarked older
        headSeparated childAnchor with
      ⟨predecessor⟩
    exact ⟨mateRawAge, ⟨predecessor⟩⟩

end CanonicalTagHistory
end SequentialFigure7
end ProofNetIR
