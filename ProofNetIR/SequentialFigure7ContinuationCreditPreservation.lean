/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ContinuationCredit

/-!
# Figure-7 continuation-credit preservation

Every successful typed dispatcher branch transports a continuation receipt
owned before the step. The one prepared-prefix residual is exact: `concl`,
`nop`, and `new` refute it, while `wait`, `forward`, and `unifyPayload` turn
the consumed mate into scheduled conclusion work. The dispatcher corollaries
lift the six local theorems to all old credits and to every concretely marked
non-conclusion. Exact canonical histories inherit the latter invariant.

This module proves preservation for already supplied typed executions. It does
not establish dispatcher progress, totality, termination, completeness, or the
existence of a canonical execution history for an arbitrary scheduler state.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- The same submitted connective viewed from its opposite premise. -/
private def connectiveBelowAtMate
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex)
    (structural : certificate.StructurallyWellFormed) :
    ConnectiveBelow certificate consumer.mate := by
  cases sideEquation : consumer.side with
  | storedLeft =>
      refine {
        linkIndex := consumer.linkIndex
        kind := consumer.kind
        storedLeft := consumer.storedLeft
        storedRight := consumer.storedRight
        conclusion := consumer.conclusion
        side := .storedRight
        consumer_eq := ?_
        link_eq := consumer.link_eq
        wellFormed := consumer.wellFormed
        premise_eq := ?_ }
      · apply ConsumerIndex.build_uniqueConsumer?_eq_some structural
          consumer.link_eq consumer.mate_bound
        cases kindEquation : consumer.kind <;>
          simp [SequentialConnectiveKind.asLink, Link.premises,
            ConnectiveBelow.mate, TensorPremiseSide.mate, sideEquation]
      · simp [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEquation,
          TensorPremiseSide.premise]

  | storedRight =>
      refine {
        linkIndex := consumer.linkIndex
        kind := consumer.kind
        storedLeft := consumer.storedLeft
        storedRight := consumer.storedRight
        conclusion := consumer.conclusion
        side := .storedLeft
        consumer_eq := ?_
        link_eq := consumer.link_eq
        wellFormed := consumer.wellFormed
        premise_eq := ?_ }
      · apply ConsumerIndex.build_uniqueConsumer?_eq_some structural
          consumer.link_eq consumer.mate_bound
        cases kindEquation : consumer.kind <;>
          simp [SequentialConnectiveKind.asLink, Link.premises,
            ConnectiveBelow.mate, TensorPremiseSide.mate, sideEquation]
      · simp [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEquation,
          TensorPremiseSide.premise]

/-- Viewing a submitted connective from its mate swaps the two premises. -/
private theorem connectiveBelowAtMate_mate
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex)
    (structural : certificate.StructurallyWellFormed) :
    (connectiveBelowAtMate consumer structural).mate = vertex := by
  rcases consumer with
    ⟨linkIndex, kind, storedLeft, storedRight, conclusion, side,
      consumerEq, linkEq, wellFormed, premiseEq⟩
  cases side <;>
    simp [connectiveBelowAtMate, ConnectiveBelow.mate,
      TensorPremiseSide.mate, TensorPremiseSide.premise] at premiseEq ⊢
  · exact premiseEq.symm
  · exact premiseEq.symm

/-- The opposite-premise view transported to an explicitly identified mate. -/
private def connectiveBelowAtMateEq
    {certificate : Certificate} {vertex mate : Vertex}
    (consumer : ConnectiveBelow certificate vertex)
    (structural : certificate.StructurallyWellFormed)
    (mateEquation : consumer.mate = mate) :
    ConnectiveBelow certificate mate := by
  rw [← mateEquation]
  exact connectiveBelowAtMate consumer structural

private theorem connectiveBelowAtMateEq_mate
    {certificate : Certificate} {vertex mate : Vertex}
    (consumer : ConnectiveBelow certificate vertex)
    (structural : certificate.StructurallyWellFormed)
    (mateEquation : consumer.mate = mate) :
    (connectiveBelowAtMateEq consumer structural mateEquation).mate = vertex := by
  subst mate
  exact connectiveBelowAtMate_mate consumer structural

private theorem connectiveBelowAtMateEq_conclusion
    {certificate : Certificate} {vertex mate : Vertex}
    (consumer : ConnectiveBelow certificate vertex)
    (structural : certificate.StructurallyWellFormed)
    (mateEquation : consumer.mate = mate) :
    (connectiveBelowAtMateEq consumer structural mateEquation).conclusion =
      consumer.conclusion := by
  subst mate
  rcases consumer with
    ⟨linkIndex, kind, storedLeft, storedRight, conclusion, side,
      consumerEq, linkEq, wellFormed, premiseEq⟩
  cases side <;> rfl

/-- Exact connective views at one occurrence agree on their conclusion. -/
private theorem connectiveBelow_conclusion_eq
    {certificate : Certificate} {vertex : Vertex}
    (left right : ConnectiveBelow certificate vertex) :
    left.conclusion = right.conclusion := by
  have sameIndex : left.linkIndex = right.linkIndex :=
    Option.some.inj (left.consumer_eq.symm.trans right.consumer_eq)
  have leftLookup := left.link_eq
  rw [sameIndex] at leftLookup
  have sameLink :
      left.kind.asLink left.storedLeft left.storedRight left.conclusion =
        right.kind.asLink right.storedLeft right.storedRight right.conclusion :=
    Option.some.inj (leftLookup.symm.trans right.link_eq)
  cases leftKind : left.kind <;> cases rightKind : right.kind <;>
    simp [SequentialConnectiveKind.asLink, leftKind, rightKind] at sameLink
  · exact sameLink.2.2
  · exact sameLink.2.2

/-- Exact connective views at one occurrence agree on their opposite premise. -/
private theorem connectiveBelow_mate_eq
    {certificate : Certificate} {vertex : Vertex}
    (left right : ConnectiveBelow certificate vertex) :
    left.mate = right.mate := by
  have sameIndex : left.linkIndex = right.linkIndex :=
    Option.some.inj (left.consumer_eq.symm.trans right.consumer_eq)
  have leftLookup := left.link_eq
  rw [sameIndex] at leftLookup
  have sameLink :
      left.kind.asLink left.storedLeft left.storedRight left.conclusion =
        right.kind.asLink right.storedLeft right.storedRight right.conclusion :=
    Option.some.inj (leftLookup.symm.trans right.link_eq)
  have leftPremise := left.premise_eq
  have rightPremise := right.premise_eq
  have leftDifferent := left.mate_ne
  cases leftKind : left.kind <;> cases rightKind : right.kind <;>
    cases leftSide : left.side <;> cases rightSide : right.side <;>
      simp_all [SequentialConnectiveKind.asLink, ConnectiveBelow.mate,
        TensorPremiseSide.mate, TensorPremiseSide.premise]

namespace FutureWorkAt

/-- A future-work occurrence before the common prefix either survives at the
same boundary or is exactly the selected ready head. -/
private theorem afterPrepared_or_selected
    {before : ReservationState} (step : PreparedStep before)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt before rawAge vertex) :
    FutureWorkAt step.after rawAge vertex ∨
      vertex = step.stackResult.vertex := by
  rcases work.afterPreparedOrSelected step with selected | survived
  · exact Or.inr selected
  · exact Or.inl survived

end FutureWorkAt

namespace PreparedStep

private theorem after_unmarked_of_ne_selected
    {before : ReservationState} (step : PreparedStep before)
    {vertex : Vertex}
    (different : vertex ≠ step.stackResult.vertex)
    (unmarked : before.core.marks[vertex]? = some none) :
    step.after.core.marks[vertex]? = some none := by
  rcases UnificationState.markReadyRaw?_exact step.core_mark_eq with
    ⟨_selectedUnmarked, marksEquation, _parents, _components,
      _started, _fired, _selectedMarked⟩
  change step.coreMarked.marks[vertex]? = some none
  rw [marksEquation]
  simpa [Array.getElem?_setIfInBounds, Ne.symm different] using unmarked

private theorem after_marked_of_before_marked
    {before : ReservationState} (step : PreparedStep before)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (marked : before.core.marks[vertex]? = some (some rawAge)) :
    step.after.core.marks[vertex]? = some (some rawAge) := by
  rcases UnificationState.markReadyRaw?_exact step.core_mark_eq with
    ⟨selectedUnmarked, marksEquation, _parents, _components,
      _started, _fired, _selectedMarked⟩
  have different : vertex ≠ step.stackResult.vertex := by
    intro same
    subst vertex
    rw [selectedUnmarked] at marked
    simp at marked
  change step.coreMarked.marks[vertex]? = some (some rawAge)
  rw [marksEquation]
  simpa [Array.getElem?_setIfInBounds, Ne.symm different] using marked

/-- Old continuation credit crosses the common prefix except for the one exact
case in which a raw mate is itself the selected occurrence. Future conclusions
selected by the prefix become marked-conclusion credit. -/
private theorem continuationCredit_or_rawMateSelected
    {certificate : Certificate} {before : ReservationState}
    (step : PreparedStep before) {vertex : Vertex}
    (credit : ContinuationCredit certificate before vertex) :
    ContinuationCredit certificate step.after vertex ∨
      ∃ consumer : ConnectiveBelow certificate vertex,
        before.core.marks[consumer.mate]? = some none ∧
          consumer.mate = step.stackResult.vertex := by
  cases credit with
  | rawMate consumer mateUnmarked =>
      by_cases selected : consumer.mate = step.stackResult.vertex
      · exact Or.inr ⟨consumer, mateUnmarked, selected⟩
      · exact Or.inl (.rawMate consumer
          (step.after_unmarked_of_ne_selected selected mateUnmarked))
  | futureConclusion consumer boundary work =>
      rcases work.afterPrepared_or_selected step with survived | selected
      · exact Or.inl (.futureConclusion consumer boundary survived)
      · left
        apply ContinuationCredit.markedConclusion
          consumer step.stackResult.rawAge
        rcases UnificationState.markReadyRaw?_exact step.core_mark_eq with
          ⟨_selectedUnmarked, _marks, _parents, _components,
            _started, _fired, selectedMarked⟩
        change step.coreMarked.marks[consumer.conclusion]? =
          some (some step.stackResult.rawAge)
        rw [selected]
        exact selectedMarked
  | markedConclusion consumer rawAge marked =>
      exact Or.inl (.markedConclusion consumer rawAge
        (step.after_marked_of_before_marked marked))

end PreparedStep

namespace NopStep

/-- A `nop` step transports continuation credit for an already-marked owner.
The raw-mate-selected residual is impossible: the same submitted par viewed
from the selected occurrence has the marked owner as its mate, contradicting
the exact `nop` guard. -/
theorem continuationCredit
    {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after)
    (structural : certificate.StructurallyWellFormed)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (ownerMarked : before.core.marks[vertex]? = some (some rawAge))
    (credit : ContinuationCredit certificate before vertex) :
    ContinuationCredit certificate after vertex := by
  rcases step.prepared.continuationCredit_or_rawMateSelected credit with
    middleCredit | ⟨consumer, _mateUnmarked, selected⟩
  · rw [step.output_eq]
    exact middleCredit
  · let opposite :=
      connectiveBelowAtMateEq consumer structural selected
    have stepMateEq : step.consumer.mate = vertex := by
      calc
        step.consumer.mate = opposite.mate :=
          connectiveBelow_mate_eq step.consumer opposite
        _ = vertex :=
          connectiveBelowAtMateEq_mate consumer structural selected
    have ownerMarkedMiddle :=
      step.prepared.after_marked_of_before_marked ownerMarked
    have stepMateUnmarked :
        step.prepared.after.core.marks[step.consumer.mate]? = some none := by
      exact step.mate_unmarked
    rw [stepMateEq, ownerMarkedMiddle] at stepMateUnmarked
    simp at stepMateUnmarked

end NopStep

namespace FutureWorkAt

/-- Waiting-destination insertion preserves every pre-existing exact
future-work occurrence. At the destination boundary it becomes a tail member
of the extended payload; every other waiting bucket is unchanged. -/
private theorem afterWaitDestination
    {before after : ReservationState}
    {mateRawAge : RawTokenAge} {conclusion : Vertex}
    (step : WaitDestinationStep before after mateRawAge conclusion)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt before rawAge vertex) :
    FutureWorkAt after rawAge vertex := by
  rcases step.exact with
    ⟨oldPayload, oldInitialized, newInitialized, _marks, _nextAge,
      sigmaEquation, readyEquation, _core, _tags⟩
  cases work with
  | @ready position _ bucket _ sigmaAt readyAt member =>
      apply FutureWorkAt.ready
      · rw [sigmaEquation]
        exact sigmaAt
      · rw [readyEquation]
        exact readyAt
      · exact member
  | @waiting _ payload _ waitingAt member =>
      by_cases sameBoundary : rawAge = step.boundary
      · subst rawAge
        have payloadEquation : payload = oldPayload := by
          have cellsEqual := waitingAt.symm.trans oldInitialized
          simpa using cellsEqual
        subst payload
        exact FutureWorkAt.waiting newInitialized (by simp [member])
      · apply FutureWorkAt.waiting
        · rw [step.output_eq]
          change step.stackAfter.waiting[rawAge]? = _
          exact
            (SequentialStackState.prependWaiting?_of_ne
              step.stack_eq sameBoundary).trans waitingAt
        · exact member

end FutureWorkAt

namespace ContinuationCredit

/-- The destination half of a wait step only extends one waiting payload and
leaves the production core unchanged, so every middle-state credit survives. -/
private theorem afterWaitDestination
    {certificate : Certificate} {before after : ReservationState}
    {mateRawAge : RawTokenAge} {conclusion : Vertex}
    (step : WaitDestinationStep before after mateRawAge conclusion)
    {vertex : Vertex}
    (credit : ContinuationCredit certificate before vertex) :
    ContinuationCredit certificate after vertex := by
  rcases step.exact with
    ⟨_payload, _oldInitialized, _newInitialized, _marks, _nextAge,
      _sigma, _ready, coreEquation, _tags⟩
  cases credit with
  | rawMate consumer mateUnmarked =>
      exact .rawMate consumer (by rw [coreEquation]; exact mateUnmarked)
  | futureConclusion consumer boundary work =>
      exact .futureConclusion consumer boundary
        (work.afterWaitDestination step)
  | markedConclusion consumer rawAge marked =>
      exact .markedConclusion consumer rawAge
        (by rw [coreEquation]; exact marked)

end ContinuationCredit

namespace PreparedStep

/-- A concrete mark after the common prefix is either an unchanged old mark or
the unique mark created on the selected ready head. -/
private theorem after_marked_old_or_selected
    {before : ReservationState} (step : PreparedStep before)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (marked : step.after.core.marks[vertex]? = some (some rawAge)) :
    before.core.marks[vertex]? = some (some rawAge) ∨
      (rawAge = step.stackResult.rawAge ∧
        vertex = step.stackResult.vertex) := by
  rcases UnificationState.markReadyRaw?_exact step.core_mark_eq with
    ⟨_selectedUnmarked, marksEquation, _parents, _components,
      _started, _fired, selectedMarked⟩
  change step.coreMarked.marks[vertex]? = some (some rawAge) at marked
  by_cases same : vertex = step.stackResult.vertex
  · right
    subst vertex
    rw [selectedMarked] at marked
    exact ⟨by simpa using marked.symm, rfl⟩
  · left
    rw [marksEquation] at marked
    simpa [Array.getElem?_setIfInBounds, Ne.symm same] using marked

end PreparedStep
namespace WaitStep

/-- In the sole prepared-prefix failure case, a completed `wait` turns the
selected raw mate's submitted conclusion into exact future waiting work. -/
private theorem continuationCredit_of_rawMateSelected
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (structural : certificate.StructurallyWellFormed)
    {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex)
    (selected : consumer.mate = step.prepared.stackResult.vertex) :
    ContinuationCredit certificate after vertex := by
  let opposite :=
    connectiveBelowAtMateEq consumer structural selected
  have sameConclusion :
      consumer.conclusion = step.consumer.conclusion := by
    calc
      consumer.conclusion = opposite.conclusion :=
        (connectiveBelowAtMateEq_conclusion
          consumer structural selected).symm
      _ = step.consumer.conclusion :=
        connectiveBelow_conclusion_eq opposite step.consumer
  apply ContinuationCredit.futureConclusion
    consumer step.destination.boundary
  rw [sameConclusion]
  rcases step.destination.exact with
    ⟨payload, _beforeCell, afterCell, _marks, _nextAge,
      _sigma, _ready, _core, _tags⟩
  exact FutureWorkAt.waiting afterCell (by simp)

/-- Every old continuation credit crosses a complete wait step. The only
prepared-prefix residual is a raw mate equal to the selected occurrence; the
wait destination upgrades exactly that residual to future-conclusion credit. -/
theorem continuationCredit
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (structural : certificate.StructurallyWellFormed)
    {vertex : Vertex}
    (credit : ContinuationCredit certificate before vertex) :
    ContinuationCredit certificate after vertex := by
  rcases step.prepared.continuationCredit_or_rawMateSelected credit with
    middleCredit | ⟨consumer, _mateUnmarked, selected⟩
  · exact middleCredit.afterWaitDestination step.destination
  · exact step.continuationCredit_of_rawMateSelected
      structural consumer selected

end WaitStep

namespace ConclStep

/-- A `concl` step transports any prior continuation credit.
The raw-mate-selected residual is impossible because the selected occurrence
has an exact conclusion view and therefore cannot also have a consumer. -/
theorem continuationCredit
    {certificate : Certificate} {before after : ReservationState}
    (step : ConclStep certificate before after)
    (structural : certificate.StructurallyWellFormed)
    {vertex : Vertex}
    (credit : ContinuationCredit certificate before vertex) :
    ContinuationCredit certificate after vertex := by
  rcases step.prepared.continuationCredit_or_rawMateSelected credit with
    middleCredit | ⟨consumer, _mateUnmarked, selected⟩
  · rw [step.output_eq]
    exact middleCredit
  · let opposite :=
      connectiveBelowAtMateEq consumer structural selected
    exact False.elim (step.boundary.not_connective opposite)

end ConclStep

namespace NewStep

private def preparedPrefix
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) : PreparedStep before where
  stackResult := step.stackResult
  coreMarked := step.coreMarked
  stack_eq := step.stack_eq
  core_mark_eq := step.core_mark_eq

private def connectiveConsumer
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    ConnectiveBelow certificate step.stackResult.vertex where
  linkIndex := step.tensor.linkIndex
  kind := .tensor
  storedLeft := step.tensor.storedLeft
  storedRight := step.tensor.storedRight
  conclusion := step.tensor.conclusion
  side := step.tensor.side
  consumer_eq := step.tensorValid.1
  link_eq := by
    simpa [SequentialConnectiveKind.asLink] using step.tensorValid.2.1
  wellFormed := by
    simpa [SequentialConnectiveKind.asLink] using step.tensorValid.2.2.1
  premise_eq := step.tensorValid.2.2.2

private theorem after_marks_eq_markedMiddle
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    after.core.marks = step.markedMiddle.core.marks := by
  have afterCore : after.core = step.coreAfter :=
    congrArg ReservationState.core step.output_eq
  rcases certificate.reserveAxiomAt?_exact step.core_reserve_eq with
    ⟨_left, _right, _component, _link, _ready, _lookup, _frontier,
      marksEquation, _parents, _components, _counter, _fired⟩
  rw [afterCore]
  exact marksEquation

end NewStep

namespace FutureWorkAt

private theorem afterNew
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt step.markedMiddle rawAge vertex) :
    FutureWorkAt after rawAge vertex := by
  have afterStack : after.stack = step.stackAfter :=
    congrArg ReservationState.stack step.output_eq
  rcases SequentialStackState.operationalNewEnqueue?_some_iff.mp
      step.stack_enqueue_eq with
    ⟨operation⟩
  rcases operation.ready with
    ⟨_positive, _activeTop, _activeLt, _reachedBound, _partnerBound,
      _distinct, _reachedFresh, _partnerFresh, _reachedUnmarked,
      _partnerUnmarked, activeUndefined, _freshUndefined⟩
  cases work with
  | @ready position _ bucket _ sigmaAt readyAt member =>
      have sigmaPosition :
          position < step.markedMiddle.stack.sigma.length :=
        (List.getElem?_eq_some_iff.mp sigmaAt).1
      have readyPosition :
          position < step.markedMiddle.stack.ready.length :=
        (List.getElem?_eq_some_iff.mp readyAt).1
      apply FutureWorkAt.ready (position := position) (bucket := bucket)
      · rw [afterStack, operation.after_eq]
        change
          (step.markedMiddle.stack.sigma ++
            [step.markedMiddle.stack.nextAge])[position]? = some rawAge
        rw [List.getElem?_append_left sigmaPosition]
        exact sigmaAt
      · rw [afterStack, operation.after_eq]
        change
          (step.markedMiddle.stack.ready ++
            [[step.reached, step.partner]])[position]? = some bucket
        rw [List.getElem?_append_left readyPosition]
        exact readyAt
      · exact member
  | @waiting _ payload _ waitingAt member =>
      by_cases same : rawAge = operation.active
      · subst rawAge
        have activeUndefinedMiddle :
            step.markedMiddle.stack.waiting[operation.active]? =
              some .undefined := by
          exact activeUndefined
        rw [activeUndefinedMiddle] at waitingAt
        simp at waitingAt
      · apply FutureWorkAt.waiting
        · rw [afterStack, operation.after_eq]
          change
            (step.markedMiddle.stack.waiting.setIfInBounds operation.active
              (.initialized []))[rawAge]? = some (.initialized payload)
          rw [Array.getElem?_setIfInBounds_ne (Ne.symm same)]
          exact waitingAt
        · exact member

end FutureWorkAt

namespace NewStep

private theorem continuationCredit_afterPrepared
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) {vertex : Vertex}
    (credit : ContinuationCredit certificate step.markedMiddle vertex) :
    ContinuationCredit certificate after vertex := by
  cases credit with
  | rawMate consumer mateUnmarked =>
      apply ContinuationCredit.rawMate consumer
      rw [step.after_marks_eq_markedMiddle]
      exact mateUnmarked
  | futureConclusion consumer boundary work =>
      exact .futureConclusion consumer boundary (work.afterNew step)
  | markedConclusion consumer rawAge marked =>
      apply ContinuationCredit.markedConclusion consumer rawAge
      rw [step.after_marks_eq_markedMiddle]
      exact marked

/-- A `new` step transports continuation credit for an already-marked owner.
If the old raw mate is selected, exact consumer uniqueness identifies the owner
with the new step's guarded-unmarked tensor mate, contradicting its old mark. -/
theorem continuationCredit
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (structural : certificate.StructurallyWellFormed)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (ownerMarked : before.core.marks[vertex]? = some (some rawAge))
    (credit : ContinuationCredit certificate before vertex) :
    ContinuationCredit certificate after vertex := by
  rcases step.preparedPrefix.continuationCredit_or_rawMateSelected credit with
    middleCredit | ⟨consumer, _mateUnmarked, selected⟩
  · exact step.continuationCredit_afterPrepared middleCredit
  · let opposite :=
      connectiveBelowAtMateEq consumer structural selected
    let submitted := step.connectiveConsumer
    have submittedMate : submitted.mate = vertex := by
      calc
        submitted.mate = opposite.mate :=
          connectiveBelow_mate_eq submitted opposite
        _ = vertex :=
          connectiveBelowAtMateEq_mate consumer structural selected
    have ownerMarkedMiddle :=
      step.preparedPrefix.after_marked_of_before_marked ownerMarked
    have ownerMarkedMiddle' :
        step.markedMiddle.core.marks[vertex]? = some (some rawAge) := by
      exact ownerMarkedMiddle
    have submittedMateUnmarked :
        step.markedMiddle.core.marks[submitted.mate]? = some none := by
      exact step.mate_unmarked
    rw [submittedMate, ownerMarkedMiddle'] at submittedMateUnmarked
    simp at submittedMateUnmarked

end NewStep

namespace ForwardStep

private theorem after_marks_eq_prepared
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) :
    after.core.marks = step.prepared.after.core.marks := by
  have afterCore : after.core = step.coreAfter :=
    congrArg ReservationState.core step.output_eq
  rcases Certificate.queuePar?_exact step.core_queue_eq with
    ⟨_outputToken, _component, _leftFocus, _afterLeft, _rightFocus,
      _context, _tokenGuard, _componentLookup, _leftPick, _rightPick,
      _components, marksEquation, _parents, _started, _fired⟩
  rw [afterCore, marksEquation]
  rfl


end ForwardStep

namespace FutureWorkAt

private theorem afterForward
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt step.prepared.after rawAge vertex) :
    FutureWorkAt after rawAge vertex := by
  have afterStack : after.stack = step.stackAfter :=
    congrArg ReservationState.stack step.output_eq
  have afterSigma :
      after.stack.sigma = step.prepared.after.stack.sigma := by
    calc
      after.stack.sigma = step.stackAfter.sigma :=
        congrArg SequentialStackState.sigma afterStack
      _ = step.prepared.after.stack.sigma := by
        simpa [PreparedStep.after] using
          congrArg SequentialStackState.sigma step.prependStep.after_eq
  have afterWaiting :
      after.stack.waiting = step.prepared.after.stack.waiting := by
    calc
      after.stack.waiting = step.stackAfter.waiting :=
        congrArg SequentialStackState.waiting afterStack
      _ = step.prepared.after.stack.waiting := by
        simpa [PreparedStep.after] using
          congrArg SequentialStackState.waiting step.prependStep.after_eq
  have middleReady :
      step.prepared.after.stack.ready =
        step.prependStep.readyPrefix ++ [step.prependStep.activeReady] := by
    exact step.prependStep.ready_eq
  have afterReady :
      after.stack.ready = step.prependStep.readyPrefix ++
        [step.consumer.conclusion :: step.prependStep.activeReady] := by
    calc
      after.stack.ready = step.stackAfter.ready :=
        congrArg SequentialStackState.ready afterStack
      _ = _ := congrArg SequentialStackState.ready
        step.prependStep.after_eq
  cases work with
  | @ready position _ bucket _ sigmaAt readyAt member =>
      have positionBound :
          position <
            (step.prependStep.readyPrefix ++
              [step.prependStep.activeReady]).length := by
        rw [← middleReady]
        exact (List.getElem?_eq_some_iff.mp readyAt).1
      by_cases inPrefix : position < step.prependStep.readyPrefix.length
      · apply FutureWorkAt.ready (position := position) (bucket := bucket)
        · rw [afterSigma]
          exact sigmaAt
        · rw [afterReady, List.getElem?_append_left inPrefix]
          rw [middleReady, List.getElem?_append_left inPrefix] at readyAt
          exact readyAt
        · exact member
      · have positionTop :
            position = step.prependStep.readyPrefix.length := by
          simp at positionBound
          omega
        subst position
        have bucketEquation : bucket = step.prependStep.activeReady := by
          rw [middleReady] at readyAt
          simp at readyAt
          exact readyAt.symm
        subst bucket
        apply FutureWorkAt.ready
          (position := step.prependStep.readyPrefix.length)
          (bucket := step.consumer.conclusion :: step.prependStep.activeReady)
        · rw [afterSigma]
          exact sigmaAt
        · rw [afterReady]
          simp
        · exact List.mem_cons_of_mem _ member
  | @waiting _ payload _ waitingAt member =>
      apply FutureWorkAt.waiting
      · rw [afterWaiting]
        exact waitingAt
      · exact member

end FutureWorkAt

namespace ForwardStep

private theorem continuationCredit_afterPrepared
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) {vertex : Vertex}
    (credit : ContinuationCredit certificate step.prepared.after vertex) :
    ContinuationCredit certificate after vertex := by
  cases credit with
  | rawMate consumer mateUnmarked =>
      apply ContinuationCredit.rawMate consumer
      rw [step.after_marks_eq_prepared]
      exact mateUnmarked
  | futureConclusion consumer boundary work =>
      exact .futureConclusion consumer boundary (work.afterForward step)
  | markedConclusion consumer rawAge marked =>
      apply ContinuationCredit.markedConclusion consumer rawAge
      rw [step.after_marks_eq_prepared]
      exact marked

private theorem continuationCredit_of_rawMateSelected
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (structural : certificate.StructurallyWellFormed)
    {vertex : Vertex} (consumer : ConnectiveBelow certificate vertex)
    (selected : consumer.mate = step.prepared.stackResult.vertex) :
    ContinuationCredit certificate after vertex := by
  let opposite :=
    connectiveBelowAtMateEq consumer structural selected
  have sameConclusion :
      consumer.conclusion = step.consumer.conclusion := by
    calc
      consumer.conclusion = opposite.conclusion :=
        (connectiveBelowAtMateEq_conclusion
          consumer structural selected).symm
      _ = step.consumer.conclusion :=
        connectiveBelow_conclusion_eq opposite step.consumer
  apply ContinuationCredit.futureConclusion
    consumer step.prepared.stackResult.rawAge
  rw [sameConclusion]
  exact step.createdConclusionFutureWorkAt

/-- A `forward` step transports any prior continuation credit. If the old raw
mate is selected, the branch's inserted conclusion is
the same connective conclusion and upgrades the residual to future work. -/
theorem continuationCredit
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (structural : certificate.StructurallyWellFormed)
    {vertex : Vertex}
    (credit : ContinuationCredit certificate before vertex) :
    ContinuationCredit certificate after vertex := by
  rcases step.prepared.continuationCredit_or_rawMateSelected credit with
    middleCredit | ⟨consumer, _mateUnmarked, selected⟩
  · exact step.continuationCredit_afterPrepared middleCredit
  · exact step.continuationCredit_of_rawMateSelected
      structural consumer selected

end ForwardStep

namespace UnifyPayloadStep

private def selectedConsumer
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    ConnectiveBelow certificate step.prepared.stackResult.vertex where
  linkIndex := step.consumer.linkIndex
  kind := .tensor
  storedLeft := step.consumer.storedLeft
  storedRight := step.consumer.storedRight
  conclusion := step.consumer.conclusion
  side := step.consumer.side
  consumer_eq := Certificate.tensorBelow?_consumer step.consumer_eq
  link_eq := by
    simpa [SequentialConnectiveKind.asLink] using
      Certificate.tensorBelow?_link step.consumer_eq
  wellFormed := by
    simpa [SequentialConnectiveKind.asLink] using
      Certificate.tensorBelow?_wellFormed step.consumer_eq
  premise_eq := Certificate.tensorBelow?_premise step.consumer_eq

private theorem after_marks_eq_prepared
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    after.core.marks = step.prepared.after.core.marks := by
  have afterCore : after.core = step.coreAfter :=
    congrArg ReservationState.core step.output_eq
  have tensorMarks :
      step.coreTensor.marks = step.prepared.coreMarked.marks := by
    rw [step.tensorStep.after_eq]
  have foldMarks : step.coreAfter.marks = step.coreTensor.marks :=
    step.activationFold.marks_eq
  calc
    after.core.marks = step.coreAfter.marks :=
      congrArg UnificationState.marks afterCore
    _ = step.coreTensor.marks := foldMarks
    _ = step.prepared.coreMarked.marks := tensorMarks
    _ = step.prepared.after.core.marks := rfl


end UnifyPayloadStep

namespace FutureWorkAt

private theorem afterUnifyPayload
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt step.prepared.after rawAge vertex) :
    ∃ boundary, FutureWorkAt after boundary vertex := by
  have afterStack : after.stack = step.stackAfter :=
    congrArg ReservationState.stack step.output_eq
  have middleSigma :
      step.prepared.after.stack.sigma = step.mergeStep.sigmaPrefix ++
        [step.previousBoundary, step.mergeStep.activeBoundary] := by
    exact step.mergeStep.sigma_eq
  have middleReady :
      step.prepared.after.stack.ready = step.mergeStep.readyPrefix ++
        [step.mergeStep.previousReady, step.mergeStep.activeReady] := by
    exact step.mergeStep.ready_eq
  have afterSigma :
      after.stack.sigma = step.mergeStep.sigmaPrefix ++
        [step.previousBoundary] := by
    exact (congrArg SequentialStackState.sigma afterStack).trans step.exact.1
  have afterReady :
      after.stack.ready = step.mergeStep.readyPrefix ++
        [step.consumer.conclusion ::
          (step.payload ++ step.mergeStep.previousReady ++
            step.mergeStep.activeReady)] := by
    exact (congrArg SequentialStackState.ready afterStack).trans
      step.exact.2.1
  have afterWaiting :
      after.stack.waiting =
        step.prepared.after.stack.waiting.setIfInBounds
          step.previousBoundary .undefined := by
    have stackWaiting :
        step.stackAfter.waiting =
          step.prepared.stackResult.after.waiting.setIfInBounds
            step.previousBoundary .undefined := step.exact.2.2.1
    calc
      after.stack.waiting = step.stackAfter.waiting :=
        congrArg SequentialStackState.waiting afterStack
      _ = step.prepared.stackResult.after.waiting.setIfInBounds
          step.previousBoundary .undefined := stackWaiting
      _ = step.prepared.after.stack.waiting.setIfInBounds
          step.previousBoundary .undefined := rfl
  have prefixLengths :
      step.mergeStep.sigmaPrefix.length =
        step.mergeStep.readyPrefix.length := by
    have middleInvariant :
        ReservationInvariant certificate step.prepared.after :=
      step.prepared.reservationInvariant step.before_invariant
    have aligned := middleInvariant.stack_wellShaped.ready_aligned
    rw [middleReady, middleSigma] at aligned
    simp at aligned
    omega
  cases work with
  | @ready position _ bucket _ sigmaAt readyAt member =>
      have positionBound :
          position <
            (step.mergeStep.readyPrefix ++
              [step.mergeStep.previousReady,
                step.mergeStep.activeReady]).length := by
        rw [← middleReady]
        exact (List.getElem?_eq_some_iff.mp readyAt).1
      by_cases inPrefix : position < step.mergeStep.readyPrefix.length
      · refine ⟨rawAge, ?_⟩
        apply FutureWorkAt.ready (position := position) (bucket := bucket)
        · have sigmaInPrefix :
              position < step.mergeStep.sigmaPrefix.length := by
            omega
          rw [afterSigma, List.getElem?_append_left sigmaInPrefix]
          rw [middleSigma, List.getElem?_append_left sigmaInPrefix] at sigmaAt
          exact sigmaAt
        · rw [afterReady, List.getElem?_append_left inPrefix]
          rw [middleReady, List.getElem?_append_left inPrefix] at readyAt
          exact readyAt
        · exact member
      · have tailPosition :
            position = step.mergeStep.readyPrefix.length ∨
              position = step.mergeStep.readyPrefix.length + 1 := by
          simp only [List.length_append, List.length_cons,
            List.length_nil] at positionBound
          omega
        rcases tailPosition with previousPosition | activePosition
        · subst position
          have bucketEquation : bucket = step.mergeStep.previousReady := by
            rw [middleReady] at readyAt
            simp at readyAt
            exact readyAt.symm
          subst bucket
          refine ⟨step.previousBoundary, ?_⟩
          apply FutureWorkAt.ready
            (position := step.mergeStep.sigmaPrefix.length)
            (bucket := step.consumer.conclusion ::
              (step.payload ++ step.mergeStep.previousReady ++
                step.mergeStep.activeReady))
          · rw [afterSigma]
            simp
          · rw [afterReady, prefixLengths]
            simp
          · simp [member]
        · subst position
          have bucketEquation : bucket = step.mergeStep.activeReady := by
            rw [middleReady] at readyAt
            simp at readyAt
            exact readyAt.symm
          subst bucket
          refine ⟨step.previousBoundary, ?_⟩
          apply FutureWorkAt.ready
            (position := step.mergeStep.sigmaPrefix.length)
            (bucket := step.consumer.conclusion ::
              (step.payload ++ step.mergeStep.previousReady ++
                step.mergeStep.activeReady))
          · rw [afterSigma]
            simp
          · rw [afterReady, prefixLengths]
            simp
          · simp [member]
  | @waiting _ payload _ waitingAt member =>
      by_cases same : rawAge = step.previousBoundary
      · subst rawAge
        have payloadEquation : payload = step.payload :=
          WaitingCell.initialized.inj
            (Option.some.inj (waitingAt.symm.trans step.waiting_payload))
        subst payload
        refine ⟨step.previousBoundary, ?_⟩
        apply FutureWorkAt.ready
          (position := step.mergeStep.sigmaPrefix.length)
          (bucket := step.consumer.conclusion ::
            (step.payload ++ step.mergeStep.previousReady ++
              step.mergeStep.activeReady))
        · rw [afterSigma]
          simp
        · rw [afterReady, prefixLengths]
          simp
        · simp [member]
      · refine ⟨rawAge, ?_⟩
        apply FutureWorkAt.waiting
        · rw [afterWaiting,
              Array.getElem?_setIfInBounds_ne (Ne.symm same)]
          exact waitingAt
        · exact member

end FutureWorkAt

namespace UnifyPayloadStep

private theorem continuationCredit_afterPrepared
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) {vertex : Vertex}
    (credit : ContinuationCredit certificate step.prepared.after vertex) :
    ContinuationCredit certificate after vertex := by
  cases credit with
  | rawMate consumer mateUnmarked =>
      apply ContinuationCredit.rawMate consumer
      rw [step.after_marks_eq_prepared]
      exact mateUnmarked
  | futureConclusion consumer _boundary work =>
      rcases work.afterUnifyPayload step with ⟨boundary, afterWork⟩
      exact .futureConclusion consumer boundary afterWork
  | markedConclusion consumer rawAge marked =>
      apply ContinuationCredit.markedConclusion consumer rawAge
      rw [step.after_marks_eq_prepared]
      exact marked

private theorem continuationCredit_of_rawMateSelected
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (structural : certificate.StructurallyWellFormed)
    {vertex : Vertex} (consumer : ConnectiveBelow certificate vertex)
    (selected : consumer.mate = step.prepared.stackResult.vertex) :
    ContinuationCredit certificate after vertex := by
  let opposite :=
    connectiveBelowAtMateEq consumer structural selected
  let submitted := step.selectedConsumer
  have sameConclusion :
      consumer.conclusion = submitted.conclusion := by
    calc
      consumer.conclusion = opposite.conclusion :=
        (connectiveBelowAtMateEq_conclusion
          consumer structural selected).symm
      _ = submitted.conclusion :=
        connectiveBelow_conclusion_eq opposite submitted
  apply ContinuationCredit.futureConclusion consumer step.previousBoundary
  rw [sameConclusion]
  exact step.createdConclusionFutureWorkAt

/-- A `unifyPayload` step transports any prior continuation credit. If the old
raw mate is selected, the branch's inserted tensor conclusion
upgrades the residual to future work at the merged previous boundary. -/
theorem continuationCredit
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (structural : certificate.StructurallyWellFormed)
    {vertex : Vertex}
    (credit : ContinuationCredit certificate before vertex) :
    ContinuationCredit certificate after vertex := by
  rcases step.prepared.continuationCredit_or_rawMateSelected credit with
    middleCredit | ⟨consumer, _mateUnmarked, selected⟩
  · exact step.continuationCredit_afterPrepared middleCredit
  · exact step.continuationCredit_of_rawMateSelected
      structural consumer selected

end UnifyPayloadStep

namespace DispatchTagEvidence

/-- Every branch-aligned dispatcher event transports continuation credit owned
by an occurrence that was already concretely marked on input. -/
theorem oldContinuationCredit
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result)
    (structural : certificate.StructurallyWellFormed)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (ownerMarked : before.core.marks[vertex]? = some (some rawAge))
    (credit : ContinuationCredit certificate before vertex) :
    ContinuationCredit certificate result.after vertex := by
  cases evidence with
  | concl step =>
      exact step.continuationCredit structural credit
  | nop step =>
      exact step.continuationCredit structural ownerMarked credit
  | new step =>
      exact step.continuationCredit structural ownerMarked credit
  | wait step =>
      exact step.continuationCredit structural credit
  | forward step =>
      exact step.continuationCredit structural credit
  | unifyPayload step =>
      exact step.continuationCredit structural credit

end DispatchTagEvidence

namespace DispatchTagEvidence

/-- One branch-aligned dispatcher event preserves continuation credit for
every concrete raw-marked non-conclusion in its input state and gives the
fresh selected raw mark its branch-local receipt. -/
theorem markedNonconclusionContinuation
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result)
    (structural : certificate.StructurallyWellFormed)
    (prior : MarkedNonconclusionContinuation certificate before) :
    MarkedNonconclusionContinuation certificate result.after := by
  intro rawAge vertex markedAfter notConclusion
  rcases (evidence.final_rawMarked_iff_old_or_event).mp markedAfter with
    oldMarked | event
  · exact evidence.oldContinuationCredit structural oldMarked
      (prior oldMarked notConclusion)
  · exact evidence.newlyMarkedContinuationCredit event notConclusion

end DispatchTagEvidence

namespace CanonicalTagHistory

/-- Every exact canonical dispatcher history carries continuation credit for
all concrete raw-marked non-conclusions in its final state. This is induction
over supplied execution evidence, not an existence or progress theorem. -/
theorem markedNonconclusionContinuation
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history) :
    MarkedNonconclusionContinuation certificate state := by
  induction tagHistory with
  | empty =>
      exact empty_markedNonconclusionContinuation certificate
  | init step =>
      exact
        SequentialFigure7.InitialReservationStep.markedNonconclusionContinuation
          step
  | @later before result history invariant dispatch prior evidence induction =>
      exact evidence.markedNonconclusionContinuation invariant.structural induction

end CanonicalTagHistory

end SequentialFigure7
end ProofNetIR
