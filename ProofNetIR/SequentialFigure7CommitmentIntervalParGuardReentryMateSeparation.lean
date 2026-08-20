/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParGuardReentryFailure

/-!
# Figure-7 commitment-interval par-guard re-entry mate separation

A retained simple re-entry path cannot revisit its external starting mate. If
the marked re-entry target's own connective view had the current selected head
as its mate, structural parent uniqueness would swap the two exact connective
views and identify that target with the path start. This contradiction removes
the selected raw-sibling alternative for the exact marked target.

The avoiding and equal-final selected/mate interval branches remain. The new
carrier does not eliminate the marked target, choose its parent source kind,
derive a ready-tail witness or the history-tail law, or prove progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

private theorem edgeSimplePath_target_ne_start_of_mem
    {graph : Graph} (path : graph.EdgeSimplePath)
    {directed : graph.DirectedEdge}
    (membership : directed ∈ path.traversed) :
    directed.target ≠ path.start := by
  intro same
  apply path.start_not_mem_vertices_tail
  change path.start ∈ path.traversed.map Graph.DirectedEdge.target
  rw [← same]
  exact List.mem_map.mpr ⟨directed, membership, rfl⟩

/-- A marked external re-entry target whose exact target is separated from the
current mate. Every connective view rooted at that target also has a mate
different from the current selected head. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex)
    (current : ConnectiveBelow certificate input.vertex) : Prop :=
  ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
      (directed : certificate.referenceSwitchingGraph.DirectedEdge)
      (markedAge : RawTokenAge),
    path.start = current.mate ∧
      path.finish ∈ owned ∧
      directed ∈ path.traversed ∧
      ActiveCarrierInboundParentEdge certificate component owned directed ∧
      directed.target ≠ input.vertex ∧
      directed.target ≠ current.mate ∧
      state.core.marks[directed.target]? = some (some markedAge) ∧
      tagHistory.RawMarked markedAge directed.target ∧
      state.core.representative markedAge = input.rawAge ∧
      ∀ targetConsumer : ConnectiveBelow certificate directed.target,
        targetConsumer.mate ≠ input.vertex

private theorem connectiveMateMembership
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    consumer.mate ∈ consumer.submittedLink.premises := by
  cases kindEq : consumer.kind <;> cases sideEq : consumer.side <;>
    simp [ConnectiveBelow.mate, ConnectiveBelow.submittedLink,
      SequentialConnectiveKind.asLink, Link.premises,
      TensorPremiseSide.mate, kindEq, sideEq]

private theorem connectiveBelow_mate_eq_of_mate_eq
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {leftVertex rightVertex : Vertex}
    (left : ConnectiveBelow certificate leftVertex)
    (right : ConnectiveBelow certificate rightVertex)
    (leftMate : left.mate = rightVertex) :
    right.mate = leftVertex := by
  have mateIndex :
      certificate.consumerIndex.uniqueConsumer? left.mate =
        some left.linkIndex := by
    simpa [Certificate.consumerIndex] using
      ConsumerIndex.build_uniqueConsumer?_eq_some structural left.link_eq
        left.mate_bound (connectiveMateMembership left)
  have rightIndex :
      certificate.consumerIndex.uniqueConsumer? rightVertex =
        some left.linkIndex := by
    simpa [leftMate] using mateIndex
  have sameIndex : right.linkIndex = left.linkIndex :=
    Option.some.inj (right.consumer_eq.symm.trans rightIndex)
  have rightLookup := right.link_eq
  rw [sameIndex] at rightLookup
  have sameLink :
      right.kind.asLink right.storedLeft right.storedRight right.conclusion =
        left.kind.asLink left.storedLeft left.storedRight left.conclusion :=
    Option.some.inj (rightLookup.symm.trans left.link_eq)
  have leftPremise := left.premise_eq
  have rightPremise := right.premise_eq
  cases leftKind : left.kind <;> cases rightKind : right.kind <;>
    cases leftSide : left.side <;> cases rightSide : right.side <;>
      simp_all [SequentialConnectiveKind.asLink, ConnectiveBelow.mate,
        TensorPremiseSide.mate, TensorPremiseSide.premise]

/-- A marked target reached from the current mate by a retained simple path is
mate-separated: it is not the current mate, and its own opposite premise is
not the current selected head. -/
theorem ActiveCarrierExternalReentryMarkedHistoricalTarget.mateSeparated
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    (structural : certificate.StructurallyWellFormed)
    (current : ConnectiveBelow certificate input.vertex)
    (target :
      ActiveCarrierExternalReentryMarkedHistoricalTarget tagHistory input
        component owned current.mate) :
    ActiveCarrierExternalReentryMarkedMateSeparatedTarget tagHistory input
      component owned current := by
  rcases target with
    ⟨path, directed, markedAge, pathStarts, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetMarked, authentic,
      representativeEq⟩
  have targetNeStart := edgeSimplePath_target_ne_start_of_mem path
    directedMembership
  have targetNeMate : directed.target ≠ current.mate := by
    intro same
    apply targetNeStart
    exact same.trans pathStarts.symm
  have targetConsumerMateNeSelected :
      ∀ targetConsumer : ConnectiveBelow certificate directed.target,
        targetConsumer.mate ≠ input.vertex := by
    intro targetConsumer same
    have currentMateEq : current.mate = directed.target :=
      connectiveBelow_mate_eq_of_mate_eq structural targetConsumer current same
    exact targetNeMate currentMateEq.symm
  exact ⟨path, directed, markedAge, pathStarts, finishOwned,
    directedMembership, parentEdge, targetNeSelected, targetNeMate,
    targetMarked, authentic, representativeEq, targetConsumerMateNeSelected⟩

namespace CanonicalTagHistory

private theorem CommitmentIntervalParTraceOutcome.mapOlderMateStatus
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state}
    {consumer : ConnectiveBelow certificate input.vertex}
    {position edgeCount : Nat} {first : RawTokenAge}
    {beforeStatus afterStatus : Prop}
    (outcome : tagHistory.CommitmentIntervalParTraceOutcome input consumer
      position edgeCount first beforeStatus)
    (mapStatus : beforeStatus → afterStatus) :
    tagHistory.CommitmentIntervalParTraceOutcome input consumer position
      edgeCount first afterStatus := by
  cases outcome with
  | avoiding path => exact .avoiding path
  | equalSelected offset parent child event offsetLt parentAt childAt
      notAvoiding membership eventAge childEq side beforeTrace afterTrace trace =>
      exact .equalSelected offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childEq side beforeTrace afterTrace trace
  | equalMate offset parent child event offsetLt parentAt childAt notAvoiding
      membership eventAge childEq side beforeTrace afterTrace trace =>
      exact .equalMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childEq side beforeTrace afterTrace trace
  | olderMate offset parent child event offsetLt parentAt childAt notAvoiding
      membership eventAge childLt side beforeTrace afterTrace trace status =>
      exact .olderMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childLt side beforeTrace afterTrace trace
        (mapStatus status)

end CanonicalTagHistory

/-- In the strictly older Nop branch, exact ready-tail failure leaves a marked
re-entry target separated from both the current mate and the current selected
head through every target connective view. -/
theorem NopStep.commitmentInterval_parTraceReentryMateSeparatedOutcome
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (connected : certificate.ReferenceSwitchingConnected)
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (step : NopStep certificate before after)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      before.core.components[step.prepared.stackResult.rawAge]? =
        some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {position edgeCount : Nat} {first : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : before.stack.sigma[position]? = some first)
    (lastAt :
      before.stack.sigma[position + edgeCount]? =
        some step.prepared.stackResult.rawAge)
    (noTail :
      ¬ ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) :
    tagHistory.CommitmentIntervalParTraceOutcome
      step.prepared.readyHeadInput step.consumer position edgeCount first
        (step.consumer.mate ∉ owned ∧
          before.core.marks[step.consumer.mate]? = some none ∧
          ActiveCarrierExternalReentryMarkedMateSeparatedTarget tagHistory
            step.prepared.readyHeadInput component owned step.consumer) := by
  apply (step.commitmentInterval_parTraceReentryMarkedOutcome connected
    tagHistory invariant componentLookup occurrence positive firstAt lastAt
    noTail).mapOlderMateStatus
  intro status
  rcases status with ⟨mateOutside, mateUnmarked, target⟩
  exact ⟨mateOutside, mateUnmarked,
    ActiveCarrierExternalReentryMarkedHistoricalTarget.mateSeparated
      (tagHistory := tagHistory) (input := step.prepared.readyHeadInput)
      (component := component) (owned := owned) invariant.structural
      step.consumer target⟩

/-- In the strictly older Wait branch, exact ready-tail failure leaves a marked
re-entry target separated from both the current mate and the current selected
head through every target connective view. -/
theorem WaitStep.commitmentInterval_parTraceReentryMateSeparatedOutcome
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (connected : certificate.ReferenceSwitchingConnected)
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (step : WaitStep certificate before after)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      before.core.components[step.prepared.stackResult.rawAge]? =
        some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {position edgeCount : Nat} {first : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : before.stack.sigma[position]? = some first)
    (lastAt :
      before.stack.sigma[position + edgeCount]? =
        some step.prepared.stackResult.rawAge)
    (noTail :
      ¬ ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) :
    tagHistory.CommitmentIntervalParTraceOutcome
      step.prepared.readyHeadInput step.consumer position edgeCount first
        (step.consumer.mate ∉ owned ∧
          before.core.marks[step.consumer.mate]? =
            some (some step.mateRawAge) ∧
          before.core.representative step.mateRawAge <
            step.prepared.stackResult.rawAge ∧
          ActiveCarrierExternalReentryMarkedMateSeparatedTarget tagHistory
            step.prepared.readyHeadInput component owned step.consumer) := by
  apply (step.commitmentInterval_parTraceReentryMarkedOutcome connected
    tagHistory invariant componentLookup occurrence positive firstAt lastAt
    noTail).mapOlderMateStatus
  intro status
  rcases status with
    ⟨mateOutside, mateMarked, representativeOlder, target⟩
  exact ⟨mateOutside, mateMarked, representativeOlder,
    ActiveCarrierExternalReentryMarkedHistoricalTarget.mateSeparated
      (tagHistory := tagHistory) (input := step.prepared.readyHeadInput)
      (component := component) (owned := owned) invariant.structural
      step.consumer target⟩

end SequentialFigure7
end ProofNetIR
