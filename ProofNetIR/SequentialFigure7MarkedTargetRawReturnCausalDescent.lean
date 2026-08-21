/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnFirstDescent
import ProofNetIR.SequentialFigure7RawMarkCausalOrder

/-!
# Figure-7 marked-target raw-return causal descent

The first representative descent exposed by an exact Wait raw return is also
causally ordered.  The active origin and the first connective's opposite
premise were authentically raw-marked before the strictly older parent
conclusion.  The opposite premise is non-global and therefore has its own
finite continuation exit from canonical continuation-credit preservation.

The generic target adapter and typed Wait theorem replace the prior first-step
descent alternative by this stronger causal receipt.  They retain every other
exit and every outer commitment-interval outcome.

This checkpoint does not eliminate the causal descent or its sibling exit,
derive a ready-tail witness or history-tail law, establish event-order
transitivity, or prove completion or progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

private theorem connectiveMateMembership
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    consumer.mate ∈ consumer.submittedLink.premises := by
  cases kindEq : consumer.kind <;> cases sideEq : consumer.side <;>
    simp [ConnectiveBelow.mate, ConnectiveBelow.submittedLink,
      SequentialConnectiveKind.asLink, Link.premises,
      TensorPremiseSide.mate, kindEq, sideEq]

/-- An authenticated first representative descent together with the strict
raw-mark-event order of both premises and a finite continuation exit for the
opposite premise. -/
def MarkedConclusionChainFirstCausalDescent
    (certificate : Certificate) (state : ReservationState)
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (origin terminal : Vertex) (active : RawTokenAge) : Prop :=
  ∃ (originAge : RawTokenAge) (consumer : ConnectiveBelow certificate origin)
      (conclusionAge mateAge : RawTokenAge),
    state.core.marks[origin]? = some (some originAge) ∧
      state.core.representative originAge = active ∧
      state.core.marks[consumer.conclusion]? = some (some conclusionAge) ∧
      tagHistory.RawMarked conclusionAge consumer.conclusion ∧
      consumer.conclusion ∉ certificate.conclusions ∧
      state.core.representative conclusionAge < active ∧
      tagHistory.RawMarkedBefore originAge origin
        conclusionAge consumer.conclusion ∧
      tagHistory.RawMarkedBefore mateAge consumer.mate
        conclusionAge consumer.conclusion ∧
      ContinuationExit certificate state consumer.mate ∧
      MarkedConclusionChain certificate state consumer.conclusion terminal

namespace MarkedConclusionChainFirstRepresentativeDescent

/-- Enrich an authenticated first representative descent with strict causal
raw-mark order for both premises and a finite exit for the opposite premise. -/
theorem causalDescent
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin terminal : Vertex} {active : RawTokenAge}
    (invariant : SchedulerInvariant certificate state)
    (descent :
      MarkedConclusionChainFirstRepresentativeDescent certificate state
        tagHistory origin terminal active) :
    MarkedConclusionChainFirstCausalDescent certificate state tagHistory
      origin terminal active := by
  rcases descent with
    ⟨originAge, consumer, conclusionAge, originMarked,
      originRepresentative, conclusionMarked, conclusionEvent,
      conclusionNotGlobal, conclusionOlder, tail⟩
  rcases tagHistory.rawMarkedPremisesBefore consumer conclusionEvent with
    ⟨premiseAge, mateAge, premiseBefore, mateBefore⟩
  have premiseMarked :
      state.core.marks[origin]? = some (some premiseAge) :=
    tagHistory.final_rawMarked_iff.mpr premiseBefore.first_rawMarked
  have premiseAgeEq : originAge = premiseAge :=
    Option.some.inj (Option.some.inj (originMarked.symm.trans premiseMarked))
  subst premiseAge
  have mateMarked :
      state.core.marks[consumer.mate]? = some (some mateAge) :=
    tagHistory.final_rawMarked_iff.mpr mateBefore.first_rawMarked
  have mateNotGlobal : consumer.mate ∉ certificate.conclusions :=
    submittedPremise_not_conclusion invariant.structural consumer.link_eq
      (connectiveMateMembership consumer)
  have continuation : MarkedNonconclusionContinuation certificate state :=
    tagHistory.markedNonconclusionContinuation
  have mateExit : ContinuationExit certificate state consumer.mate :=
    continuation.continuationExit mateMarked mateNotGlobal
  exact ⟨originAge, consumer, conclusionAge, mateAge, originMarked,
    originRepresentative, conclusionMarked, conclusionEvent,
    conclusionNotGlobal, conclusionOlder, premiseBefore, mateBefore, mateExit,
    tail⟩

end MarkedConclusionChainFirstRepresentativeDescent

/-- The marked re-entry target after replacing the first representative
descent by its causally ordered two-premise receipt. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCausalDescentTarget
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
      ∃ targetConsumer : ConnectiveBelow certificate directed.target,
        targetConsumer.mate ≠ input.vertex ∧
        directed.source = targetConsumer.conclusion ∧
        targetConsumer.conclusion ∉ owned ∧
        ((∃ terminal,
            MarkedConclusionChain certificate state directed.target terminal ∧
            ∃ terminalConsumer : ConnectiveBelow certificate terminal,
              state.core.marks[terminalConsumer.mate]? = some none ∧
              terminalConsumer.mate ∉ owned) ∨
          MarkedConclusionChainFirstCausalDescent certificate state
            tagHistory directed.target current.mate input.rawAge ∨
          (∃ terminal,
            MarkedConclusionChain certificate state directed.target terminal ∧
            ∃ terminalConsumer : ConnectiveBelow certificate terminal,
              ∃ boundary,
                FutureWorkAt state boundary terminalConsumer.conclusion ∧
                terminalConsumer.conclusion ∉ owned ∧
                boundary < input.rawAge) ∨
          ∃ terminal,
            MarkedConclusionChain certificate state directed.target terminal ∧
            ∃ terminalConsumer : ConnectiveBelow certificate terminal,
              ∃ conclusionAge,
                state.core.marks[terminalConsumer.conclusion]? =
                  some (some conclusionAge) ∧
                terminalConsumer.conclusion ∈ certificate.conclusions ∧
                terminalConsumer.conclusion ∉ owned ∧
                state.core.representative conclusionAge < input.rawAge)

namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationFirstDescentTarget

/-- Replace the first-descent alternative in a generic re-entry target by its
strict causal two-premise refinement. -/
theorem causalDescentTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationFirstDescentTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCausalDescentTarget
      tagHistory input component owned current := by
  rcases target with
    ⟨path, directed, markedAge, pathStart, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetNeMate, targetMarked, authentic,
      representativeEq, targetConsumer, targetConsumerMateNeSelected,
      sourceConsumer, targetConclusionOutside, status⟩
  refine ⟨path, directed, markedAge, pathStart, finishOwned,
    directedMembership, parentEdge, targetNeSelected, targetNeMate,
    targetMarked, authentic, representativeEq, targetConsumer,
    targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside, ?_⟩
  rcases status with raw | descent | future | marked
  · exact Or.inl raw
  · exact Or.inr (Or.inl (descent.causalDescent invariant))
  · exact Or.inr (Or.inr (Or.inl future))
  · exact Or.inr (Or.inr (Or.inr marked))

end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationFirstDescentTarget

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

/-- In the strictly older Wait branch, replace exact raw return by a first
descent whose two premises strictly precede the older parent conclusion in the
canonical raw-mark event order. -/
theorem WaitStep.commitmentInterval_parTraceReentryMarkedContinuationCausalDescentOutcome
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
          ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCausalDescentTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply
    (step.commitmentInterval_parTraceReentryMarkedContinuationFirstDescentOutcome
      connected tagHistory invariant componentLookup occurrence positive firstAt
      lastAt noTail).mapOlderMateStatus
  intro status
  rcases status with ⟨mateOutside, mateMarked, representativeOlder, target⟩
  exact ⟨mateOutside, mateMarked, representativeOlder,
    target.causalDescentTarget step.prepared.readyHeadInput invariant⟩

end SequentialFigure7
end ProofNetIR
