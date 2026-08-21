/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnTerminalCausalOrder

/-!
# Figure-7 raw-mark sibling-exit causal order

Authentic raw-mark events at distinct vertices are strictly comparable in one
canonical history. This orders a marked-global endpoint of the first descent's
sibling continuation against the authenticated outer-mate terminal. Raw and
future sibling exits remain unchanged.

This is an exact causal classification. It does not eliminate an endpoint,
derive a ready-tail witness or history-tail law, or prove completion or
progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

namespace CanonicalTagHistory.RawMarkedBefore

/-- Authentic raw marks at distinct vertices are strictly comparable in their
canonical event order. -/
theorem total_of_vertex_ne
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {firstAge secondAge : RawTokenAge} {first second : Vertex}
    (firstEvent : tagHistory.RawMarked firstAge first)
    (secondEvent : tagHistory.RawMarked secondAge second)
    (different : first ≠ second) :
    tagHistory.RawMarkedBefore firstAge first secondAge second ∨
      tagHistory.RawMarkedBefore secondAge second firstAge first := by
  induction tagHistory with
  | empty => exact False.elim firstEvent
  | init step => exact False.elim firstEvent
  | later prior evidence induction =>
      rcases firstEvent with firstOld | firstCurrent
      · rcases secondEvent with secondOld | secondCurrent
        · rcases induction firstOld secondOld with before | after
          · exact Or.inl (.prior before)
          · exact Or.inr (.prior after)
        · exact Or.inl (.current firstOld secondCurrent)
      · rcases secondEvent with secondOld | secondCurrent
        · exact Or.inr (.current secondOld firstCurrent)
        · exact False.elim (different (firstCurrent.2.trans secondCurrent.2.symm))

/-- Two authentic raw marks are the same age/vertex event or occur in one of
the two strict chronological orders. -/
theorem eq_or_before_or_after
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {firstAge secondAge : RawTokenAge} {first second : Vertex}
    (firstEvent : tagHistory.RawMarked firstAge first)
    (secondEvent : tagHistory.RawMarked secondAge second) :
    (firstAge = secondAge ∧ first = second) ∨
      tagHistory.RawMarkedBefore firstAge first secondAge second ∨
        tagHistory.RawMarkedBefore secondAge second firstAge first := by
  by_cases same : first = second
  · subst second
    have firstMarked := tagHistory.final_rawMarked_iff.mpr firstEvent
    have secondMarked := tagHistory.final_rawMarked_iff.mpr secondEvent
    have nestedEq : some (some firstAge) = some (some secondAge) :=
      firstMarked.symm.trans secondMarked
    have ageEq : firstAge = secondAge :=
      Option.some.inj (Option.some.inj nestedEq)
    exact Or.inl ⟨ageEq, rfl⟩
  · exact Or.inr (total_of_vertex_ne firstEvent secondEvent same)

end CanonicalTagHistory.RawMarkedBefore

/-- A sibling continuation exit whose marked-global endpoint is strictly
ordered against an authenticated outer terminal. -/
inductive ContinuationExitOuterTerminalCausalOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (origin outer : Vertex) (outerAge : RawTokenAge) : Prop where
  | rawMate {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none) :
      ContinuationExitOuterTerminalCausalOutcome tagHistory origin outer
        outerAge
  | futureConclusion {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (consumer : ConnectiveBelow certificate terminal)
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion) :
      ContinuationExitOuterTerminalCausalOutcome tagHistory origin outer
        outerAge
  | markedGlobalBefore {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (consumer : ConnectiveBelow certificate terminal)
      (conclusionAge : RawTokenAge)
      (marked :
        state.core.marks[consumer.conclusion]? = some (some conclusionAge))
      (global : consumer.conclusion ∈ certificate.conclusions)
      (before : tagHistory.RawMarkedBefore conclusionAge consumer.conclusion
        outerAge outer) :
      ContinuationExitOuterTerminalCausalOutcome tagHistory origin outer
        outerAge
  | markedGlobalAfter {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (consumer : ConnectiveBelow certificate terminal)
      (conclusionAge : RawTokenAge)
      (marked :
        state.core.marks[consumer.conclusion]? = some (some conclusionAge))
      (global : consumer.conclusion ∈ certificate.conclusions)
      (before : tagHistory.RawMarkedBefore outerAge outer conclusionAge
        consumer.conclusion) :
      ContinuationExitOuterTerminalCausalOutcome tagHistory origin outer
        outerAge

/-- Normalize a continuation exit relative to a distinct authenticated
non-global outer terminal. -/
theorem ContinuationExit.outerTerminalCausalOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin outer : Vertex} {outerAge : RawTokenAge}
    (exit : ContinuationExit certificate state origin)
    (outerEvent : tagHistory.RawMarked outerAge outer)
    (outerNotGlobal : outer ∉ certificate.conclusions) :
    ContinuationExitOuterTerminalCausalOutcome tagHistory origin outer
      outerAge := by
  cases exit with
  | rawMate chain consumer mateUnmarked =>
      exact .rawMate chain consumer mateUnmarked
  | futureConclusion chain consumer boundary work =>
      exact .futureConclusion chain consumer boundary work
  | markedGlobalConclusion chain consumer conclusionAge marked global =>
    have conclusionEvent :
        tagHistory.RawMarked conclusionAge consumer.conclusion :=
      tagHistory.final_rawMarked_iff.mp marked
    have different : consumer.conclusion ≠ outer := by
      intro same
      subst outer
      exact outerNotGlobal global
    rcases CanonicalTagHistory.RawMarkedBefore.total_of_vertex_ne
        conclusionEvent outerEvent different with before | after
    · exact .markedGlobalBefore chain consumer conclusionAge marked global
        before
    · exact .markedGlobalAfter chain consumer conclusionAge marked global after

/-- The first descent's sibling receipt is ordered and classified against an
authenticated non-global outer terminal. -/
theorem MarkedConclusionChainFirstCausalDescent.siblingExitOuterTerminalCausalOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin outer : Vertex} {active outerAge : RawTokenAge}
    (descent : MarkedConclusionChainFirstCausalDescent certificate state
      tagHistory origin outer active)
    (outerEvent : tagHistory.RawMarked outerAge outer)
    (outerNotGlobal : outer ∉ certificate.conclusions) :
    ∃ (consumer : ConnectiveBelow certificate origin) (mateAge : RawTokenAge),
      tagHistory.RawMarkedBefore mateAge consumer.mate outerAge outer ∧
        ContinuationExitOuterTerminalCausalOutcome tagHistory consumer.mate
          outer outerAge := by
  rcases descent with
    ⟨originAge, consumer, conclusionAge, mateAge, originMarked,
      originRepresentative, conclusionMarked, conclusionEvent,
      conclusionNotGlobal, conclusionOlder, originBefore, mateBefore, mateExit,
      tail⟩
  have mateBeforeOuter :
      tagHistory.RawMarkedBefore mateAge consumer.mate outerAge outer := by
    rcases MarkedConclusionChain.rawMarkedBefore_or_eq tagHistory tail
        outerEvent with same | ⟨tailAge, conclusionBeforeOuter⟩
    · subst outer
      have ageEq : conclusionAge = outerAge := by
        have conclusionMarkedAt := tagHistory.final_rawMarked_iff.mpr
          conclusionEvent
        have outerMarkedAt := tagHistory.final_rawMarked_iff.mpr outerEvent
        exact Option.some.inj
          (Option.some.inj (conclusionMarkedAt.symm.trans outerMarkedAt))
      subst outerAge
      exact mateBefore
    · have ageEq : tailAge = conclusionAge := by
        have tailMarkedAt := tagHistory.final_rawMarked_iff.mpr
          conclusionBeforeOuter.first_rawMarked
        have conclusionMarkedAt := tagHistory.final_rawMarked_iff.mpr
          conclusionEvent
        exact Option.some.inj
          (Option.some.inj (tailMarkedAt.symm.trans conclusionMarkedAt))
      subst tailAge
      exact CanonicalTagHistory.RawMarkedBefore.trans mateBefore
        conclusionBeforeOuter
  exact ⟨consumer, mateAge, mateBeforeOuter,
    mateExit.outerTerminalCausalOutcome outerEvent outerNotGlobal⟩

private theorem connectiveMateMembership
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    consumer.mate ∈ consumer.submittedLink.premises := by
  rcases consumer with
    ⟨linkIndex, kind, storedLeft, storedRight, conclusion, side,
      consumerEq, linkEq, wellFormed, premiseEq⟩
  cases kind <;> cases side <;>
    simp [ConnectiveBelow.submittedLink, ConnectiveBelow.mate,
      SequentialConnectiveKind.asLink, TensorPremiseSide.mate, Link.premises]

/-- A terminal-causal re-entry target whose first-descent sibling exit has
been classified against the authenticated outer terminal. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex)
    (current : ConnectiveBelow certificate input.vertex) : Prop :=
  ∃ (outerAge : RawTokenAge),
    tagHistory.RawMarked outerAge current.mate ∧
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
              (MarkedConclusionChainFirstCausalDescent certificate state
                  tagHistory directed.target current.mate input.rawAge ∧
                ∃ (consumer : ConnectiveBelow certificate directed.target)
                    (mateAge : RawTokenAge),
                  tagHistory.RawMarkedBefore mateAge consumer.mate outerAge
                      current.mate ∧
                    ContinuationExitOuterTerminalCausalOutcome tagHistory
                      consumer.mate current.mate outerAge) ∨
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

namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationTerminalCausalTarget

/-- Refine the first-descent branch by ordering the sibling's marked-global
exit against the authenticated outer terminal. -/
theorem siblingExitCausalTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (structural : certificate.StructurallyWellFormed)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationTerminalCausalTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalTarget
      tagHistory input component owned current := by
  rcases target with
    ⟨outerAge, outerEvent, path, directed, markedAge, pathStart, finishOwned,
      directedMembership, parentEdge, targetNeSelected, targetNeMate,
      targetMarked, targetEvent, representativeEq, targetConsumer,
      targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside,
      status⟩
  refine ⟨outerAge, outerEvent, path, directed, markedAge, pathStart,
    finishOwned, directedMembership, parentEdge, targetNeSelected, targetNeMate,
    targetMarked, targetEvent, representativeEq, targetConsumer,
    targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside, ?_⟩
  rcases status with raw | descent | future | marked
  · exact Or.inl raw
  · have outerNotGlobal : current.mate ∉ certificate.conclusions :=
      submittedPremise_not_conclusion structural current.link_eq
        (connectiveMateMembership current)
    exact Or.inr (Or.inl ⟨descent,
      descent.siblingExitOuterTerminalCausalOutcome outerEvent outerNotGlobal⟩)
  · exact Or.inr (Or.inr (Or.inl future))
  · exact Or.inr (Or.inr (Or.inr marked))

end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationTerminalCausalTarget

namespace CanonicalTagHistory

private theorem CommitmentIntervalParTraceOutcome.mapSiblingStatus
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

open ActiveCarrierExternalReentryMarkedMateSeparatedContinuationTerminalCausalTarget

/-- In the strictly older Wait branch, classify the first-descent sibling's
marked-global exit against the authenticated outer mate. -/
theorem WaitStep.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalOutcome
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
          ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply CanonicalTagHistory.CommitmentIntervalParTraceOutcome.mapSiblingStatus
    (step.commitmentInterval_parTraceReentryMarkedContinuationTerminalCausalOutcome
      connected tagHistory invariant componentLookup occurrence positive firstAt
      lastAt noTail)
  intro status
  rcases status with ⟨mateOutside, mateMarked, representativeOlder, target⟩
  exact ⟨mateOutside, mateMarked, representativeOlder,
    siblingExitCausalTarget invariant.structural target⟩

end SequentialFigure7
end ProofNetIR
