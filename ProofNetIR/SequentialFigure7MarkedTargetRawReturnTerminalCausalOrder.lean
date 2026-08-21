/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnCausalDescent

/-!
# Figure-7 raw-mark terminal causal order

Strict canonical raw-mark order is transitive and asymmetric. A finite marked
conclusion chain therefore places a distinct origin before any authenticated
terminal raw-mark event.

For an authenticated first causal descent, both its origin and the first
connective's opposite premise precede the chain terminal. The target adapter
authenticates the outer mate; in the causal-descent alternative it is that
terminal event. The typed Wait theorem propagates the receipt through every
retained commitment-interval outcome.

This checkpoint orders the remaining descent through its full marked chain.
It does not eliminate the descent or sibling continuation exit, derive a
ready-tail witness or history-tail law, or prove completion or progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

private def rawMarkEventCount
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state} :
    CanonicalTagHistory certificate history → Nat
  | .empty => 0
  | .init _step => 0
  | .later prior _evidence => rawMarkEventCount prior + 1

private def RawMarkedAt
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (position : Nat) (rawAge : RawTokenAge) (vertex : Vertex) : Prop :=
  match tagHistory with
  | .empty => False
  | .init _step => False
  | .later prior evidence =>
      RawMarkedAt prior position rawAge vertex ∨
        position = rawMarkEventCount prior ∧
          evidence.RawMarked rawAge vertex

private theorem DispatchTagEvidence.RawMarked.not_prior
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    {history : ExecutedHistory certificate before}
    {tagHistory : CanonicalTagHistory certificate history}
    {evidence : DispatchTagEvidence certificate before result}
    {priorAge currentAge : RawTokenAge} {vertex : Vertex}
    (current : evidence.RawMarked currentAge vertex)
    (prior : tagHistory.RawMarked priorAge vertex) : False := by
  have oldMarked :
      before.core.marks[vertex]? = some (some priorAge) :=
    tagHistory.final_rawMarked_iff.mpr prior
  rcases UnificationState.markReadyRaw?_exact
      evidence.prepared.core_mark_eq with
    ⟨selectedUnmarked, _marksEq, _parents, _components, _started,
      _fired, _selectedMarked⟩
  rw [current.2, selectedUnmarked] at oldMarked
  simp at oldMarked

private theorem rawMarkedAt_rawMarked
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {position : Nat} {rawAge : RawTokenAge} {vertex : Vertex}
    (occurs : RawMarkedAt tagHistory position rawAge vertex) :
    tagHistory.RawMarked rawAge vertex := by
  induction tagHistory with
  | empty => exact False.elim occurs
  | init step => exact False.elim occurs
  | later prior evidence induction =>
      rcases occurs with old | current
      · exact Or.inl (induction old)
      · exact Or.inr current.2

private theorem rawMarkedAt_position_lt
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {position : Nat} {rawAge : RawTokenAge} {vertex : Vertex}
    (occurs : RawMarkedAt tagHistory position rawAge vertex) :
    position < rawMarkEventCount tagHistory := by
  induction tagHistory with
  | empty => exact False.elim occurs
  | init step => exact False.elim occurs
  | later prior evidence induction =>
      rcases occurs with old | current
      · simpa [rawMarkEventCount] using Nat.lt_succ_of_lt (induction old)
      · simp [rawMarkEventCount, current.1]

private theorem rawMarkedAt_position_eq
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {firstPosition secondPosition : Nat}
    {firstAge secondAge : RawTokenAge} {vertex : Vertex}
    (first : RawMarkedAt tagHistory firstPosition firstAge vertex)
    (second : RawMarkedAt tagHistory secondPosition secondAge vertex) :
    firstPosition = secondPosition := by
  induction tagHistory with
  | empty => exact False.elim first
  | init step => exact False.elim first
  | later prior evidence induction =>
      rcases first with firstOld | firstCurrent
      · rcases second with secondOld | secondCurrent
        · exact induction firstOld secondOld
        · exact False.elim
            (DispatchTagEvidence.RawMarked.not_prior secondCurrent.2
              (rawMarkedAt_rawMarked firstOld))
      · rcases second with secondOld | secondCurrent
        · exact False.elim
            (DispatchTagEvidence.RawMarked.not_prior firstCurrent.2
              (rawMarkedAt_rawMarked secondOld))
        · exact firstCurrent.1.trans secondCurrent.1.symm

private theorem CanonicalTagHistory.RawMarked.exists_at
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {rawAge : RawTokenAge} {vertex : Vertex}
    (marked : tagHistory.RawMarked rawAge vertex) :
    ∃ position, RawMarkedAt tagHistory position rawAge vertex := by
  induction tagHistory with
  | empty => exact False.elim marked
  | init step => exact False.elim marked
  | later prior evidence induction =>
      rcases marked with old | current
      · rcases induction old with ⟨position, occurs⟩
        exact ⟨position, Or.inl occurs⟩
      · exact ⟨rawMarkEventCount prior, Or.inr ⟨rfl, current⟩⟩

private theorem CanonicalTagHistory.RawMarkedBefore.positions
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {firstAge secondAge : RawTokenAge} {first second : Vertex}
    (before : tagHistory.RawMarkedBefore
      firstAge first secondAge second) :
    ∃ firstPosition secondPosition,
      RawMarkedAt tagHistory firstPosition firstAge first ∧
        RawMarkedAt tagHistory secondPosition secondAge second ∧
          firstPosition < secondPosition := by
  induction before with
  | prior earlier induction =>
      rcases induction with
        ⟨firstPosition, secondPosition, firstAt, secondAt, positionsLt⟩
      exact ⟨firstPosition, secondPosition, Or.inl firstAt,
        Or.inl secondAt, positionsLt⟩
  | current earlier current =>
      rcases CanonicalTagHistory.RawMarked.exists_at earlier with
        ⟨firstPosition, firstAt⟩
      exact ⟨firstPosition, _, Or.inl firstAt,
        Or.inr ⟨rfl, current⟩, rawMarkedAt_position_lt firstAt⟩

private theorem rawMarkedBefore_of_at_lt
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {firstPosition secondPosition : Nat}
    {firstAge secondAge : RawTokenAge} {first second : Vertex}
    (firstAt : RawMarkedAt tagHistory firstPosition firstAge first)
    (secondAt : RawMarkedAt tagHistory secondPosition secondAge second)
    (positionsLt : firstPosition < secondPosition) :
    tagHistory.RawMarkedBefore firstAge first secondAge second := by
  induction tagHistory with
  | empty => exact False.elim firstAt
  | init step => exact False.elim firstAt
  | later prior evidence induction =>
      rcases firstAt with firstOld | firstCurrent
      · rcases secondAt with secondOld | secondCurrent
        · exact .prior (induction firstOld secondOld)
        · exact .current (rawMarkedAt_rawMarked firstOld) secondCurrent.2
      · rcases secondAt with secondOld | secondCurrent
        · have firstEq := firstCurrent.1
          have secondLt := rawMarkedAt_position_lt secondOld
          omega
        · have firstEq := firstCurrent.1
          have secondEq := secondCurrent.1
          omega

namespace CanonicalTagHistory.RawMarkedBefore

/-- Strict canonical raw-mark order is transitive. -/
theorem trans
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {firstAge middleAge lastAge : RawTokenAge}
    {first middle last : Vertex}
    (firstBefore : tagHistory.RawMarkedBefore
      firstAge first middleAge middle)
    (secondBefore : tagHistory.RawMarkedBefore
      middleAge middle lastAge last) :
    tagHistory.RawMarkedBefore firstAge first lastAge last := by
  rcases CanonicalTagHistory.RawMarkedBefore.positions firstBefore with
    ⟨firstPosition, middlePosition, firstAt, middleAt, firstLt⟩
  rcases CanonicalTagHistory.RawMarkedBefore.positions secondBefore with
    ⟨middlePosition', lastPosition, middleAt', lastAt, secondLt⟩
  have middleEq : middlePosition = middlePosition' :=
    rawMarkedAt_position_eq middleAt middleAt'
  apply rawMarkedBefore_of_at_lt firstAt lastAt
  omega

/-- Strict canonical raw-mark order is asymmetric. -/
theorem asymmetric
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {firstAge secondAge : RawTokenAge} {first second : Vertex}
    (before : tagHistory.RawMarkedBefore
      firstAge first secondAge second) :
    ¬ tagHistory.RawMarkedBefore secondAge second firstAge first := by
  intro reverse
  rcases CanonicalTagHistory.RawMarkedBefore.positions before with
    ⟨firstPosition, secondPosition, firstAt, secondAt, firstLt⟩
  rcases CanonicalTagHistory.RawMarkedBefore.positions reverse with
    ⟨secondPosition', firstPosition', secondAt', firstAt', secondLt⟩
  have firstEq : firstPosition = firstPosition' :=
    rawMarkedAt_position_eq firstAt firstAt'
  have secondEq : secondPosition = secondPosition' :=
    rawMarkedAt_position_eq secondAt secondAt'
  omega

end CanonicalTagHistory.RawMarkedBefore

private theorem MarkedConclusionChain.positions_lt_of_ne
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {origin terminal : Vertex} {terminalAge : RawTokenAge}
    (chain : MarkedConclusionChain certificate state origin terminal)
    (terminalEvent : tagHistory.RawMarked terminalAge terminal)
    (different : origin ≠ terminal) :
    ∃ originAge originPosition terminalPosition,
      RawMarkedAt tagHistory originPosition originAge origin ∧
        RawMarkedAt tagHistory terminalPosition terminalAge terminal ∧
          originPosition < terminalPosition := by
  induction chain with
  | refl vertex => exact False.elim (different rfl)
  | @step vertex terminal conclusionAge consumer marked notConclusion tail ih =>
      have conclusionEvent :
          tagHistory.RawMarked conclusionAge consumer.conclusion :=
        tagHistory.final_rawMarked_iff.mp marked
      rcases tagHistory.rawMarkedPremisesBefore consumer conclusionEvent with
        ⟨premiseAge, _mateAge, premiseBefore, _mateBefore⟩
      rcases CanonicalTagHistory.RawMarkedBefore.positions premiseBefore with
        ⟨premisePosition, conclusionPosition, premiseAt, conclusionAt,
          premiseLt⟩
      by_cases same : consumer.conclusion = terminal
      · subst terminal
        rcases CanonicalTagHistory.RawMarked.exists_at terminalEvent with
          ⟨terminalPosition, terminalAt⟩
        have positionEq : conclusionPosition = terminalPosition :=
          rawMarkedAt_position_eq conclusionAt terminalAt
        exact ⟨premiseAge, premisePosition, terminalPosition, premiseAt,
          terminalAt, by omega⟩
      · rcases ih terminalEvent same with
          ⟨chainAge, chainPosition, terminalPosition, chainAt, terminalAt,
            chainLt⟩
        have positionEq : conclusionPosition = chainPosition :=
          rawMarkedAt_position_eq conclusionAt chainAt
        exact ⟨premiseAge, premisePosition, terminalPosition, premiseAt,
          terminalAt, by omega⟩

private theorem MarkedConclusionChain.rawMarkedBefore_of_ne
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {origin terminal : Vertex} {terminalAge : RawTokenAge}
    (chain : MarkedConclusionChain certificate state origin terminal)
    (terminalEvent : tagHistory.RawMarked terminalAge terminal)
    (different : origin ≠ terminal) :
    ∃ originAge,
      tagHistory.RawMarkedBefore originAge origin terminalAge terminal := by
  rcases MarkedConclusionChain.positions_lt_of_ne tagHistory chain
      terminalEvent different with
    ⟨originAge, originPosition, terminalPosition, originAt, terminalAt,
      positionsLt⟩
  exact ⟨originAge,
    rawMarkedBefore_of_at_lt originAt terminalAt positionsLt⟩

private theorem CanonicalTagHistory.RawMarked.age_eq
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {firstAge secondAge : RawTokenAge} {vertex : Vertex}
    (first : tagHistory.RawMarked firstAge vertex)
    (second : tagHistory.RawMarked secondAge vertex) :
    firstAge = secondAge := by
  have firstMarked :
      state.core.marks[vertex]? = some (some firstAge) :=
    tagHistory.final_rawMarked_iff.mpr first
  have secondMarked :
      state.core.marks[vertex]? = some (some secondAge) :=
    tagHistory.final_rawMarked_iff.mpr second
  exact Option.some.inj (Option.some.inj (firstMarked.symm.trans secondMarked))

/-- A finite marked-conclusion chain either is reflexive or places its
origin strictly before an authenticated terminal event. -/
theorem MarkedConclusionChain.rawMarkedBefore_or_eq
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {origin terminal : Vertex} {terminalAge : RawTokenAge}
    (chain : MarkedConclusionChain certificate state origin terminal)
    (terminalEvent : tagHistory.RawMarked terminalAge terminal) :
    origin = terminal ∨
      ∃ originAge,
        tagHistory.RawMarkedBefore originAge origin terminalAge terminal := by
  by_cases same : origin = terminal
  · exact Or.inl same
  · exact Or.inr
      (MarkedConclusionChain.rawMarkedBefore_of_ne tagHistory chain
        terminalEvent same)

namespace MarkedConclusionChainFirstCausalDescent

/-- The descent origin was raw-marked before the full chain terminal. -/
theorem originBeforeTerminal
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin terminal : Vertex} {active terminalAge : RawTokenAge}
    (descent : MarkedConclusionChainFirstCausalDescent certificate state
      tagHistory origin terminal active)
    (terminalEvent : tagHistory.RawMarked terminalAge terminal) :
    ∃ originAge,
      tagHistory.RawMarkedBefore originAge origin terminalAge terminal := by
  rcases descent with
    ⟨originAge, consumer, conclusionAge, mateAge, _originMarked,
      _originRepresentative, _conclusionMarked, conclusionEvent,
      _conclusionNotGlobal, _conclusionOlder, originBefore,
      _mateBefore, _mateExit, tail⟩
  rcases MarkedConclusionChain.rawMarkedBefore_or_eq tagHistory tail
      terminalEvent with
    same | ⟨tailAge, conclusionBeforeTerminal⟩
  · subst terminal
    have ageEq : conclusionAge = terminalAge :=
      CanonicalTagHistory.RawMarked.age_eq conclusionEvent terminalEvent
    subst terminalAge
    exact ⟨originAge, originBefore⟩
  · have ageEq : tailAge = conclusionAge :=
      CanonicalTagHistory.RawMarked.age_eq
        conclusionBeforeTerminal.first_rawMarked conclusionEvent
    subst tailAge
    exact ⟨originAge,
      CanonicalTagHistory.RawMarkedBefore.trans originBefore
        conclusionBeforeTerminal⟩

/-- The first connective's opposite premise was raw-marked before the full
chain terminal. -/
theorem mateBeforeTerminal
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin terminal : Vertex} {active terminalAge : RawTokenAge}
    (descent : MarkedConclusionChainFirstCausalDescent certificate state
      tagHistory origin terminal active)
    (terminalEvent : tagHistory.RawMarked terminalAge terminal) :
    ∃ (consumer : ConnectiveBelow certificate origin) (mateAge : RawTokenAge),
      tagHistory.RawMarkedBefore mateAge consumer.mate terminalAge terminal := by
  rcases descent with
    ⟨originAge, consumer, conclusionAge, mateAge, _originMarked,
      _originRepresentative, _conclusionMarked, conclusionEvent,
      _conclusionNotGlobal, _conclusionOlder, _originBefore,
      mateBefore, _mateExit, tail⟩
  rcases MarkedConclusionChain.rawMarkedBefore_or_eq tagHistory tail
      terminalEvent with
    same | ⟨tailAge, conclusionBeforeTerminal⟩
  · subst terminal
    have ageEq : conclusionAge = terminalAge :=
      CanonicalTagHistory.RawMarked.age_eq conclusionEvent terminalEvent
    subst terminalAge
    exact ⟨consumer, mateAge, mateBefore⟩
  · have ageEq : tailAge = conclusionAge :=
      CanonicalTagHistory.RawMarked.age_eq
        conclusionBeforeTerminal.first_rawMarked conclusionEvent
    subst tailAge
    exact ⟨consumer, mateAge,
      CanonicalTagHistory.RawMarkedBefore.trans mateBefore
        conclusionBeforeTerminal⟩

end MarkedConclusionChainFirstCausalDescent

/-- A re-entry target with an authenticated outer mate, which is the
marked-conclusion chain terminal in its causal-descent alternative. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationTerminalCausalTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex)
    (current : ConnectiveBelow certificate input.vertex) : Prop :=
  ∃ terminalAge,
    tagHistory.RawMarked terminalAge current.mate ∧
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCausalDescentTarget
        tagHistory input component owned current

namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCausalDescentTarget

/-- Attach an authenticated outer-mate event to a causal-descent re-entry
target; it is the chain terminal in the causal-descent alternative. -/
theorem terminalCausalTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCausalDescentTarget
        tagHistory input component owned current)
    {terminalAge : RawTokenAge}
    (terminalEvent : tagHistory.RawMarked terminalAge current.mate) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationTerminalCausalTarget
      tagHistory input component owned current := by
  exact ⟨terminalAge, terminalEvent, target⟩

end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCausalDescentTarget

namespace CanonicalTagHistory

private theorem CommitmentIntervalParTraceOutcome.mapStatus
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

open ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCausalDescentTarget

/-- In the strictly older Wait branch, authenticate the outer mate; it is the
terminal event of any retained causal-descent alternative. -/
theorem WaitStep.commitmentInterval_parTraceReentryMarkedContinuationTerminalCausalOutcome
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
          ActiveCarrierExternalReentryMarkedMateSeparatedContinuationTerminalCausalTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply CanonicalTagHistory.CommitmentIntervalParTraceOutcome.mapStatus
    (step.commitmentInterval_parTraceReentryMarkedContinuationCausalDescentOutcome
      connected tagHistory invariant componentLookup occurrence positive firstAt
      lastAt noTail)
  intro status
  rcases status with ⟨mateOutside, mateMarked, representativeOlder, target⟩
  have terminalEvent :
      tagHistory.RawMarked step.mateRawAge step.consumer.mate :=
    tagHistory.final_rawMarked_iff.mp mateMarked
  exact ⟨mateOutside, mateMarked, representativeOlder,
    terminalCausalTarget target terminalEvent⟩

end SequentialFigure7
end ProofNetIR
