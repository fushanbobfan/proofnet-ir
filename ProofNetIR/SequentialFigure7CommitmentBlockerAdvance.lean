/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7EqualBoundaryCommitmentTargetAvoidance
import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchAvailability
import ProofNetIR.SequentialFigure7StrictOlderSigmaSplit

/-!
# Figure-7 commitment blocker advance

Combines global queued-future-work touch separation, the strict older `sigma`
split, and the equal-boundary commitment-edge dichotomy. A failed callback on
a strict retained edge yields a mate-touching ledger event whose current
representative is strictly higher than the starting representative while
remaining strictly below the active candidate representative. Here `advance`
refers only to this current-representative order; it does not assert a later
raw age or a later position in ledger chronology.

The public result is an inclusive three-way reduction: a target-avoiding
commitment path, a strict higher-current-representative mate-touch advance, or
an equal-boundary stored-left callback-failure witness. The last branch does
not assert that a target-avoiding path is absent, and the branches need not be
exclusive.

This module does not exclude the stored-left witness, prove `NewEnabled`,
dispatcher progress, totality, worklist completeness, fallback removal,
token-age scheduling, or whole-program linearity.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

namespace CanonicalTagHistory

private theorem representative_eq_of_sigmaAt
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {position : Nat} {rawAge : RawTokenAge}
    (sigmaAt : state.stack.sigma[position]? = some rawAge) :
    state.core.representative rawAge = rawAge := by
  have rawAgeMembership : rawAge ∈ state.stack.sigma :=
    List.mem_of_getElem? sigmaAt
  have rawAgeBound : rawAge < state.stack.nextAge :=
    invariant.stack_wellShaped.sigma_partition.boundary_lt rawAge
      rawAgeMembership
  rcases
      invariant.stack_wellShaped.sigma_partition.boundary_exists rawAgeBound
    with ⟨boundary, boundaryLookup⟩
  have boundaryLeRawAge : boundary ≤ rawAge :=
    sigmaBoundary?_le boundaryLookup
  have rawAgeLeBoundary : rawAge ≤ boundary :=
    sigmaBoundary?_greatest
      invariant.stack_wellShaped.sigma_partition.strictIncreasing
      boundaryLookup rawAge rawAgeMembership (Nat.le_refl _)
  have boundaryEq : boundary = rawAge :=
    Nat.le_antisymm boundaryLeRawAge rawAgeLeBoundary
  subst boundary
  have representativeLookup :=
    invariant.realizesSigma.representative_eq_boundary rawAgeBound
  exact Option.some.inj (representativeLookup.symm.trans boundaryLookup)

private theorem commitmentEdge_avoiding_or_higherRepresentativeMateTouch
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (headSeparated : OlderEventFutureWorkTouchSeparated tagHistory)
    (candidate : FutureNewCandidateAt certificate state)
    {position : Nat} {parent child : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt : state.stack.sigma[position + 1]? = some child)
    (childOlder :
      state.core.representative child <
        state.core.representative candidate.rawAge) :
    tagHistory.CommitmentEdgeTargetAvoidingPath parent child
        candidate.tensor.conclusion ∨
      ∃ event : ReservationEvent certificate,
        event ∈ tagHistory.reservationLedger ∧
          state.core.representative parent <
            state.core.representative event.rawAge ∧
          state.core.representative event.rawAge <
            state.core.representative candidate.rawAge ∧
          event.Touched candidate.tensor.mate := by
  classical
  by_cases childUntouched :
      ∀ {event : ReservationEvent certificate},
        event ∈ tagHistory.reservationLedger → event.rawAge = child →
          ¬ event.Touched candidate.tensor.conclusion
  · exact Or.inl
      (tagHistory.commitmentEdge_referencePath_avoiding invariant candidate
        parentAt childAt childUntouched)
  · rcases Classical.not_forall.mp childUntouched with ⟨event, missing⟩
    rcases Classical.not_imp.mp missing with ⟨membership, missing⟩
    rcases Classical.not_imp.mp missing with ⟨eventAge, missing⟩
    have conclusionTouched : event.Touched candidate.tensor.conclusion :=
      Classical.not_not.mp missing
    have parentRoot := representative_eq_of_sigmaAt invariant parentAt
    have childRoot := representative_eq_of_sigmaAt invariant childAt
    have indexOrder : parent < child := by
      rcases List.getElem?_eq_some_iff.mp parentAt with
        ⟨parentBound, parentValue⟩
      rcases List.getElem?_eq_some_iff.mp childAt with
        ⟨childBound, childValue⟩
      have ordered :=
        (List.pairwise_iff_getElem.mp
          invariant.stack_wellShaped.sigma_partition.strictIncreasing)
          position (position + 1) parentBound childBound (by omega)
      simpa [parentValue, childValue] using ordered
    have parentBeforeEvent :
        state.core.representative parent <
          state.core.representative event.rawAge := by
      rw [eventAge, parentRoot, childRoot]
      exact indexOrder
    have eventOlder :
        state.core.representative event.rawAge <
          state.core.representative candidate.rawAge := by
      simpa [eventAge] using childOlder
    rcases event.touched_candidateConclusion_cases invariant.structural candidate
        conclusionTouched with mateTouched | headTouched
    · exact Or.inr
        ⟨event, membership, parentBeforeEvent, eventOlder, mateTouched⟩
    · exact False.elim
        (headSeparated.event_candidate membership candidate eventOlder headTouched)

private theorem commitmentInterval_avoiding_or_higherRepresentativeMateTouch
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (headSeparated : OlderEventFutureWorkTouchSeparated tagHistory)
    (candidate : FutureNewCandidateAt certificate state)
    {position edgeCount : Nat} {first last : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : state.stack.sigma[position]? = some first)
    (lastAt : state.stack.sigma[position + edgeCount]? = some last)
    (lastOlder :
      state.core.representative last <
        state.core.representative candidate.rawAge) :
    tagHistory.CommitmentEdgeTargetAvoidingPath first last
        candidate.tensor.conclusion ∨
      ∃ event : ReservationEvent certificate,
        event ∈ tagHistory.reservationLedger ∧
          state.core.representative first <
            state.core.representative event.rawAge ∧
          state.core.representative event.rawAge <
            state.core.representative candidate.rawAge ∧
          event.Touched candidate.tensor.mate := by
  induction edgeCount generalizing position first last with
  | zero => omega
  | succ remaining induction =>
      have lastBound :
          position + Nat.succ remaining < state.stack.sigma.length :=
        (List.getElem?_eq_some_iff.mp lastAt).choose
      have nextBound : position + 1 < state.stack.sigma.length := by
        omega
      let middle := state.stack.sigma[position + 1]
      have middleAt :
          state.stack.sigma[position + 1]? = some middle :=
        List.getElem?_eq_getElem nextBound
      have middleRoot := representative_eq_of_sigmaAt invariant middleAt
      have lastRoot := representative_eq_of_sigmaAt invariant lastAt
      have middleLeLast : middle ≤ last := by
        by_cases sameIndex : position + 1 = position + Nat.succ remaining
        · have sameLookup :
              state.stack.sigma[position + 1]? = some last := by
            simpa [sameIndex] using lastAt
          exact Nat.le_of_eq
            (Option.some.inj (middleAt.symm.trans sameLookup))
        · have indexLt : position + 1 < position + Nat.succ remaining := by
            omega
          rcases List.getElem?_eq_some_iff.mp middleAt with
            ⟨middleBoundAgain, middleValue⟩
          rcases List.getElem?_eq_some_iff.mp lastAt with
            ⟨lastBoundAgain, lastValue⟩
          have ordered :=
            (List.pairwise_iff_getElem.mp
              invariant.stack_wellShaped.sigma_partition.strictIncreasing)
              (position + 1) (position + Nat.succ remaining)
              middleBoundAgain lastBoundAgain indexLt
          rw [middleValue, lastValue] at ordered
          exact Nat.le_of_lt ordered
      have middleOlder :
          state.core.representative middle <
            state.core.representative candidate.rawAge := by
        rw [middleRoot]
        rw [lastRoot] at lastOlder
        exact Nat.lt_of_le_of_lt middleLeLast lastOlder
      rcases tagHistory.commitmentEdge_avoiding_or_higherRepresentativeMateTouch
          invariant headSeparated candidate firstAt middleAt middleOlder with
        firstPath | blocker
      · by_cases noTail : remaining = 0
        · subst remaining
          have sameAge : middle = last := by
            apply Option.some.inj
            exact middleAt.symm.trans (by simpa using lastAt)
          subst last
          exact Or.inl firstPath
        · have indexEq :
              position + Nat.succ remaining = (position + 1) + remaining := by
            omega
          have tailLastAt :
              state.stack.sigma[(position + 1) + remaining]? = some last := by
            rw [← indexEq]
            exact lastAt
          rcases induction (Nat.zero_lt_of_ne_zero noTail) middleAt tailLastAt
              lastOlder with tailPath | tailBlocker
          · rcases firstPath with
              ⟨firstEvent, middleEvent, firstWitness, firstLookup,
                middleLookup, firstStarts, firstFinishes, firstAvoids⟩
            rcases tailPath with
              ⟨middleEventAgain, lastEvent, tailWitness, middleLookupAgain,
                lastLookup, tailStarts, tailFinishes, tailAvoids⟩
            have middleEq : middleEvent = middleEventAgain := by
              apply Option.some.inj
              exact middleLookup.symm.trans middleLookupAgain
            subst middleEventAgain
            have meeting : firstWitness.finish = tailWitness.start :=
              firstFinishes.trans tailStarts.symm
            rcases firstWitness.connectEraseAvoiding tailWitness meeting
                firstAvoids tailAvoids with
              ⟨path, pathStarts, pathFinishes, pathAvoids⟩
            exact Or.inl
              ⟨firstEvent, lastEvent, path, firstLookup, lastLookup,
                pathStarts.trans firstStarts,
                pathFinishes.trans tailFinishes, pathAvoids⟩
          · rcases tailBlocker with
              ⟨event, membership, middleBefore, eventOlder, mateTouched⟩
            have firstBeforeMiddle :
                state.core.representative first <
                  state.core.representative middle := by
              have firstRoot := representative_eq_of_sigmaAt invariant firstAt
              have firstLtMiddle : first < middle := by
                rcases List.getElem?_eq_some_iff.mp firstAt with
                  ⟨firstBound, firstValue⟩
                rcases List.getElem?_eq_some_iff.mp middleAt with
                  ⟨middleBoundAgain, middleValue⟩
                have ordered :=
                  (List.pairwise_iff_getElem.mp
                    invariant.stack_wellShaped.sigma_partition.strictIncreasing)
                    position (position + 1) firstBound middleBoundAgain (by omega)
                simpa [firstValue, middleValue] using ordered
              rw [firstRoot, middleRoot]
              exact firstLtMiddle
            exact Or.inr
              ⟨event, membership, Nat.lt_trans firstBeforeMiddle middleBefore,
                eventOlder, mateTouched⟩
      · exact Or.inr blocker

/-- Under declarative correctness, the complete scheduler invariant, a
canonical history, and an active `NewGuard`, an authentic ledger event whose
current representative is strictly below the active head reduces to one of
three inclusive alternatives:

* a commitment reference path avoiding the active tensor conclusion;
* a mate-touching ledger event with a strictly higher current representative,
  still strictly below the active head's current representative; or
* an equal-boundary stored-left event trace witnessing failure of the generic
  child-untouched callback through the exact conclusion-to-head step.

The second alternative is an advance only in current-representative order,
not in raw-age or ledger chronology. The third alternative does not deny that
an avoiding path may also exist. This theorem does not derive the independent
mate-region invariant, close any created-candidate raw seam, prove `NewEnabled`,
or establish scheduler progress, totality, or completeness. -/
theorem strictOlder_commitmentPath_or_advance_or_equalCallbackFailure
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (guard : NewGuard certificate state)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger)
    (older :
      state.core.representative event.rawAge <
        state.core.representative guard.head.rawAge) :
    tagHistory.CommitmentEdgeTargetAvoidingPath
        (state.core.representative event.rawAge) guard.head.rawAge
        guard.tensor.conclusion ∨
      (∃ higherEvent : ReservationEvent certificate,
        higherEvent ∈ tagHistory.reservationLedger ∧
          state.core.representative event.rawAge <
            state.core.representative higherEvent.rawAge ∧
          state.core.representative higherEvent.rawAge <
            state.core.representative guard.head.rawAge ∧
          higherEvent.Touched guard.tensor.mate) ∨
      ∃ childEvent : ReservationEvent certificate,
        ∃ beforeTrace afterTrace,
          childEvent ∈ tagHistory.reservationLedger ∧
            childEvent.rawAge = guard.head.rawAge ∧
            guard.tensor.side = .storedLeft ∧
            childEvent.search.result.trace =
              beforeTrace ++ guard.tensor.conclusion ::
                guard.head.vertex :: afterTrace := by
  let candidate := guard.futureNewCandidateAt invariant
  have headSeparated :
      OlderEventFutureWorkTouchSeparated tagHistory :=
    tagHistory.olderEventFutureWorkTouchSeparated invariant.structural
  rcases tagHistory.strictOlderSigmaSplit invariant membership candidate older with
    ⟨position, edgeCount, predecessor, firstAt, predecessorAt, childAt,
      predecessorOlder⟩
  by_cases zero : edgeCount = 0
  · subst edgeCount
    have same : state.core.representative event.rawAge = predecessor := by
      apply Option.some.inj
      exact firstAt.symm.trans (by simpa using predecessorAt)
    subst predecessor
    rcases tagHistory.commitmentEdge_equal_boundary_dichotomy correct invariant
        guard predecessorAt childAt with path | callbackFailure
    · exact Or.inl path
    · exact Or.inr (Or.inr callbackFailure)
  · have positive : 0 < edgeCount := Nat.zero_lt_of_ne_zero zero
    rcases
        tagHistory.commitmentInterval_avoiding_or_higherRepresentativeMateTouch
          invariant headSeparated candidate positive firstAt predecessorAt
          predecessorOlder with prefixPath | blocker
    · rcases tagHistory.commitmentEdge_equal_boundary_dichotomy correct invariant
          guard predecessorAt childAt with suffixPath | callbackFailure
      · rcases prefixPath with
          ⟨firstEvent, middleEvent, prefixWitness, firstLookup, middleLookup,
            prefixStarts, prefixFinishes, prefixAvoids⟩
        rcases suffixPath with
          ⟨middleEventAgain, lastEvent, suffixWitness, middleLookupAgain,
            lastLookup, suffixStarts, suffixFinishes, suffixAvoids⟩
        have middleEq : middleEvent = middleEventAgain := by
          apply Option.some.inj
          exact middleLookup.symm.trans middleLookupAgain
        subst middleEventAgain
        have meeting : prefixWitness.finish = suffixWitness.start :=
          prefixFinishes.trans suffixStarts.symm
        rcases prefixWitness.connectEraseAvoiding suffixWitness meeting
            prefixAvoids suffixAvoids with
          ⟨path, pathStarts, pathFinishes, pathAvoids⟩
        exact Or.inl
          ⟨firstEvent, lastEvent, path, firstLookup, lastLookup,
            pathStarts.trans prefixStarts, pathFinishes.trans suffixFinishes,
            pathAvoids⟩
      · exact Or.inr (Or.inr callbackFailure)
    · rcases blocker with
        ⟨higherEvent, higherMembership, firstBeforeHigher, higherOlder,
          mateTouched⟩
      have firstRoot := representative_eq_of_sigmaAt invariant firstAt
      rw [firstRoot] at firstBeforeHigher
      change
        state.core.representative higherEvent.rawAge <
          state.core.representative guard.head.rawAge at higherOlder
      exact Or.inr (Or.inl
        ⟨higherEvent, higherMembership, firstBeforeHigher, higherOlder,
          mateTouched⟩)

end CanonicalTagHistory
end SequentialFigure7
end ProofNetIR
