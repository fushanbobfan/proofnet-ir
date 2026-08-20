/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentEdgeTargetAvoidance
import ProofNetIR.SequentialFigure7SameRepresentativeEventTouch
import ProofNetIR.SequentialFigure7TouchCompleteness

/-!
# Figure-7 equal-boundary commitment target avoidance

Classifies the final commitment edge whose child is the active ready head.
The stored-right orientation gives an exact target-avoiding reference path.
The general result is an inclusive dichotomy: its right branch records the
failure of the generic child-untouched callback through an exact stored-left
historical touch, without denying that an avoiding path may also exist.

For a supplied ready-head par conclusion, a parallel inclusive dichotomy
returns an avoiding path or the exact same-age historical trace step from that
conclusion to the selected premise or its mate.

This module does not prove unconditional equal-boundary target avoidance,
dispatcher progress, totality, worklist completeness, fallback removal,
token-age scheduling, or whole-program linearity.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialUnification
open SequentialSchedulerBridge
open SequentialSchedulerState

private theorem sourceLeftReachable_trans
    {certificate : Certificate} {first middle last : Vertex}
    (firstPath : SourceLeftReachable certificate first middle)
    (suffix : SourceLeftReachable certificate middle last) :
    SourceLeftReachable certificate first last := by
  induction firstPath with
  | refl => exact suffix
  | step head tail induction => exact .step head (induction suffix)

private theorem sourceLeftStep_next_unique
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {source firstNext secondNext : Vertex}
    (first : SourceLeftStep certificate source firstNext)
    (second : SourceLeftStep certificate source secondNext) :
    firstNext = secondNext := by
  cases first with
  | @tensor _ _ firstRight _ firstLink =>
      cases second with
      | @tensor _ _ secondRight _ secondLink =>
          have linkEq :=
            UnificationState.StructurallyWellFormed.producerLink_unique
              (conclusion := source)
              (first := .tensor firstNext firstRight source)
              (second := .tensor secondNext secondRight source)
              structural
              (List.mem_of_getElem? firstLink) (by simp [Link.produces])
              (List.mem_of_getElem? secondLink) (by simp [Link.produces])
          exact Link.tensor.inj linkEq |>.1
      | @par _ _ secondRight _ secondLink =>
          have linkEq :=
            UnificationState.StructurallyWellFormed.producerLink_unique
              (conclusion := source)
              (first := .tensor firstNext firstRight source)
              (second := .par secondNext secondRight source)
              structural
              (List.mem_of_getElem? firstLink) (by simp [Link.produces])
              (List.mem_of_getElem? secondLink) (by simp [Link.produces])
          contradiction
  | @par _ _ firstRight _ firstLink =>
      cases second with
      | @tensor _ _ secondRight _ secondLink =>
          have linkEq :=
            UnificationState.StructurallyWellFormed.producerLink_unique
              (conclusion := source)
              (first := .par firstNext firstRight source)
              (second := .tensor secondNext secondRight source)
              structural
              (List.mem_of_getElem? firstLink) (by simp [Link.produces])
              (List.mem_of_getElem? secondLink) (by simp [Link.produces])
          contradiction
      | @par _ _ secondRight _ secondLink =>
          have linkEq :=
            UnificationState.StructurallyWellFormed.producerLink_unique
              (conclusion := source)
              (first := .par firstNext firstRight source)
              (second := .par secondNext secondRight source)
              structural
              (List.mem_of_getElem? firstLink) (by simp [Link.produces])
              (List.mem_of_getElem? secondLink) (by simp [Link.produces])
          exact Link.par.inj linkEq |>.1

private theorem SourceLeftChain.decompose_at_step
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {trace : List Vertex} {reached left right source next : Vertex}
    {linkIndex : Nat}
    (chain : SourceLeftChain certificate trace)
    (last : trace.getLast? = some reached)
    (exactAxiom :
      certificate.links[linkIndex]? = some (.axiom left right))
    (reachedEndpoint : reached = left ∨ reached = right)
    (sourceMem : source ∈ trace)
    (step : SourceLeftStep certificate source next) :
    ∃ beforeTrace afterTrace,
      trace = beforeTrace ++ source :: next :: afterTrace := by
  induction chain generalizing source with
  | singleton only =>
      simp only [List.mem_singleton] at sourceMem
      subst source
      simp only [List.getLast?_singleton, Option.some.injEq] at last
      subst reached
      have axiomMembership :
          Link.axiom left right ∈ certificate.links :=
        List.mem_of_getElem? exactAxiom
      cases step with
      | tensor connective =>
          exact False.elim
            (structural.axiomEndpoint_ne_connectiveConclusion
              axiomMembership reachedEndpoint
              (List.mem_of_getElem? connective) (by simp [Link.produces]))
      | par connective =>
          exact False.elim
            (structural.axiomEndpoint_ne_connectiveConclusion
              axiomMembership reachedEndpoint
              (List.mem_of_getElem? connective) (by simp [Link.produces]))
  | @cons current actualNext tail headStep rest induction =>
      have restLast : (actualNext :: tail).getLast? = some reached := by
        simpa [List.getLast?_cons_of_ne_nil (by simp :
          actualNext :: tail ≠ [])] using last
      rcases List.mem_cons.mp sourceMem with sourceEq | sourceMem
      · subst source
        have nextEq : actualNext = next :=
          sourceLeftStep_next_unique structural headStep step
        subst next
        exact ⟨[], tail, by simp⟩
      · rcases induction restLast sourceMem step with
          ⟨beforeTrace, afterTrace, decomposition⟩
        exact ⟨current :: beforeTrace, afterTrace, by simp [decomposition]⟩

/-- A reservation event touching a submitted par conclusion traverses the
exact stored-left source step in its search trace. -/
theorem ReservationEvent.touched_parConclusion_decomposition
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (event : ReservationEvent certificate)
    {selected : Vertex}
    (consumer : ConnectiveBelow certificate selected)
    (parEq : consumer.kind = .par)
    (touched : event.Touched consumer.conclusion) :
    ∃ beforeTrace afterTrace,
      event.search.result.trace =
        beforeTrace ++ consumer.conclusion :: consumer.storedLeft ::
          afterTrace := by
  have parLookup :
      certificate.links[consumer.linkIndex]? =
        some (.par consumer.storedLeft consumer.storedRight
          consumer.conclusion) := by
    simpa [SequentialConnectiveKind.asLink, parEq] using consumer.link_eq
  have conclusionInTrace :
      consumer.conclusion ∈ event.search.result.trace := by
    rcases touched with inTrace | leftEq | rightEq
    · exact inTrace
    · exfalso
      exact structural.axiomEndpoint_ne_connectiveConclusion
        (List.mem_of_getElem? event.search.result.exactLink) (Or.inl rfl)
        (List.mem_of_getElem? parLookup)
        (by simpa [Link.produces] using leftEq)
    · exfalso
      exact structural.axiomEndpoint_ne_connectiveConclusion
        (List.mem_of_getElem? event.search.result.exactLink) (Or.inr rfl)
        (List.mem_of_getElem? parLookup)
        (by simpa [Link.produces] using rightEq)
  have reachedEndpoint :
      event.search.reached = event.search.result.left ∨
        event.search.reached = event.search.result.right := by
    rcases event.search.route.storedEndpoints with endpoints | endpoints
    · exact Or.inl endpoints.1
    · exact Or.inr endpoints.1
  exact SourceLeftChain.decompose_at_step structural
    event.search.route.chain event.search.route.traceLast
    event.search.result.exactLink reachedEndpoint conclusionInTrace
    (.par parLookup)

/-- Touching a submitted par conclusion records either the exact
conclusion-to-selected step or the exact conclusion-to-mate step, according to
the submitted premise orientation. -/
theorem ReservationEvent.touched_parConclusion_cases
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (event : ReservationEvent certificate)
    {selected : Vertex}
    (consumer : ConnectiveBelow certificate selected)
    (parEq : consumer.kind = .par)
    (touched : event.Touched consumer.conclusion) :
    (consumer.side = .storedLeft ∧
      ∃ beforeTrace afterTrace,
        event.search.result.trace =
          beforeTrace ++ consumer.conclusion :: selected :: afterTrace) ∨
    (consumer.side = .storedRight ∧
      ∃ beforeTrace afterTrace,
        event.search.result.trace =
          beforeTrace ++ consumer.conclusion :: consumer.mate ::
            afterTrace) := by
  rcases event.touched_parConclusion_decomposition structural consumer parEq
      touched with ⟨beforeTrace, afterTrace, decomposition⟩
  cases sideEq : consumer.side with
  | storedLeft =>
      left
      refine ⟨rfl, beforeTrace, afterTrace, ?_⟩
      have selectedEq : selected = consumer.storedLeft := by
        simpa [TensorPremiseSide.premise, sideEq] using consumer.premise_eq
      simpa [selectedEq] using decomposition
  | storedRight =>
      right
      refine ⟨rfl, beforeTrace, afterTrace, ?_⟩
      simpa [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEq] using
        decomposition

namespace CanonicalTagHistory

/-- If an event in the active boundary's current representative touches the
active tensor conclusion, then the tensor is stored-left selected and the
event trace contains the exact conclusion-to-head step. -/
theorem sameRepresentative_conclusionTouch_decomposition
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger)
    (sameRepresentative :
      before.core.representative event.rawAge =
        before.core.representative guard.head.rawAge)
    (touched : event.Touched guard.tensor.conclusion) :
    guard.tensor.side = .storedLeft ∧
      ∃ beforeTrace afterTrace,
        event.search.result.trace =
          beforeTrace ++ guard.tensor.conclusion ::
            guard.head.vertex :: afterTrace := by
  have mateUntouched : ¬ event.Touched guard.tensor.mate := by
    intro mateTouched
    apply tagHistory.not_event_touch_of_sameRepresentative correct invariant guard
      membership sameRepresentative mateTouched
    exact .visited (.refl guard.tensor.mate)
  have conclusionInTrace :
      guard.tensor.conclusion ∈ event.search.result.trace := by
    rcases touched with inTrace | leftEq | rightEq
    · exact inTrace
    · exfalso
      exact invariant.structural.axiomEndpoint_ne_connectiveConclusion
        (List.mem_of_getElem? event.search.result.exactLink) (Or.inl rfl)
        (List.mem_of_getElem? guard.tensor_valid.2.1)
        (by simpa [Link.produces] using leftEq)
    · exfalso
      exact invariant.structural.axiomEndpoint_ne_connectiveConclusion
        (List.mem_of_getElem? event.search.result.exactLink) (Or.inr rfl)
        (List.mem_of_getElem? guard.tensor_valid.2.1)
        (by simpa [Link.produces] using rightEq)
  have sideLeft : guard.tensor.side = .storedLeft := by
    cases sideEquation : guard.tensor.side with
    | storedLeft => exact rfl
    | storedRight =>
        exfalso
        apply mateUntouched
        have conclusionReach :
            SourceLeftReachable certificate event.start
              guard.tensor.conclusion := by
          have region := event.touched_sourceLeftRegion touched
          cases region with
          | visited reachable => exact reachable
          | terminalPartner reachable exactAxiom =>
              rcases exactAxiom with axiomEq | axiomEq
              · exact False.elim
                  (invariant.structural.axiomEndpoint_ne_connectiveConclusion
                    (List.mem_of_getElem? axiomEq) (Or.inr rfl)
                    (List.mem_of_getElem? guard.tensor_valid.2.1)
                    (by simp [Link.produces]))
              · exact False.elim
                  (invariant.structural.axiomEndpoint_ne_connectiveConclusion
                    (List.mem_of_getElem? axiomEq) (Or.inl rfl)
                    (List.mem_of_getElem? guard.tensor_valid.2.1)
                    (by simp [Link.produces]))
        have storedLeftReach :
            SourceLeftReachable certificate event.start guard.tensor.storedLeft :=
          sourceLeftReachable_trans conclusionReach
            (.step (.tensor guard.tensor_valid.2.1)
              (.refl guard.tensor.storedLeft))
        have storedLeftTouched : event.Touched guard.tensor.storedLeft :=
          event.sourceLeftRegion_touched invariant.structural
            (.visited storedLeftReach)
        simpa [TensorBelow.mate, TensorPremiseSide.mate, sideEquation] using
          storedLeftTouched
  have headIsStoredLeft :
      guard.head.vertex = guard.tensor.storedLeft := by
    simpa [TensorBelow.premise, TensorPremiseSide.premise, sideLeft] using
      guard.tensor_valid.2.2.2
  have reachedEndpoint :
      event.search.reached = event.search.result.left ∨
        event.search.reached = event.search.result.right := by
    rcases event.search.route.storedEndpoints with endpoints | endpoints
    · exact Or.inl endpoints.1
    · exact Or.inr endpoints.1
  rcases SourceLeftChain.decompose_at_step invariant.structural
      event.search.route.chain event.search.route.traceLast
      event.search.result.exactLink reachedEndpoint conclusionInTrace
      (.tensor guard.tensor_valid.2.1) with
    ⟨beforeTrace, afterTrace, decomposition⟩
  refine ⟨sideLeft, beforeTrace, afterTrace, ?_⟩
  simpa [headIsStoredLeft] using decomposition

/-- The equal-boundary final commitment edge avoids the active tensor
conclusion in the stored-right orientation. The stored-left orientation is
deliberately excluded because an authentic child event may touch it. -/
theorem commitmentEdge_referencePath_avoiding_of_equal_storedRight
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (guard : NewGuard certificate state)
    {position : Nat} {parent : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt :
      state.stack.sigma[position + 1]? = some guard.head.rawAge)
    (storedRight : guard.tensor.side = .storedRight) :
    tagHistory.CommitmentEdgeTargetAvoidingPath parent guard.head.rawAge
      guard.tensor.conclusion := by
  apply tagHistory.commitmentEdge_referencePath_avoiding invariant
    (guard.futureNewCandidateAt invariant) parentAt childAt
  intro event membership eventAge touched
  have sameRepresentative :
      state.core.representative event.rawAge =
        state.core.representative guard.head.rawAge := by
    rw [eventAge]
  have sideLeft :=
    (tagHistory.sameRepresentative_conclusionTouch_decomposition correct invariant
      guard membership sameRepresentative touched).1
  rw [storedRight] at sideLeft
  contradiction

/-- An equal-boundary final commitment edge satisfies an inclusive case split:
either an exact target-avoiding path is available, or one child event witnesses
failure of the generic child-untouched callback by crossing the active
stored-left tensor conclusion immediately into its queued head. The right
branch does not assert that every target-avoiding path is absent; both branches
may hold. -/
theorem commitmentEdge_equal_boundary_dichotomy
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (guard : NewGuard certificate state)
    {position : Nat} {parent : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt :
      state.stack.sigma[position + 1]? = some guard.head.rawAge) :
    tagHistory.CommitmentEdgeTargetAvoidingPath parent guard.head.rawAge
        guard.tensor.conclusion ∨
      ∃ event : ReservationEvent certificate,
        ∃ beforeTrace afterTrace,
        event ∈ tagHistory.reservationLedger ∧
          event.rawAge = guard.head.rawAge ∧
          guard.tensor.side = .storedLeft ∧
          event.search.result.trace =
            beforeTrace ++ guard.tensor.conclusion ::
              guard.head.vertex :: afterTrace := by
  classical
  by_cases childUntouched :
      ∀ {event : ReservationEvent certificate},
        event ∈ tagHistory.reservationLedger →
          event.rawAge = guard.head.rawAge →
            ¬ event.Touched guard.tensor.conclusion
  · exact Or.inl
      (tagHistory.commitmentEdge_referencePath_avoiding invariant
        (guard.futureNewCandidateAt invariant) parentAt childAt childUntouched)
  · rcases Classical.not_forall.mp childUntouched with ⟨event, missing⟩
    rcases Classical.not_imp.mp missing with ⟨membership, missing⟩
    rcases Classical.not_imp.mp missing with ⟨eventAge, missing⟩
    have touched : event.Touched guard.tensor.conclusion :=
      Classical.not_not.mp missing
    have sameRepresentative :
        state.core.representative event.rawAge =
          state.core.representative guard.head.rawAge := by
      rw [eventAge]
    rcases tagHistory.sameRepresentative_conclusionTouch_decomposition correct
        invariant guard membership sameRepresentative touched with
      ⟨sideLeft, beforeTrace, afterTrace, decomposition⟩
    exact Or.inr ⟨event, beforeTrace, afterTrace, membership, eventAge,
      sideLeft, decomposition⟩

/-- The equal-boundary final commitment edge either avoids the supplied
ready-head par conclusion or exposes an exact same-age historical trace step
from that conclusion to the selected premise or its mate.

The alternatives are inclusive. The theorem does not prove the child event
untouched, eliminate either trace orientation, compose a whole retained
interval, or derive a ready-tail witness. -/
theorem commitmentEdge_parConclusion_dichotomy
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (input : ReadyHeadInput state)
    (consumer : ConnectiveBelow certificate input.vertex)
    (parEq : consumer.kind = .par)
    {position parent : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt :
      state.stack.sigma[position + 1]? = some input.rawAge) :
    tagHistory.CommitmentEdgeTargetAvoidingPath parent input.rawAge
        consumer.conclusion ∨
      ∃ event : ReservationEvent certificate,
        event ∈ tagHistory.reservationLedger ∧
          event.rawAge = input.rawAge ∧
          ((consumer.side = .storedLeft ∧
              ∃ beforeTrace afterTrace,
                event.search.result.trace =
                  beforeTrace ++ consumer.conclusion :: input.vertex ::
                    afterTrace) ∨
            (consumer.side = .storedRight ∧
              ∃ beforeTrace afterTrace,
                event.search.result.trace =
                  beforeTrace ++ consumer.conclusion :: consumer.mate ::
                    afterTrace)) := by
  classical
  by_cases childUntouched :
      ∀ {event : ReservationEvent certificate},
        event ∈ tagHistory.reservationLedger →
          event.rawAge = input.rawAge →
            ¬ event.Touched consumer.conclusion
  · exact Or.inl
      (tagHistory.commitmentEdge_referencePath_avoiding_parConclusion invariant
        input consumer parEq parentAt childAt childUntouched)
  · rcases Classical.not_forall.mp childUntouched with ⟨event, missing⟩
    rcases Classical.not_imp.mp missing with ⟨membership, missing⟩
    rcases Classical.not_imp.mp missing with ⟨eventAge, missing⟩
    have touched : event.Touched consumer.conclusion :=
      Classical.not_not.mp missing
    exact Or.inr ⟨event, membership, eventAge,
      event.touched_parConclusion_cases invariant.structural consumer parEq
        touched⟩

end CanonicalTagHistory
end SequentialFigure7
end ProofNetIR
