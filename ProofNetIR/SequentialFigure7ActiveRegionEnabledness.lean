/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveRegionTouchSeparation
import ProofNetIR.SequentialFigure7OlderRawMarkedRegionSeparation
import ProofNetIR.SequentialFigure7RawMarkReservationAnchor

/-!
# Figure-7 active-region enabledness

Closes the active `NewGuard` input-availability gate without assuming either
the global `OlderEventTouchSeparated` invariant or the global
`OlderRawMarkedRegionSeparated` invariant. The preceding local touch theorem
excludes historical tag blockers. A concrete raw mark is anchored to its exact
reservation event and final owned component; the resulting active-mate anchor
is incompatible with strict representative order, excluding the remaining
occurrence-exact owner blocker.

The final theorem proves input-only `NewEnabled` for an already established
history-indexed active guard. It does not prove that a guard exists, choose a
dispatcher branch, establish queue/worklist origin or completeness, prove a
successful whole dispatch step, remove fallback recursion, derive token-age
scheduling or whole-program linearity, or discharge the remaining global
sequentialization obligations.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

namespace CanonicalTagHistory

/-- The complete active mate source-left region contains no concrete raw mark.

Unlike `OlderRawMarkedRegionSeparated.active_sourceLeftRegion_no_rawMark`,
this local theorem needs no global raw-marked-region separation premise. -/
theorem active_sourceLeftRegion_no_rawMark
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {vertex : Vertex}
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex) :
    ¬ ∃ rawAge, before.core.marks[vertex]? = some (some rawAge) := by
  rintro ⟨rawAge, marked⟩
  have representativeLe :=
    guard.marked_representative_le_active invariant marked
  have representativeNe :=
    guard.sourceLeftRegion_marked_representative_ne_active
      correct invariant region marked
  have representativeLt :
      before.core.representative rawAge <
        before.core.representative guard.head.rawAge :=
    Nat.lt_of_le_of_ne representativeLe representativeNe
  rcases tagHistory.rawMarked_reservationEvent_referenceAnchors invariant
      marked with
    ⟨event, component, _eventUsed, _forestUsed, owned, leftPath, _rightPath,
      eventLookup, eventAge, componentLookup, _eventDerivation, _eventLink,
      _eventWitness, eventAccounted, _vertexOwned, _eventLeftOwned,
      _eventRightOwned, leftStarts, leftFinishes, leftWithin,
      _rightStarts, _rightFinishes, _rightWithin⟩
  have eventMembership : event ∈ tagHistory.reservationLedger :=
    List.mem_of_getElem? eventLookup
  have eventOlder :
      before.core.representative event.rawAge <
        before.core.representative guard.head.rawAge := by
    simpa [eventAge] using representativeLt
  have mateBelowConclusion :
      certificate.formulaComplexityAt guard.tensor.mate <
        certificate.formulaComplexityAt guard.tensor.conclusion :=
    guard.sourceLeftRegion_formulaComplexity_lt_conclusion correct.1
      (.visited (.refl _))
  have vertexBelowConclusion :
      certificate.formulaComplexityAt vertex <
        certificate.formulaComplexityAt guard.tensor.conclusion :=
    guard.sourceLeftRegion_formulaComplexity_lt_conclusion correct.1 region
  have vertexNeConclusion : vertex ≠ guard.tensor.conclusion := by
    intro same
    exact (Nat.ne_of_lt vertexBelowConclusion)
      (congrArg certificate.formulaComplexityAt same)
  rcases sourceLeftRegionVertex_referencePath_avoiding correct.1 region
      mateBelowConclusion vertexNeConclusion with
    ⟨regionPath, regionStarts, regionFinishes, regionAvoids⟩
  have conclusionNotOwned : guard.tensor.conclusion ∉ owned :=
    guard.tensorConclusion_not_owned invariant componentLookup eventAccounted
  have leftAvoids : guard.tensor.conclusion ∉ leftPath.vertices := by
    intro inPath
    exact conclusionNotOwned
      (leftWithin guard.tensor.conclusion inPath)
  rcases regionPath.connectEraseAvoiding leftPath
      (regionFinishes.trans leftStarts.symm) regionAvoids leftAvoids with
    ⟨anchorPath, anchorStarts, anchorFinishes, anchorAvoids⟩
  have anchor : ActiveMateEventAnchor guard event :=
    ⟨anchorPath, anchorStarts.trans regionStarts,
      anchorFinishes.trans leftFinishes, anchorAvoids⟩
  exact (tagHistory.no_strictOlder_activeMateEventAnchor
    correct invariant guard eventMembership eventOlder) anchor

/-- No occurrence in the complete active mate source-left region has an exact
live marked owner. -/
theorem active_sourceLeftRegion_no_exactMarkedOwner
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before) :
    ∀ {vertex},
      SourceLeftRegionVertex certificate guard.tensor.mate vertex →
        ¬ ExactMarkedOccurrenceOwner certificate before.core vertex := by
  intro vertex region owner
  rcases owner with
    ⟨rawAge, _index, _component, _usedLinks, _owned, marked,
      _representative, _componentLookup, _witness, _accounted,
      _vertexOwned⟩
  exact tagHistory.active_sourceLeftRegion_no_rawMark
    correct invariant guard region ⟨rawAge, marked⟩

/-- Every occurrence in the complete active mate source-left region is false
in the current input tag carrier, with no global older-event separation
premise. -/
theorem active_sourceLeftRegion_tagFresh
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {vertex : Vertex}
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex) :
    before.tags[vertex]? = some false := by
  by_cases fresh : before.tags[vertex]? = some false
  · exact fresh
  · have touched :=
      tagHistory.classifyFreshTagBlocker invariant guard region fresh
    rcases tagHistory.touched_reservationLedger_event touched with
      ⟨event, eventMembership, eventTouched⟩
    have separated :=
      tagHistory.event_touchSeparatedFrom_active_sourceLeftRegion
        correct invariant guard eventMembership
    exact (separated eventTouched region).elim

/-- The active history-indexed guard determines a complete input-only source
region package, including the exact run, endpoint queue absence, and waiting
capacity. -/
theorem active_newSourceRegionInput
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before) :
    Nonempty (NewSourceRegionInput certificate before) := by
  rcases invariant.structural.freshSourceLeftRun_or_blocker
      guard.mate_bound with run | blocker
  · rcases run with ⟨trace, reached, partner, linkIndex, run⟩
    rcases run with ⟨run⟩
    exact ⟨tagHistory.newSourceRegionInputOfRun invariant guard run⟩
  · rcases blocker with ⟨blocker⟩
    rcases tagHistory.classifyFreshSourceBlocker_of_declarativelyCorrect
        correct invariant guard blocker with touched | owner
    · have fresh := tagHistory.active_sourceLeftRegion_tagFresh
        correct invariant guard blocker.region
      have tagged : before.tags[blocker.vertex]? = some true :=
        tagHistory.tagged_iff_touched.2 touched
      rw [tagged] at fresh
      simp at fresh
    · exact False.elim
        (tagHistory.active_sourceLeftRegion_no_exactMarkedOwner
          correct invariant guard blocker.region owner)

/-- Every history-indexed active `NewGuard` is input-only `NewEnabled`, with
no global older-event or older-raw-region separation premise. -/
theorem active_newEnabled
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before) :
    NewEnabled certificate before := by
  rcases tagHistory.active_newSourceRegionInput correct invariant guard with
    ⟨input⟩
  exact input.newEnabled invariant history.futureWaitingUndefined

end CanonicalTagHistory
end SequentialFigure7
end ProofNetIR
