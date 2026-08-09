import ProofNetIR.SequentialFigure7ActiveRegionAvailability
import ProofNetIR.SequentialFigure7CrossRepresentativeStablePreservation

namespace ProofNetIR

/-!
# Figure-7 older raw-marked region separation

This module isolates a state-only separation invariant for concrete raw marks.
`OlderRawMarksSeparatedFrom` is deliberately parameterized by only a candidate
raw age and source-left start, so later rule-local created candidates can reuse
it without first constructing a `FutureWorkAt` witness.  The bundled
`OlderRawMarkedRegionSeparated` quantifies that primitive over the future
`new` candidates already present in one scheduler state.

The synchronized prepare prefix preserves this invariant.  Its sole new raw
mark belongs to the selected active boundary and therefore cannot be strictly
older than any surviving future candidate; every other mark transports from
the input state.  The exact `concl` and `nop` rules inherit that result because
their output is the prepared state.

For an active `NewGuard`, every concrete marked representative is at most the
active representative.  Declarative correctness excludes equality inside the
mate source-left region, so the separation invariant eliminates every raw mark
there.  The resulting owner-clear theorem has exactly the premise shape used
by `CanonicalTagHistory.active_newEnabled_of_no_exactMarkedOwner`.

No preservation theorem for `new`, `wait`, `forward`, or `unifyPayload` is
claimed here.  In particular, this module does not manufacture created-region
side conditions, prove global source-region separation, establish progress or
totality, remove the recursive fallback, or prove whole-program linearity.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

/-- Every concrete raw mark whose current representative is strictly older
than the supplied candidate representative lies outside the supplied
source-left region.

The primitive intentionally stores no future-work, executor, history, or
reachability witness.  This makes it usable for rule-local candidates that do
not yet occur in the scheduler queues.
-/
def OlderRawMarksSeparatedFrom
    (certificate : Certificate) (state : ReservationState)
    (candidateRawAge : RawTokenAge) (candidateMate : Vertex) : Prop :=
  ∀ rawAge vertex,
    state.core.marks[vertex]? = some (some rawAge) →
      state.core.representative rawAge <
          state.core.representative candidateRawAge →
        ¬ SourceLeftRegionVertex certificate candidateMate vertex

/-- Every queued future `new` candidate is separated from every strictly
older concrete raw mark in the current state.

This is a state predicate, not a reachability or history predicate.
-/
structure OlderRawMarkedRegionSeparated
    (certificate : Certificate) (state : ReservationState) : Prop where
  /-- Instantiate the generic separation primitive at one exact future
  candidate already present in the scheduler state. -/
  candidate :
    ∀ candidate : FutureNewCandidateAt certificate state,
      OlderRawMarksSeparatedFrom certificate state candidate.rawAge
        candidate.tensor.mate

/-- Under the complete scheduler invariant, occurrence-exact marked ownership
is equivalent to the existence of the concrete raw mark stored at that
occurrence. -/
theorem SchedulerInvariant.exactMarkedOccurrenceOwner_iff_exists_rawMark
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {vertex : Vertex} :
    ExactMarkedOccurrenceOwner certificate state.core vertex ↔
      ∃ rawAge, state.core.marks[vertex]? = some (some rawAge) := by
  constructor
  · rintro ⟨rawAge, _index, _component, _used, _owned, marked, _rest⟩
    exact ⟨rawAge, marked⟩
  · rintro ⟨rawAge, marked⟩
    exact SchedulerInvariant.exactMarkedOccurrenceOwner invariant marked

/-- The exact empty reservation state has no raw marks and therefore satisfies
older raw-marked region separation. -/
theorem empty_olderRawMarkedRegionSeparated (certificate : Certificate) :
    OlderRawMarkedRegionSeparated certificate
      (ReservationState.empty certificate) := by
  refine { candidate := ?_ }
  intro _candidate
  intro rawAge vertex marked _older
  by_cases vertexBound : vertex < certificate.formulas.size <;>
    simp [ReservationState.empty, Certificate.initialUnificationState,
      vertexBound] at marked

/-- A successful initial reservation preserves the empty raw-mark array, so
its output establishes older raw-marked region separation without an extra
side condition. -/
theorem InitialReservationStep.olderRawMarkedRegionSeparated
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    OlderRawMarkedRegionSeparated certificate after := by
  refine { candidate := ?_ }
  intro _candidate
  intro rawAge vertex marked _older
  rw [step.output_eq] at marked
  change step.coreAfter.marks[vertex]? = some (some rawAge) at marked
  rcases certificate.reserveAxiomAt?_exact step.core_eq with
    ⟨_left, _right, _component, _link, _ready, _componentEq, _frontier,
      marksEq, _parents, _components, _started, _fired⟩
  rw [marksEq] at marked
  by_cases vertexBound : vertex < certificate.formulas.size <;>
    simp [ReservationState.empty, Certificate.initialUnificationState,
      vertexBound] at marked

private theorem PreparedStep.selected_not_strictly_older_than_candidate
    {certificate : Certificate} {before : ReservationState}
    (step : PreparedStep before)
    (invariant : SchedulerInvariant certificate before)
    (candidate : FutureNewCandidateAt certificate step.after) :
    ¬ step.after.core.representative step.stackResult.rawAge <
        step.after.core.representative candidate.rawAge := by
  intro older
  have afterInvariant : SchedulerInvariant certificate step.after :=
    step.schedulerInvariant invariant
  rcases SequentialStackState.popReadyMark?_exact step.stack_eq with
    ⟨_topReady, sigmaTopBefore, _selectedUnmarked, _stackMarks,
      _nextAge, sigmaEq, _readyEq, _waitingEq, stackSelectedMarked⟩
  have sigmaTopAfter :
      step.stackResult.after.sigma.getLast? =
        some step.stackResult.rawAge := by
    rw [sigmaEq]
    exact sigmaTopBefore
  have activeAgeBound :
      step.stackResult.rawAge < step.stackResult.after.nextAge :=
    afterInvariant.stack_wellShaped.assigned_age_bound
      step.stackResult.vertex step.stackResult.rawAge stackSelectedMarked
  have activeBoundary :=
    afterInvariant.stack_wellShaped.sigma_partition.sigmaBoundary?_eq_top
      sigmaTopAfter
  have activeRealized :=
    afterInvariant.realizesSigma.representative_eq_boundary activeAgeBound
  have activeRoot :
      step.after.core.representative step.stackResult.rawAge =
        step.stackResult.rawAge := by
    exact Option.some.inj (activeRealized.symm.trans activeBoundary)
  have candidateAgeBound : candidate.rawAge < step.after.stack.nextAge :=
    candidate.work.rawAge_lt_nextAge afterInvariant
  have candidateRoot :
      step.after.core.representative candidate.rawAge = candidate.rawAge :=
    candidate.work.representative_eq_rawAge afterInvariant
  have candidateLeActive : candidate.rawAge ≤ step.stackResult.rawAge := by
    by_cases candidateLe : candidate.rawAge ≤ step.stackResult.rawAge
    · exact candidateLe
    · have activeLtCandidate :
          step.stackResult.rawAge < candidate.rawAge :=
        Nat.lt_of_not_ge candidateLe
      have topLookup :=
        afterInvariant.stack_wellShaped.sigma_partition
          |>.sigmaBoundary?_eq_top_of_le sigmaTopAfter
            (Nat.le_of_lt activeLtCandidate) candidateAgeBound
      have candidateRealized :=
        afterInvariant.realizesSigma.representative_eq_boundary
          candidateAgeBound
      have representativeEq :
          step.after.core.representative candidate.rawAge =
            step.stackResult.rawAge :=
        Option.some.inj (candidateRealized.symm.trans topLookup)
      have candidateEq : candidate.rawAge = step.stackResult.rawAge :=
        candidateRoot.symm.trans representativeEq
      exact False.elim
        ((Nat.ne_of_lt activeLtCandidate) candidateEq.symm)
  rw [activeRoot, candidateRoot] at older
  exact (Nat.not_lt_of_ge candidateLeActive) older

/-- The synchronized pop/raw-mark prefix preserves older raw-marked region
separation for every future candidate that survives in the prepared state.

The newly selected mark cannot satisfy the strict older-representative guard;
all other marks and representatives transport from the input state.
-/
theorem PreparedStep.olderRawMarkedRegionSeparated
    {certificate : Certificate} {before : ReservationState}
    (step : PreparedStep before)
    (invariant : SchedulerInvariant certificate before)
    (separated : OlderRawMarkedRegionSeparated certificate before) :
    OlderRawMarkedRegionSeparated certificate step.after := by
  refine { candidate := ?_ }
  intro candidate
  intro rawAge vertex marked older
  intro region
  rcases UnificationState.markReadyRaw?_exact step.core_mark_eq with
    ⟨_selectedUnmarked, afterMarks, _parents, _components, _started,
      _fired, selectedMarked⟩
  by_cases selectedEq : step.stackResult.vertex = vertex
  · subst vertex
    have markedSelected :
        step.after.core.marks[step.stackResult.vertex]? =
          some (some step.stackResult.rawAge) := by
      exact selectedMarked
    have rawAgeEq : rawAge = step.stackResult.rawAge := by
      exact (Option.some.inj
        (Option.some.inj (markedSelected.symm.trans marked))).symm
    subst rawAge
    exact step.selected_not_strictly_older_than_candidate invariant
      candidate older
  · have beforeMarked :
        before.core.marks[vertex]? = some (some rawAge) := by
      change step.coreMarked.marks[vertex]? = some (some rawAge) at marked
      rw [afterMarks] at marked
      simpa [Array.getElem?_setIfInBounds, selectedEq] using marked
    let beforeCandidate : FutureNewCandidateAt certificate before :=
      candidate.beforePrepared step
    have olderBefore :
        before.core.representative rawAge <
          before.core.representative beforeCandidate.rawAge := by
      change before.core.representative rawAge <
        before.core.representative candidate.rawAge
      rw [← step.after_representative_eq_before rawAge,
        ← step.after_representative_eq_before candidate.rawAge]
      exact older
    exact (separated.candidate beforeCandidate rawAge vertex beforeMarked
      olderBefore) region

/-- A successful exact `concl` step preserves older raw-marked region
separation because its output is exactly the prepared state. -/
theorem ConclStep.olderRawMarkedRegionSeparated
    {certificate : Certificate} {before after : ReservationState}
    (step : ConclStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (separated : OlderRawMarkedRegionSeparated certificate before) :
    OlderRawMarkedRegionSeparated certificate after := by
  rw [step.output_eq]
  exact step.prepared.olderRawMarkedRegionSeparated invariant separated

/-- A successful exact `nop` step preserves older raw-marked region
separation because its output is exactly the prepared state. -/
theorem NopStep.olderRawMarkedRegionSeparated
    {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (separated : OlderRawMarkedRegionSeparated certificate before) :
    OlderRawMarkedRegionSeparated certificate after := by
  rw [step.output_eq]
  exact step.prepared.olderRawMarkedRegionSeparated invariant separated

/-- Every concrete raw mark in an active `NewGuard` input resolves to a
representative at or below the active representative. -/
theorem NewGuard.marked_representative_le_active
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (marked : before.core.marks[vertex]? = some (some rawAge)) :
    before.core.representative rawAge ≤
      before.core.representative guard.head.rawAge := by
  have stackMarked :
      before.stack.marks[vertex]? = some (some rawAge) := by
    rw [← invariant.realizesSigma.marks_eq]
    exact marked
  have rawAgeBound : rawAge < before.stack.nextAge :=
    invariant.stack_wellShaped.assigned_age_bound vertex rawAge stackMarked
  have rawAgeBoundary :=
    invariant.realizesSigma.representative_eq_boundary rawAgeBound
  have representativeLeActive :
      before.core.representative rawAge ≤ guard.head.rawAge := by
    by_cases rawLtActive : rawAge < guard.head.rawAge
    · exact Nat.le_trans
        (UnificationState.OrderedParents.representative_le
          invariant.core_orderedParents rawAge)
        (Nat.le_of_lt rawLtActive)
    · have activeLeRaw : guard.head.rawAge ≤ rawAge :=
        Nat.le_of_not_gt rawLtActive
      have topLookup :=
        invariant.stack_wellShaped.sigma_partition
          |>.sigmaBoundary?_eq_top_of_le guard.head.sigma_top activeLeRaw
            rawAgeBound
      exact Nat.le_of_eq
        (Option.some.inj (rawAgeBoundary.symm.trans topLookup))
  have activeRoot :
      before.core.representative guard.head.rawAge = guard.head.rawAge :=
    (guard.head.futureWorkAt invariant).representative_eq_rawAge invariant
  rw [activeRoot]
  exact representativeLeActive

/-- Under declarative correctness and the complete scheduler invariant, an
active mate source-left region contains no concrete raw mark when older
raw-marked regions are separated. -/
theorem OlderRawMarkedRegionSeparated.active_sourceLeftRegion_no_rawMark
    {certificate : Certificate} {before : ReservationState}
    (separated : OlderRawMarkedRegionSeparated certificate before)
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
  exact
    (separated.candidate (guard.futureNewCandidateAt invariant)
      rawAge vertex marked representativeLt) region

/-- Direct owner-clear premise for
`CanonicalTagHistory.active_newEnabled_of_no_exactMarkedOwner`.

Every exact marked owner exposes a concrete raw mark through the complete
scheduler invariant, and the active-region raw-mark exclusion rejects it.
-/
theorem OlderRawMarkedRegionSeparated.active_clearOwner
    {certificate : Certificate} {before : ReservationState}
    (separated : OlderRawMarkedRegionSeparated certificate before)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before) :
    ∀ {vertex},
      SourceLeftRegionVertex certificate guard.tensor.mate vertex →
        ¬ ExactMarkedOccurrenceOwner certificate before.core vertex := by
  intro vertex region owner
  have rawMarked :=
    (SchedulerInvariant.exactMarkedOccurrenceOwner_iff_exists_rawMark
      invariant).mp owner
  exact separated.active_sourceLeftRegion_no_rawMark
    correct invariant guard region rawMarked

end SequentialFigure7

end ProofNetIR
