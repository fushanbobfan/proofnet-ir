import ProofNetIR.SequentialFigure7QueueHistory
import ProofNetIR.SequentialFreshSourceBlocker

namespace ProofNetIR

/-!
# Canonical-history provenance for fresh source-left blockers

`SequentialFreshSourceBlocker` isolates the dynamic reasons why one exact
source-left run can fail: a visited/terminal-partner occurrence is already
tagged or is not raw-unmarked after the selected ready head is marked.  This
module classifies those dynamic failures against an authentic canonical
dispatcher history and the complete scheduler invariant.

Every blocker has at least one of three possibly overlapping provenance forms
needed by the remaining correctness argument:

* a prior initialization/`new` search touched the occurrence;
* the source-left region returns to the currently selected ready head; or
* an earlier raw mark has an occurrence-exact owner in one live component.

The classification deliberately does not eliminate any of these cases.  It
therefore proves no `NewGuard` sufficiency, progress, totality, worklist
completeness, fallback removal, or complexity bound.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

namespace NewGuard

/-- The opposite tensor premise selected by a shallow `NewGuard` belongs to
the certificate formula carrier. -/
theorem mate_bound
    {certificate : Certificate} {before : ReservationState}
    (guard : NewGuard certificate before) :
    guard.tensor.mate < certificate.formulas.size := by
  have wellFormed := guard.tensor_valid.2.2.1
  cases sideEquation : guard.tensor.side with
  | storedLeft =>
      simpa [TensorBelow.mate, TensorPremiseSide.mate, sideEquation] using
        wellFormed.2.2.2.2.1
  | storedRight =>
      simpa [TensorBelow.mate, TensorPremiseSide.mate, sideEquation] using
        wellFormed.2.2.2.1

end NewGuard

/-- Occurrence-exact ownership of one concrete raw-marked formula occurrence
by a current live production component.

The witness retains the raw age, its current representative slot, the exact
component lookup, the submitted-link/owned-occurrence derivation witness, and
membership of the named occurrence in that owned list. -/
def ExactMarkedOccurrenceOwner
    (certificate : Certificate) (state : UnificationState)
    (vertex : Vertex) : Prop :=
  ∃ (rawAge index : Nat) (component : UnificationComponent)
      (usedLinks owned : List Nat),
    state.marks[vertex]? = some (some rawAge) ∧
      state.representative rawAge = index ∧
        state.components[index]? = some (some component) ∧
          Certificate.ComponentOccurrenceWitness certificate component
            usedLinks owned ∧
            Certificate.OwnedOccurrenceAccounted state index component
              owned ∧
              vertex ∈ owned

/-- The component-forest field of the complete scheduler invariant resolves
every concrete raw mark to an exact live-component owner. -/
theorem SchedulerInvariant.exactMarkedOccurrenceOwner
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {vertex rawAge : Nat}
    (marked : state.core.marks[vertex]? = some (some rawAge)) :
    ExactMarkedOccurrenceOwner certificate state.core vertex := by
  rcases invariant.component_forest_provenance with
    ⟨usedAt, ownedAt, live, _disjoint, markedOwned⟩
  rcases markedOwned marked with
    ⟨index, component, representative, componentLookup, ownedMembership⟩
  rcases live componentLookup with ⟨componentWitness, accounted⟩
  exact ⟨rawAge, index, component, usedAt index, ownedAt index,
    marked, representative, componentLookup, componentWitness,
    accounted, ownedMembership⟩

/-- The history-level obstruction represented by one dynamically unavailable
source-left region occurrence.

The middle alternative is intentionally an equality with the currently
selected ready head: `ReadyHeadInput.markedCore` introduced precisely that
one new raw mark.  The final alternative refers to the input production core,
not the pure marked-core expression. -/
def CanonicalSourceLeftObstruction
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (guard : NewGuard certificate before) (vertex : Vertex) : Prop :=
  tagHistory.Touched vertex ∨
    vertex = guard.head.vertex ∨
      ExactMarkedOccurrenceOwner certificate before.core vertex

namespace CanonicalTagHistory

/-- A tag failure at any in-bounds source-left region occurrence is exactly a
prior initialization/`new` touch in the supplied canonical history. -/
theorem classifyFreshTagBlocker
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {vertex : Vertex}
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex)
    (tagBlocked : before.tags[vertex]? ≠ some false) :
    tagHistory.Touched vertex := by
  apply tagHistory.tagged_iff_touched.mp
  have vertexBound : vertex < certificate.formulas.size :=
    region.inBounds invariant.structural guard.mate_bound
  have tagBound : vertex < before.tags.size := by
    rw [invariant.tags_size]
    exact vertexBound
  have tagLookup :=
    Array.getElem?_eq_getElem (xs := before.tags) tagBound
  cases valueEq : before.tags[vertex] with
  | false =>
      exact False.elim
        (tagBlocked (by simpa [valueEq] using tagLookup))
  | true =>
      simpa [valueEq] using tagLookup

/-- A raw-mark failure in the pure marked-core input is either the one mark
introduced for the selected ready head, or a pre-existing occurrence-exact
live-component owner in the input production core. -/
theorem classifyFreshRawBlocker
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {vertex : Vertex}
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex)
    (markBlocked :
      guard.head.markedCore.marks[vertex]? ≠ some none) :
    vertex = guard.head.vertex ∨
      ExactMarkedOccurrenceOwner certificate before.core vertex := by
  have vertexBound : vertex < certificate.formulas.size :=
    region.inBounds invariant.structural guard.mate_bound
  have markedSize :
      guard.head.markedCore.marks.size = certificate.formulas.size := by
    simpa [ReadyHeadInput.markedCore] using
      invariant.core_abstractable.markArraySize
  have markedBound : vertex < guard.head.markedCore.marks.size := by
    rw [markedSize]
    exact vertexBound
  have rawMarked :
      ∃ rawAge,
        guard.head.markedCore.marks[vertex]? = some (some rawAge) := by
    have markedLookup :=
      Array.getElem?_eq_getElem
        (xs := guard.head.markedCore.marks) markedBound
    cases valueEq : guard.head.markedCore.marks[vertex] with
    | none =>
        exact False.elim
          (markBlocked (by simpa [valueEq] using markedLookup))
    | some rawAge =>
        exact ⟨rawAge, by simpa [valueEq] using markedLookup⟩
  by_cases selected : vertex = guard.head.vertex
  · exact Or.inl selected
  · right
    rcases rawMarked with ⟨rawAge, marked⟩
    have oldMarked :
        before.core.marks[vertex]? = some (some rawAge) := by
      simpa [ReadyHeadInput.markedCore, Ne.symm selected] using marked
    exact SchedulerInvariant.exactMarkedOccurrenceOwner invariant oldMarked

/-- Classify one dynamic fresh-source blocker against an exact canonical
history.

Tag-domain and raw-mark-domain bounds come from the complete scheduler
invariant.  A false-tag failure is therefore an exact prior touch.  A
marked-core failure is either the one mark introduced for the selected ready
head, or a pre-existing raw mark with occurrence-exact component ownership.
No branch is ruled out here. -/
theorem classifyFreshSourceBlocker
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (blocker :
      FreshSourceBlocker certificate guard.head.markedCore before.tags
        guard.tensor.mate) :
    CanonicalSourceLeftObstruction tagHistory guard blocker.vertex := by
  rcases blocker.unavailable with tagBlocked | markBlocked
  · exact Or.inl
      (tagHistory.classifyFreshTagBlocker invariant guard blocker.region
        tagBlocked)
  · rcases
        classifyFreshRawBlocker invariant guard blocker.region markBlocked with
      selected | owned
    · exact Or.inr (Or.inl selected)
    · exact Or.inr (Or.inr owned)

/-- For a canonical dispatcher history, the structural source-left
classification sharpens to either an exact formula-budget run or one region
occurrence carrying an explicit history/component obstruction. -/
theorem freshSourceLeftRun_or_obstruction
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before) :
    (∃ trace reached partner linkIndex,
      Nonempty
        (FreshSourceLeftRun certificate guard.head.markedCore
          certificate.formulas.size before.tags guard.tensor.mate trace
          reached partner linkIndex)) ∨
      ∃ vertex,
        SourceLeftRegionVertex certificate guard.tensor.mate vertex ∧
          CanonicalSourceLeftObstruction tagHistory guard vertex := by
  rcases
      invariant.structural.freshSourceLeftRun_or_blocker guard.mate_bound with
    run | blocker
  · exact Or.inl run
  · rcases blocker with ⟨blocker⟩
    exact Or.inr ⟨blocker.vertex, blocker.region,
      tagHistory.classifyFreshSourceBlocker invariant guard blocker⟩

/-- If all three canonical-history obstruction forms are excluded throughout
the structurally determined source-left region, the exact formula-budget run
exists.

The exclusion premise is the remaining geometric/history obligation.  This
theorem does not derive it from declarative correctness or reachability. -/
theorem freshSourceLeftRun_of_no_obstruction
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (clear :
      ∀ {vertex : Vertex},
        SourceLeftRegionVertex certificate guard.tensor.mate vertex →
          ¬ CanonicalSourceLeftObstruction tagHistory guard vertex) :
    ∃ trace reached partner linkIndex,
      Nonempty
        (FreshSourceLeftRun certificate guard.head.markedCore
          certificate.formulas.size before.tags guard.tensor.mate trace
          reached partner linkIndex) := by
  rcases tagHistory.freshSourceLeftRun_or_obstruction invariant guard with
    run | obstruction
  · exact run
  · rcases obstruction with ⟨vertex, region, blocked⟩
    exact False.elim (clear region blocked)

/-- Excluding the three exact canonical-history obstruction forms upgrades
the shallow `NewGuard` to the older route-based `NewInputNecessary` predicate.
The theorem assumes no executor equation or post-state. -/
theorem newInputNecessary_of_no_sourceLeftObstruction
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (clear :
      ∀ {vertex : Vertex},
        SourceLeftRegionVertex certificate guard.tensor.mate vertex →
          ¬ CanonicalSourceLeftObstruction tagHistory guard vertex) :
    NewInputNecessary certificate before := by
  rcases tagHistory.freshSourceLeftRun_of_no_obstruction invariant guard clear
      with ⟨trace, reached, partner, linkIndex, run⟩
  rcases run with ⟨run⟩
  exact ⟨{
    guard := guard
    route := run.toFreshSourceLeftRoute (Nat.le_refl _) }⟩

/-- Excluding the three exact canonical-history obstruction forms upgrades
the shallow `NewGuard` all the way to the established input-only `NewEnabled`
predicate.

This remains a conditional local theorem.  Until the `clear` premise is
derived for correct certified-reachable states, it is not `NewGuard`
sufficiency, dispatcher progress, or totality. -/
theorem newEnabled_of_no_sourceLeftObstruction
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (clear :
      ∀ {vertex : Vertex},
        SourceLeftRegionVertex certificate guard.tensor.mate vertex →
          ¬ CanonicalSourceLeftObstruction tagHistory guard vertex) :
    NewEnabled certificate before := by
  apply tagHistory.newEnabled_of_inputNecessary invariant
  exact tagHistory.newInputNecessary_of_no_sourceLeftObstruction
    invariant guard clear

end CanonicalTagHistory

end SequentialFigure7

end ProofNetIR
