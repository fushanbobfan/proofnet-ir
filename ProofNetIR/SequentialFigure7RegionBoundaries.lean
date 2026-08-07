import ProofNetIR.SequentialFigure7BlockerHistory

namespace ProofNetIR

/-!
# Exact-run region boundaries for canonical Figure-7 histories

This module records the two narrow disjointness statements that are available
*after* an exact `FreshSourceLeftRun` has been supplied.

The run is an explicit theorem argument.  In particular, neither result below
constructs a run from `NewGuard`; using either theorem to establish the run
required by its own premise would be circular.  The statements therefore do
not prove `NewGuard` sufficiency, dispatcher progress, or worklist
completeness.

Historical touch provenance and current live-component ownership are not
disjoint in general.  Compile-checked canonical counterexamples live in
`ProofNetIRRegionBoundariesTests.lean`.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

/-- The exact carrier inspected by one successful source-left run: every
visited trace occurrence together with the terminal axiom partner.

This is deliberately run-indexed rather than the larger structural
`SourceLeftRegionVertex` relation. -/
def ExactFreshSourceLeftRunCarrier
    {certificate : Certificate} {state : UnificationState}
    {fuel : Nat} {tags : Array Bool} {start reached partner : Vertex}
    {trace : List Vertex} {linkIndex : Nat}
    (_run : FreshSourceLeftRun certificate state fuel tags start trace
      reached partner linkIndex)
    (vertex : Vertex) : Prop :=
  vertex ∈ trace ∨ vertex = partner

/-- Every occurrence in an exact run carrier is false-tagged in that run's
input tag array. -/
theorem carrierFresh
    {certificate : Certificate} {state : UnificationState}
    {fuel : Nat} {tags : Array Bool} {start reached partner : Vertex}
    {trace : List Vertex} {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate state fuel tags start trace
      reached partner linkIndex)
    {vertex : Vertex}
    (carrier : ExactFreshSourceLeftRunCarrier run vertex) :
    tags[vertex]? = some false := by
  rcases carrier with traceMembership | rfl
  · exact run.traceFresh traceMembership
  · exact run.partnerFresh

namespace CanonicalTagHistory

/-- An exact run over the current canonical tag carrier cannot inspect a
vertex touched by any prior reservation event in that history.

The explicit `run` premise is essential: this theorem consumes a successful
run and does not derive one from a shallow `NewGuard`. -/
theorem freshSourceLeftRun_carrier_not_touched
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {runState : UnificationState} {fuel : Nat}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate runState fuel state.tags start
      trace reached partner linkIndex)
    {vertex : Vertex}
    (carrier : ExactFreshSourceLeftRunCarrier run vertex) :
    ¬ tagHistory.Touched vertex := by
  intro touched
  have tagged : state.tags[vertex]? = some true :=
    tagHistory.tagged_iff_touched.2 touched
  have fresh : state.tags[vertex]? = some false :=
    carrierFresh run carrier
  rw [tagged] at fresh
  contradiction

end CanonicalTagHistory

/-- An exact run in the selected head's marked core cannot inspect an
occurrence that was already raw-marked and owned by a live component in the
input production core.

The selected ready head is handled separately because `markedCore` introduces
its one new raw mark.  Again, the exact `run` is a premise, not an output of
`NewGuard`; this theorem alone cannot establish run existence. -/
theorem carrier_not_exactMarkedOccurrenceOwner
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {fuel : Nat} {reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate guard.head.markedCore fuel
      before.tags guard.tensor.mate trace reached partner linkIndex)
    {vertex : Vertex}
    (carrier : ExactFreshSourceLeftRunCarrier run vertex) :
    ¬ ExactMarkedOccurrenceOwner certificate before.core vertex := by
  intro owner
  have runReady :
      guard.head.markedCore.marks[vertex]? = some none := by
    rcases carrier with traceMembership | rfl
    · exact run.traceReady traceMembership
    · exact run.partnerReady
  rcases owner with
    ⟨rawAge, _index, _component, _usedLinks, _owned, oldMarked,
      _representative, _componentLookup, _componentWitness, _accounted,
      _ownedMembership⟩
  by_cases selected : vertex = guard.head.vertex
  · subst vertex
    have selectedMarked :
        guard.head.markedCore.marks[guard.head.vertex]? =
          some (some guard.head.rawAge) :=
      (UnificationState.markReadyRaw?_exact
        (guard.head.core_mark_eq invariant)).2.2.2.2.2.2
    rw [selectedMarked] at runReady
    simp at runReady
  · have retainedMarked :
        guard.head.markedCore.marks[vertex]? = some (some rawAge) := by
      simpa [ReadyHeadInput.markedCore, Ne.symm selected] using oldMarked
    rw [retainedMarked] at runReady
    simp at runReady

end SequentialFigure7

end ProofNetIR
