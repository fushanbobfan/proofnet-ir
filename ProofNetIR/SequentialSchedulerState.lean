import ProofNetIR.SequentialRoute

namespace ProofNetIR

/-!
# Delayed sequential-scheduler state

This module specifies the first independent state layer corresponding to the
delayed `init`/`new` bookkeeping in Guerrini Figures 7--8.  Raw token ages are
kept distinct from future token representatives.  Waiting storage also
distinguishes an out-of-bounds lookup, an in-bounds undefined cell (`⊥`), and
an initialized empty cell (`∅`).

The two executable operations below only reserve a fresh raw age and enqueue
the reached/partner endpoints in that order.  They deliberately leave marks
unchanged.  This module does not prove later `NEXTAXIOM` totality, define the
full transition system, establish scheduler progress or completeness, remove
the recursive fallback, or prove a complexity bound.  The eager
`SequentialUnification.dynamicStartWithFuel?` operation remains a separate
Figure-5 refinement and is not used here.
-/

namespace SequentialSchedulerState

/-- The discovery-order age assigned when a delayed scheduler token is
reserved.  It is intentionally not a union-find representative. -/
abbrev RawTokenAge := Nat

/-- One fixed-capacity waiting-table cell.  `undefined` represents `⊥`, while
`initialized []` represents the distinct initialized empty set `∅`. -/
inductive WaitingCell where
  | undefined
  | initialized (vertices : List Vertex)
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- The paper-level `⊥` and initialized `∅` waiting states are distinct. -/
theorem WaitingCell.undefined_ne_initialized_empty :
    WaitingCell.undefined ≠ WaitingCell.initialized [] := by
  intro equation
  cases equation

/-- `sigma` is the strictly increasing stack of boundaries of contiguous raw
token-age intervals below `nextAge`. -/
structure SigmaAgePartition (nextAge : RawTokenAge)
    (sigma : List RawTokenAge) : Prop where
  empty_iff : sigma = [] ↔ nextAge = 0
  head_zero : 0 < nextAge → sigma.head? = some 0
  strictIncreasing : sigma.Pairwise (· < ·)
  boundary_lt : ∀ boundary ∈ sigma, boundary < nextAge

namespace SigmaAgePartition

/-- The unique partition at raw-age horizon zero. -/
theorem empty : SigmaAgePartition 0 [] := by
  exact {
    empty_iff := by simp
    head_zero := by
      intro impossible
      exact (Nat.not_lt_zero 0 impossible).elim
    strictIncreasing := by simp
    boundary_lt := by simp }

/-- Reserving the initial raw age produces the singleton boundary stack. -/
theorem reserveInitial : SigmaAgePartition 1 [0] := by
  exact {
    empty_iff := by simp
    head_zero := by simp
    strictIncreasing := by simp
    boundary_lt := by simp }

/-- Appending the current horizon reserves one new singleton interval. -/
theorem appendFresh
    {nextAge : RawTokenAge} {sigma : List RawTokenAge}
    (partition : SigmaAgePartition nextAge sigma)
    (positive : 0 < nextAge) :
    SigmaAgePartition (nextAge + 1) (sigma ++ [nextAge]) := by
  cases sigma with
  | nil =>
      have nextAgeZero : nextAge = 0 :=
        partition.empty_iff.mp rfl
      exact (Nat.ne_of_gt positive nextAgeZero).elim
  | cons first rest =>
      exact {
        empty_iff := by simp
        head_zero := by
          intro _
          simpa using partition.head_zero positive
        strictIncreasing := by
          rw [List.pairwise_append]
          refine ⟨partition.strictIncreasing, by simp, ?_⟩
          intro boundary boundaryMembership _ freshMembership
          simp only [List.mem_singleton] at freshMembership
          subst freshMembership
          exact partition.boundary_lt boundary boundaryMembership
        boundary_lt := by
          intro boundary membership
          simp only [List.mem_append, List.mem_singleton] at membership
          rcases membership with oldMembership | rfl
          · exact Nat.lt_trans
              (partition.boundary_lt boundary oldMembership)
              (Nat.lt_succ_self _)
          · exact Nat.lt_succ_self _ }

end SigmaAgePartition

/-- Greatest partition boundary not exceeding `age`.  The definition is
executable and uses raw ages directly. -/
def sigmaBoundary? : List RawTokenAge → RawTokenAge → Option RawTokenAge
  | [], _ => none
  | boundary :: rest, age =>
      if boundary ≤ age then
        match sigmaBoundary? rest age with
        | none => some boundary
        | some later => some later
      else
        none

/-- Appending the fresh raw-age boundary does not change any lookup strictly
below the old horizon. -/
theorem sigmaBoundary?_append_fresh_old
    {sigma : List RawTokenAge} {nextAge age : RawTokenAge}
    (ageBound : age < nextAge) :
    sigmaBoundary? (sigma ++ [nextAge]) age =
      sigmaBoundary? sigma age := by
  induction sigma with
  | nil =>
      simp [sigmaBoundary?, Nat.not_le_of_gt ageBound]
  | cons head tail induction =>
      simp [sigmaBoundary?, induction]

private theorem sigmaBoundary?_append_self_of_all_lt
    {sigma : List RawTokenAge} {nextAge : RawTokenAge}
    (allLt : ∀ boundary ∈ sigma, boundary < nextAge) :
    sigmaBoundary? (sigma ++ [nextAge]) nextAge = some nextAge := by
  induction sigma with
  | nil =>
      simp [sigmaBoundary?]
  | cons head tail induction =>
      have headLe : head ≤ nextAge :=
        Nat.le_of_lt (allLt head List.mem_cons_self)
      have tailLt : ∀ boundary ∈ tail, boundary < nextAge := by
        intro boundary membership
        exact allLt boundary (List.mem_cons_of_mem head membership)
      simp [sigmaBoundary?, headLe, induction tailLt]

/-- The boundary appended at the old horizon is exactly the boundary returned
for that freshly reserved raw age. -/
theorem SigmaAgePartition.sigmaBoundary?_append_fresh_self
    {nextAge : RawTokenAge} {sigma : List RawTokenAge}
    (partition : SigmaAgePartition nextAge sigma) :
    sigmaBoundary? (sigma ++ [nextAge]) nextAge = some nextAge := by
  exact sigmaBoundary?_append_self_of_all_lt partition.boundary_lt

/-- Every returned boundary comes from the supplied stack. -/
theorem sigmaBoundary?_mem
    {sigma : List RawTokenAge} {age boundary : RawTokenAge}
    (lookup : sigmaBoundary? sigma age = some boundary) :
    boundary ∈ sigma := by
  induction sigma with
  | nil =>
      simp [sigmaBoundary?] at lookup
  | cons head tail induction =>
      simp only [sigmaBoundary?] at lookup
      split at lookup
      · cases tailLookup : sigmaBoundary? tail age with
        | none =>
            simp [tailLookup] at lookup
            subst boundary
            exact List.mem_cons_self
        | some tailBoundary =>
            simp [tailLookup] at lookup
            subst boundary
            right
            exact induction tailLookup
      · simp at lookup

/-- Every returned boundary is at most the queried raw age. -/
theorem sigmaBoundary?_le
    {sigma : List RawTokenAge} {age boundary : RawTokenAge}
    (lookup : sigmaBoundary? sigma age = some boundary) :
    boundary ≤ age := by
  induction sigma with
  | nil =>
      simp [sigmaBoundary?] at lookup
  | cons head tail induction =>
      simp only [sigmaBoundary?] at lookup
      split at lookup
      next headLe =>
        cases tailLookup : sigmaBoundary? tail age with
        | none =>
            simp [tailLookup] at lookup
            subst boundary
            exact headLe
        | some tailBoundary =>
            simp [tailLookup] at lookup
            subst boundary
            exact induction tailLookup
      next headNotLe =>
        simp at lookup

/-- If an increasing boundary stack produces no result, none of its
boundaries is eligible for the queried age. -/
private theorem sigmaBoundary?_none_for_increasing
    {sigma : List RawTokenAge} {age : RawTokenAge}
    (increasing : sigma.Pairwise (· < ·))
    (lookup : sigmaBoundary? sigma age = none) :
    ∀ candidate ∈ sigma, ¬ candidate ≤ age := by
  induction sigma with
  | nil =>
      simp
  | cons head tail induction =>
      simp only [sigmaBoundary?] at lookup
      by_cases headLe : head ≤ age
      · cases tailLookup : sigmaBoundary? tail age <;>
          simp [headLe, tailLookup] at lookup
      · intro candidate membership candidateLe
        simp only [List.mem_cons] at membership
        rcases membership with rfl | inTail
        · exact headLe candidateLe
        · have headLtCandidate :
              head < candidate :=
            List.rel_of_pairwise_cons increasing inTail
          exact headLe (Nat.le_trans
            (Nat.le_of_lt headLtCandidate) candidateLe)

/-- On an increasing boundary stack, the executable result dominates every
other boundary that does not exceed the queried age. -/
theorem sigmaBoundary?_greatest
    {sigma : List RawTokenAge} {age boundary : RawTokenAge}
    (increasing : sigma.Pairwise (· < ·))
    (lookup : sigmaBoundary? sigma age = some boundary) :
    ∀ candidate ∈ sigma, candidate ≤ age → candidate ≤ boundary := by
  induction sigma with
  | nil =>
      simp
  | cons head tail induction =>
      simp only [sigmaBoundary?] at lookup
      split at lookup
      next headLe =>
        cases tailLookup : sigmaBoundary? tail age with
        | none =>
            simp [tailLookup] at lookup
            subst boundary
            intro candidate membership candidateLe
            simp only [List.mem_cons] at membership
            rcases membership with rfl | inTail
            · exact Nat.le_refl _
            · exact
                (sigmaBoundary?_none_for_increasing
                  increasing.tail tailLookup candidate inTail)
                  candidateLe |>.elim
        | some tailBoundary =>
            simp [tailLookup] at lookup
            subst boundary
            intro candidate membership candidateLe
            simp only [List.mem_cons] at membership
            rcases membership with rfl | inTail
            · exact Nat.le_of_lt
                (List.rel_of_pairwise_cons increasing
                  (sigmaBoundary?_mem tailLookup))
            · exact induction increasing.tail tailLookup
                candidate inTail candidateLe
      next headNotLe =>
        simp at lookup

/-- A nonempty partition always yields a boundary for any raw age below its
horizon (the head boundary `0` is already eligible). -/
theorem SigmaAgePartition.boundary_exists
    {nextAge : RawTokenAge} {sigma : List RawTokenAge}
    (partition : SigmaAgePartition nextAge sigma)
    {age : RawTokenAge} (ageBound : age < nextAge) :
    ∃ boundary, sigmaBoundary? sigma age = some boundary := by
  have positive : 0 < nextAge :=
    Nat.zero_lt_of_lt ageBound
  have headLookup := partition.head_zero positive
  rcases List.head?_eq_some_iff.mp headLookup with ⟨tail, rfl⟩
  cases tailLookup : sigmaBoundary? tail age with
  | none =>
      exact ⟨0, by simp [sigmaBoundary?, tailLookup]⟩
  | some boundary =>
      exact ⟨boundary, by simp [sigmaBoundary?, tailLookup]⟩

/-- The greatest eligible boundary is mathematically unique. -/
theorem sigmaBoundary_unique_of_greatest
    {sigma : List RawTokenAge} {age first second : RawTokenAge}
    (firstMem : first ∈ sigma) (firstLe : first ≤ age)
    (firstGreatest :
      ∀ candidate ∈ sigma, candidate ≤ age → candidate ≤ first)
    (secondMem : second ∈ sigma) (secondLe : second ≤ age)
    (secondGreatest :
      ∀ candidate ∈ sigma, candidate ≤ age → candidate ≤ second) :
    first = second := by
  exact Nat.le_antisymm
    (secondGreatest first firstMem firstLe)
    (firstGreatest second secondMem secondLe)

/-- Concrete Figures 7--8 bookkeeping before the transition system itself.
`waiting` is a fixed-capacity table: array lookup `none` means out of bounds,
`some undefined` means `⊥`, and `some (initialized [])` means `∅`. -/
structure SequentialStackState where
  marks : Array (Option RawTokenAge)
  nextAge : RawTokenAge
  sigma : List RawTokenAge
  ready : List (List Vertex)
  waiting : Array WaitingCell
  deriving Repr, DecidableEq

namespace SequentialStackState

/-- Empty fixed-carrier scheduler storage. -/
def empty (carrierSize : Nat) : SequentialStackState where
  marks := Array.replicate carrierSize none
  nextAge := 0
  sigma := []
  ready := []
  waiting := Array.replicate carrierSize .undefined

/-- Shape and age invariants for the delayed scheduler state.  This is
deliberately only a shape layer: it does not assert cross-bucket uniqueness,
semantic readiness, constraints on initialized waiting payloads, or an exact
domain correspondence between `waiting` and `sigma`. -/
structure WellShaped (state : SequentialStackState)
    (carrierSize : Nat) : Prop where
  marks_size : state.marks.size = carrierSize
  waiting_size : state.waiting.size = carrierSize
  assigned_age_bound :
    ∀ (vertex : Vertex) (age : RawTokenAge),
      state.marks[vertex]? = some (some age) →
      age < state.nextAge
  sigma_partition : SigmaAgePartition state.nextAge state.sigma
  ready_aligned : state.ready.length = state.sigma.length
  ready_nodup : ∀ bucket ∈ state.ready, bucket.Nodup
  ready_in_bounds :
    ∀ (bucket : List Vertex), bucket ∈ state.ready →
      ∀ (vertex : Vertex), vertex ∈ bucket → vertex < carrierSize
  nextAge_le_waiting : state.nextAge ≤ state.waiting.size

/-- Every reserved raw age addresses an actual waiting cell.  Thus an array
lookup returning `none` is an out-of-bounds fact and cannot be confused with
the in-bounds paper state `undefined`. -/
theorem WellShaped.waiting_lookup_exists
    {state : SequentialStackState} {carrierSize : Nat}
    (wellShaped : state.WellShaped carrierSize)
    {age : RawTokenAge} (ageBound : age < state.nextAge) :
    ∃ cell, state.waiting[age]? = some cell := by
  have waitingBound : age < state.waiting.size :=
    Nat.lt_of_lt_of_le ageBound wellShaped.nextAge_le_waiting
  exact ⟨state.waiting[age],
    Array.getElem?_eq_some_iff.mpr ⟨waitingBound, rfl⟩⟩

/-- The empty fixed-carrier state is well shaped. -/
theorem empty_wellShaped (carrierSize : Nat) :
    (empty carrierSize).WellShaped carrierSize := by
  exact {
    marks_size := by simp [empty]
    waiting_size := by simp [empty]
    assigned_age_bound := by
      intro vertex age lookup
      rcases Array.getElem?_eq_some_iff.mp lookup with
        ⟨vertexBound, value⟩
      simp [empty] at value
    sigma_partition := SigmaAgePartition.empty
    ready_aligned := by simp [empty]
    ready_nodup := by simp [empty]
    ready_in_bounds := by simp [empty]
    nextAge_le_waiting := by simp [empty] }

/-- Executable predicate asserting that every allocated occurrence is
unmarked. -/
def AllMarksUndefined (state : SequentialStackState) : Prop :=
  state.marks.all (fun mark => mark.isNone) = true

/-- Every allocated waiting-table cell is the paper-level `⊥`. -/
def AllWaitingUndefined (state : SequentialStackState) : Prop :=
  state.waiting.all (fun cell => cell == .undefined) = true

/-- Executable all-undefined marking implies the exact lookup fact at every
in-bounds occurrence. -/
theorem AllMarksUndefined.lookup
    {state : SequentialStackState} (allUndefined : AllMarksUndefined state)
    {vertex : Vertex} (vertexBound : vertex < state.marks.size) :
    state.marks[vertex]? = some none := by
  rw [Array.getElem?_eq_getElem vertexBound]
  have isNone :
      state.marks[vertex].isNone = true :=
    (Array.all_eq_true.mp allUndefined) vertex vertexBound
  simpa using isNone

/-- Executable all-undefined waiting storage implies the exact `⊥` lookup
fact at every in-bounds raw age. -/
theorem AllWaitingUndefined.lookup
    {state : SequentialStackState}
    (allUndefined : AllWaitingUndefined state)
    {age : RawTokenAge} (ageBound : age < state.waiting.size) :
    state.waiting[age]? = some .undefined := by
  rw [Array.getElem?_eq_getElem ageBound]
  have isUndefined :
      state.waiting[age] == WaitingCell.undefined :=
    (Array.all_eq_true.mp allUndefined) age ageBound
  simpa using isUndefined

/-- Local executable guard for the delayed initial reservation.  In
particular, `nextAge = 0` alone is not accepted as an empty local state: all
marks and waiting cells must be undefined, and both stacks must be empty.
Carrier agreement and the other global shape obligations remain the separate
precondition of `initEnqueue?_wellShaped`. -/
def InitReady (state : SequentialStackState)
    (reached partner : Vertex) : Prop :=
  state.nextAge = 0 ∧
  state.sigma = [] ∧
  state.ready = [] ∧
  AllMarksUndefined state ∧
  AllWaitingUndefined state ∧
  0 < state.waiting.size ∧
  reached < state.marks.size ∧
  partner < state.marks.size ∧
  reached ≠ partner

instance (state : SequentialStackState) (reached partner : Vertex) :
    Decidable (InitReady state reached partner) := by
  unfold InitReady AllMarksUndefined AllWaitingUndefined
  infer_instance

private def initAfter (state : SequentialStackState)
    (reached partner : Vertex) : SequentialStackState where
  marks := state.marks
  nextAge := 1
  sigma := [0]
  ready := [[reached, partner]]
  waiting := state.waiting

/-- Delayed Figure-7-style initialization.  It reserves raw age `0`, enqueues
the reached endpoint before its partner, and leaves both marks and `W(0)`
unchanged (`W(0)` remains `⊥`). -/
def initEnqueue? (state : SequentialStackState)
    (reached partner : Vertex) : Option SequentialStackState :=
  if InitReady state reached partner then
    some (initAfter state reached partner)
  else
    none

/-- Successful delayed initialization is exactly the strict initial
precondition together with the reserved state fields. -/
theorem initEnqueue?_some_iff
    {state after : SequentialStackState} {reached partner : Vertex} :
    initEnqueue? state reached partner = some after ↔
      InitReady state reached partner ∧
        after = initAfter state reached partner := by
  simp [initEnqueue?, eq_comm]

/-- Exact delayed-initialization fields. -/
theorem initEnqueue?_exact
    {state after : SequentialStackState} {reached partner : Vertex}
    (equation : initEnqueue? state reached partner = some after) :
    after.marks = state.marks ∧
    after.nextAge = 1 ∧
    after.sigma = [0] ∧
    after.ready = [[reached, partner]] ∧
    after.waiting = state.waiting ∧
    after.waiting[0]? = some .undefined := by
  rcases initEnqueue?_some_iff.mp equation with ⟨ready, rfl⟩
  rcases ready with
    ⟨nextAgeZero, sigmaEmpty, readyEmpty, allMarks, allWaiting,
      waitingPositive, reachedBound, partnerBound, distinct⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl,
    allWaiting.lookup waitingPositive⟩

/-- Delayed initialization leaves both enqueued endpoints unmarked. -/
theorem initEnqueue?_endpoint_unmarked
    {state after : SequentialStackState} {reached partner : Vertex}
    (equation : initEnqueue? state reached partner = some after) :
    after.marks[reached]? = some none ∧
      after.marks[partner]? = some none := by
  rcases initEnqueue?_some_iff.mp equation with ⟨ready, rfl⟩
  rcases ready with
    ⟨nextAgeZero, sigmaEmpty, readyEmpty, allMarks, allWaiting,
      waitingPositive, reachedBound, partnerBound, distinct⟩
  exact ⟨
    allMarks.lookup reachedBound,
    allMarks.lookup partnerBound⟩

/-- Delayed initialization preserves all shape invariants. -/
theorem initEnqueue?_wellShaped
    {state after : SequentialStackState} {carrierSize : Nat}
    {reached partner : Vertex}
    (wellShaped : state.WellShaped carrierSize)
    (equation : initEnqueue? state reached partner = some after) :
    after.WellShaped carrierSize := by
  rcases initEnqueue?_some_iff.mp equation with ⟨ready, rfl⟩
  rcases ready with
    ⟨nextAgeZero, sigmaEmpty, readyEmpty, allMarks, allWaiting,
      waitingPositive, reachedBound, partnerBound, distinct⟩
  have reachedCarrier : reached < carrierSize := by
    rw [← wellShaped.marks_size]
    exact reachedBound
  have partnerCarrier : partner < carrierSize := by
    rw [← wellShaped.marks_size]
    exact partnerBound
  exact {
    marks_size := wellShaped.marks_size
    waiting_size := wellShaped.waiting_size
    assigned_age_bound := by
      intro vertex age assigned
      change state.marks[vertex]? = some (some age) at assigned
      have vertexBound :=
        (Array.getElem?_eq_some_iff.mp assigned).1
      have undefined := allMarks.lookup vertexBound
      rw [undefined] at assigned
      cases Option.some.inj assigned
    sigma_partition := SigmaAgePartition.reserveInitial
    ready_aligned := by simp [initAfter]
    ready_nodup := by
      intro bucket membership
      change bucket ∈ [[reached, partner]] at membership
      simp only [List.mem_singleton] at membership
      subst bucket
      simp [distinct]
    ready_in_bounds := by
      intro bucket membership vertex vertexMembership
      change bucket ∈ [[reached, partner]] at membership
      simp only [List.mem_singleton] at membership
      subst bucket
      simp only [List.mem_cons, List.not_mem_nil, or_false] at vertexMembership
      rcases vertexMembership with rfl | rfl
      · exact reachedCarrier
      · exact partnerCarrier
    nextAge_le_waiting := by
      change 1 ≤ state.waiting.size
      exact waitingPositive }

/-- Local executable guard for reserving a later raw token age.  It does not
replace the global `WellShaped` precondition used by the preservation theorem,
nor does it assert that the endpoints are absent from older ready buckets. -/
def NewReady (state : SequentialStackState)
    (reached partner : Vertex) : Prop :=
  0 < state.nextAge ∧
  reached < state.marks.size ∧
  partner < state.marks.size ∧
  reached ≠ partner ∧
  state.marks[reached]? = some none ∧
  state.marks[partner]? = some none ∧
  state.waiting[state.nextAge]? = some .undefined

instance (state : SequentialStackState) (reached partner : Vertex) :
    Decidable (NewReady state reached partner) := by
  unfold NewReady
  infer_instance

private def newAfter (state : SequentialStackState)
    (reached partner : Vertex) : SequentialStackState where
  marks := state.marks
  nextAge := state.nextAge + 1
  sigma := state.sigma ++ [state.nextAge]
  ready := state.ready ++ [[reached, partner]]
  waiting :=
    state.waiting.setIfInBounds state.nextAge (.initialized [])

/-- Delayed `new` reservation at the current raw-age horizon. -/
def newEnqueue? (state : SequentialStackState)
    (reached partner : Vertex) : Option SequentialStackState :=
  if NewReady state reached partner then
    some (newAfter state reached partner)
  else
    none

/-- Successful delayed `new` reservation is exactly its local precondition
together with the state obtained by reserving the current raw-age horizon. -/
theorem newEnqueue?_some_iff
    {state after : SequentialStackState} {reached partner : Vertex} :
    newEnqueue? state reached partner = some after ↔
      NewReady state reached partner ∧
        after = newAfter state reached partner := by
  simp [newEnqueue?, eq_comm]

/-- Exact delayed-`new` fields, including the transition of the fresh waiting
cell from `⊥` to initialized `∅`. -/
theorem newEnqueue?_exact
    {state after : SequentialStackState} {reached partner : Vertex}
    (equation : newEnqueue? state reached partner = some after) :
    after.marks = state.marks ∧
    after.nextAge = state.nextAge + 1 ∧
    after.sigma = state.sigma ++ [state.nextAge] ∧
    after.ready = state.ready ++ [[reached, partner]] ∧
    after.waiting =
      state.waiting.setIfInBounds state.nextAge (.initialized []) ∧
    after.waiting[state.nextAge]? = some (.initialized []) := by
  rcases newEnqueue?_some_iff.mp equation with ⟨ready, rfl⟩
  rcases ready with
    ⟨positive, reachedBound, partnerBound, distinct, reachedUnmarked,
      partnerUnmarked, waitingFresh⟩
  have freshBound :
      state.nextAge < state.waiting.size :=
    (Array.getElem?_eq_some_iff.mp waitingFresh).1
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp [newAfter, freshBound]

/-- A delayed `new` reservation changes no non-fresh waiting cell. -/
theorem newEnqueue?_waiting_of_ne
    {state after : SequentialStackState} {reached partner : Vertex}
    {index : RawTokenAge}
    (equation : newEnqueue? state reached partner = some after)
    (different : index ≠ state.nextAge) :
    after.waiting[index]? = state.waiting[index]? := by
  rw [(newEnqueue?_exact equation).2.2.2.2.1]
  exact Array.getElem?_setIfInBounds_ne different.symm

/-- Delayed `new` leaves both newly enqueued endpoints unmarked. -/
theorem newEnqueue?_endpoint_unmarked
    {state after : SequentialStackState} {reached partner : Vertex}
    (equation : newEnqueue? state reached partner = some after) :
    after.marks[reached]? = some none ∧
      after.marks[partner]? = some none := by
  rcases newEnqueue?_some_iff.mp equation with ⟨ready, rfl⟩
  rcases ready with
    ⟨positive, reachedBound, partnerBound, distinct, reachedUnmarked,
      partnerUnmarked, waitingFresh⟩
  exact ⟨reachedUnmarked, partnerUnmarked⟩

/-- Reserving a later raw age preserves all state-shape invariants. -/
theorem newEnqueue?_wellShaped
    {state after : SequentialStackState} {carrierSize : Nat}
    {reached partner : Vertex}
    (wellShaped : state.WellShaped carrierSize)
    (equation : newEnqueue? state reached partner = some after) :
    after.WellShaped carrierSize := by
  rcases newEnqueue?_some_iff.mp equation with ⟨ready, rfl⟩
  rcases ready with
    ⟨positive, reachedBound, partnerBound, distinct, reachedUnmarked,
      partnerUnmarked, waitingFresh⟩
  have reachedCarrier : reached < carrierSize := by
    rw [← wellShaped.marks_size]
    exact reachedBound
  have partnerCarrier : partner < carrierSize := by
    rw [← wellShaped.marks_size]
    exact partnerBound
  have freshBound : state.nextAge < state.waiting.size :=
    (Array.getElem?_eq_some_iff.mp waitingFresh).1
  exact {
    marks_size := wellShaped.marks_size
    waiting_size := by simpa [newAfter] using wellShaped.waiting_size
    assigned_age_bound := by
      intro vertex age assigned
      have oldBound :=
        wellShaped.assigned_age_bound vertex age assigned
      exact Nat.lt_trans oldBound (Nat.lt_succ_self _)
    sigma_partition :=
      SigmaAgePartition.appendFresh wellShaped.sigma_partition positive
    ready_aligned := by
      simp [newAfter, wellShaped.ready_aligned]
    ready_nodup := by
      intro bucket membership
      change bucket ∈ state.ready ++ [[reached, partner]] at membership
      simp only [List.mem_append, List.mem_singleton] at membership
      rcases membership with oldMembership | rfl
      · exact wellShaped.ready_nodup bucket oldMembership
      · simp [distinct]
    ready_in_bounds := by
      intro bucket membership vertex vertexMembership
      change bucket ∈ state.ready ++ [[reached, partner]] at membership
      simp only [List.mem_append, List.mem_singleton] at membership
      rcases membership with oldMembership | rfl
      · exact wellShaped.ready_in_bounds bucket oldMembership
          vertex vertexMembership
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at vertexMembership
        rcases vertexMembership with rfl | rfl
        · exact reachedCarrier
        · exact partnerCarrier
    nextAge_le_waiting := by
      change state.nextAge + 1 ≤
        (state.waiting.setIfInBounds state.nextAge
          (.initialized [])).size
      simpa using (Nat.succ_le_of_lt freshBound) }

end SequentialStackState

end SequentialSchedulerState

end ProofNetIR
