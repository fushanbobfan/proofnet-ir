import ProofNetIR.SequentialRoute

namespace ProofNetIR

/-!
# Delayed sequential-scheduler state

This module specifies the first independent state layer corresponding to the
delayed `init`/`new` bookkeeping in Guerrini Figures 7--8.  Raw token ages are
kept distinct from future token representatives.  Waiting storage also
distinguishes an out-of-bounds lookup, an in-bounds undefined cell (`⊥`), and
an initialized empty cell (`∅`).

The reservation operations below reserve a fresh raw age and enqueue the
reached/partner endpoints in that order.  They deliberately leave marks
unchanged.  The literal printed `new` display and the operationally coherent
reservation are exposed separately; only the latter preserves the exact
waiting-domain invariant used by the production bridge.  This module does not
prove later `NEXTAXIOM` totality, define the full transition system, establish
scheduler progress or completeness, remove the recursive fallback, or prove a
complexity bound.  The eager `SequentialUnification.dynamicStartWithFuel?`
operation remains a separate Figure-5 refinement and is not used here.
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

/-- The active (last) boundary of a valid scheduler partition is returned
exactly when queried at its own raw age. -/
theorem SigmaAgePartition.sigmaBoundary?_eq_top
    {nextAge : RawTokenAge} {sigma : List RawTokenAge}
    (partition : SigmaAgePartition nextAge sigma)
    {active : RawTokenAge}
    (activeEquation : sigma.getLast? = some active) :
    sigmaBoundary? sigma active = some active := by
  rcases List.getLast?_eq_some_iff.mp activeEquation with
    ⟨sigmaPrefix, rfl⟩
  apply sigmaBoundary?_append_self_of_all_lt
  have increasing :
      (sigmaPrefix ++ [active]).Pairwise (· < ·) :=
    partition.strictIncreasing
  have cross := (List.pairwise_append.mp increasing).2.2
  intro boundary membership
  exact cross boundary membership active (by simp)

/-- Removing the active boundary from a partition with at least two explicit
tail boundaries leaves a valid partition at the unchanged raw-age horizon.
The horizon is an allocation counter, so a `unify` pop does not decrement it. -/
theorem SigmaAgePartition.popActive
    {nextAge : RawTokenAge}
    {sigma sigmaPrefix : List RawTokenAge}
    {previous active : RawTokenAge}
    (partition : SigmaAgePartition nextAge sigma)
    (sigmaEquation :
      sigma = sigmaPrefix ++ [previous, active]) :
    SigmaAgePartition nextAge (sigmaPrefix ++ [previous]) := by
  have positive : 0 < nextAge := by
    have activeMembership : active ∈ sigma := by
      rw [sigmaEquation]
      simp
    exact Nat.zero_lt_of_lt
      (partition.boundary_lt active activeMembership)
  have oldHead := partition.head_zero positive
  have oldIncreasing := partition.strictIncreasing
  rw [sigmaEquation] at oldHead oldIncreasing
  have reducedIncreasing :
      (sigmaPrefix ++ [previous]).Pairwise (· < ·) :=
    (List.pairwise_append.mp (by
      simpa [List.append_assoc] using oldIncreasing)).1
  exact {
    empty_iff := by
      constructor
      · intro impossible
        simp at impossible
      · intro nextAgeZero
        subst nextAge
        exact (Nat.not_lt_zero 0 positive).elim
    head_zero := by
      intro _
      simpa [List.append_assoc] using oldHead
    strictIncreasing := reducedIncreasing
    boundary_lt := by
      intro boundary membership
      apply partition.boundary_lt boundary
      rw [sigmaEquation]
      simp only [List.mem_append, List.mem_cons] at membership ⊢
      rcases membership with
        inPrefix | rfl | impossible
      · exact Or.inl inPrefix
      · exact Or.inr (Or.inl rfl)
      · simp at impossible }

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

/-- Every allocated raw age at or above the active (last) boundary resolves
to that active boundary.  This is the exact interval fact used by Figure-7
`forward`: a mate may have a younger raw age than the boundary itself while
still belonging to the active scheduler component. -/
theorem SigmaAgePartition.sigmaBoundary?_eq_top_of_le
    {nextAge : RawTokenAge} {sigma : List RawTokenAge}
    (partition : SigmaAgePartition nextAge sigma)
    {active age : RawTokenAge}
    (activeEquation : sigma.getLast? = some active)
    (activeLe : active ≤ age)
    (ageBound : age < nextAge) :
    sigmaBoundary? sigma age = some active := by
  rcases partition.boundary_exists ageBound with
    ⟨boundary, boundaryLookup⟩
  rcases List.getLast?_eq_some_iff.mp activeEquation with
    ⟨sigmaPrefix, sigmaEquation⟩
  have activeMembership : active ∈ sigma := by
    rw [sigmaEquation]
    simp
  have activeLeBoundary : active ≤ boundary :=
    sigmaBoundary?_greatest partition.strictIncreasing
      boundaryLookup active activeMembership activeLe
  have boundaryMembership : boundary ∈ sigma :=
    sigmaBoundary?_mem boundaryLookup
  have increasing :
      (sigmaPrefix ++ [active]).Pairwise (· < ·) := by
    simpa [sigmaEquation] using partition.strictIncreasing
  have boundaryLeActive : boundary ≤ active := by
    rw [sigmaEquation] at boundaryMembership
    simp only [List.mem_append, List.mem_singleton]
      at boundaryMembership
    rcases boundaryMembership with inPrefix | rfl
    · exact Nat.le_of_lt
        ((List.pairwise_append.mp increasing).2.2
          boundary inPrefix active (by simp))
    · exact Nat.le_refl _
  have boundaryEquation : boundary = active :=
    Nat.le_antisymm boundaryLeActive activeLeBoundary
  simpa [boundaryEquation] using boundaryLookup

/-- Popping the active boundary preserves every lookup strictly below it.
The exact two-boundary suffix keeps this transport tied to the scheduler's
raw-age stack rather than to an abstract representative. -/
theorem sigmaBoundary?_popActive_of_lt
    {sigma sigmaPrefix : List RawTokenAge}
    {previous active age : RawTokenAge}
    (sigmaEquation :
      sigma = sigmaPrefix ++ [previous, active])
    (ageLtActive : age < active) :
    sigmaBoundary? (sigmaPrefix ++ [previous]) age =
      sigmaBoundary? sigma age := by
  rw [sigmaEquation]
  rw [show sigmaPrefix ++ [previous, active] =
      (sigmaPrefix ++ [previous]) ++ [active] by
        simp [List.append_assoc]]
  exact (sigmaBoundary?_append_fresh_old ageLtActive).symm

/-- After popping the active boundary, every allocated raw age at or above
that removed boundary resolves to the previous boundary.  The allocation
horizon is unchanged by the pop, so `ageBound` still ranges over the old
allocated carrier. -/
theorem SigmaAgePartition.sigmaBoundary?_popActive_eq_previous_of_active_le
    {nextAge : RawTokenAge}
    {sigma sigmaPrefix : List RawTokenAge}
    {previous active age : RawTokenAge}
    (partition : SigmaAgePartition nextAge sigma)
    (sigmaEquation :
      sigma = sigmaPrefix ++ [previous, active])
    (activeLe : active ≤ age)
    (ageBound : age < nextAge) :
    sigmaBoundary? (sigmaPrefix ++ [previous]) age =
      some previous := by
  have previousLtActive : previous < active := by
    have increasing := partition.strictIncreasing
    rw [sigmaEquation] at increasing
    simpa using (List.pairwise_append.mp increasing).2.1
  have reduced :
      SigmaAgePartition nextAge (sigmaPrefix ++ [previous]) :=
    partition.popActive sigmaEquation
  exact reduced.sigmaBoundary?_eq_top_of_le
    (by simp)
    (Nat.le_trans (Nat.le_of_lt previousLtActive) activeLe)
    ageBound

/-- A raw age between the two top adjacent scheduler boundaries resolves to
the previous boundary.  This is the exact interval fact needed by Figure-7
`unify`: if `sigma = prefix ++ [j, i]` and `j ≤ age < i`, then `age`
belongs to the component represented by `j`, not the active component `i`.

The allocation horizon is unchanged when the active boundary is popped, so
the proof first removes `i` from the valid partition and then reuses the
top-boundary interval theorem on the resulting stack. -/
theorem SigmaAgePartition.sigmaBoundary?_eq_previous_of_between
    {nextAge : RawTokenAge}
    {sigma sigmaPrefix : List RawTokenAge}
    {previous active age : RawTokenAge}
    (partition : SigmaAgePartition nextAge sigma)
    (sigmaEquation :
      sigma = sigmaPrefix ++ [previous, active])
    (previousLe : previous ≤ age)
    (ageLtActive : age < active) :
    sigmaBoundary? sigma age = some previous := by
  have reduced :
      SigmaAgePartition nextAge (sigmaPrefix ++ [previous]) :=
    partition.popActive sigmaEquation
  have activeMembership : active ∈ sigma := by
    rw [sigmaEquation]
    simp
  have ageBound : age < nextAge :=
    Nat.lt_trans ageLtActive
      (partition.boundary_lt active activeMembership)
  rw [sigmaEquation]
  rw [show sigmaPrefix ++ [previous, active] =
      (sigmaPrefix ++ [previous]) ++ [active] by
        simp [List.append_assoc]]
  rw [sigmaBoundary?_append_fresh_old ageLtActive]
  exact reduced.sigmaBoundary?_eq_top_of_le
    (by simp) previousLe ageBound

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

/-- The vertices currently stored in one waiting cell.  Paper-level
`undefined` contributes no payload, while an initialized cell contributes its
complete stored list. -/
def WaitingCell.vertices : WaitingCell → List Vertex
  | .undefined => []
  | .initialized vertices => vertices

/-- All waiting payloads in raw-age order. -/
def waitingVertices (state : SequentialStackState) : List Vertex :=
  state.waiting.toList.flatMap WaitingCell.vertices

/-- Every occurrence currently stored by either the ready stack or the waiting
table.  This is the executable domain against which later enqueue operations
must check global absence.  Semantic ownership and uniqueness remain separate
history invariants. -/
def queuedVertices (state : SequentialStackState) : List Vertex :=
  state.ready.flatten ++ state.waitingVertices

/-- Prepend one conclusion to an already initialized waiting bucket.

This is the exact constant-time payload update used by the local Figure-7
`wait` slice.  It fails closed on an out-of-bounds lookup and on the distinct
paper-level undefined cell `⊥`; an initialized empty bucket `∅` succeeds.
Global queue ownership is deliberately not checked by this primitive. -/
def prependWaiting? (state : SequentialStackState)
    (boundary : RawTokenAge) (conclusion : Vertex) :
    Option SequentialStackState :=
  match state.waiting[boundary]? with
  | some (.initialized payload) =>
      some {
        state with
        waiting :=
          state.waiting.setIfInBounds boundary
            (.initialized (conclusion :: payload)) }
  | _ => none

/-- Proof-relevant exact specification of one successful waiting prepend. -/
structure PrependWaitingStep (before after : SequentialStackState)
    (boundary : RawTokenAge) (conclusion : Vertex) : Type where
  payload : List Vertex
  initialized :
    before.waiting[boundary]? = some (.initialized payload)
  after_eq :
    after = {
      before with
      waiting :=
        before.waiting.setIfInBounds boundary
          (.initialized (conclusion :: payload)) }

/-- Waiting prepend succeeds exactly on an initialized in-bounds bucket. -/
theorem prependWaiting?_some_iff
    {before after : SequentialStackState}
    {boundary : RawTokenAge} {conclusion : Vertex} :
    before.prependWaiting? boundary conclusion = some after ↔
      Nonempty
        (PrependWaitingStep before after boundary conclusion) := by
  constructor
  · intro equation
    unfold prependWaiting? at equation
    cases lookup : before.waiting[boundary]? with
    | none =>
        simp [lookup] at equation
    | some cell =>
        cases cell with
        | undefined =>
            simp [lookup] at equation
        | initialized payload =>
            simp [lookup] at equation
            subst after
            exact ⟨{
              payload
              initialized := lookup
              after_eq := rfl }⟩
  · rintro ⟨step⟩
    rcases step with ⟨payload, initialized, rfl⟩
    simp [prependWaiting?, initialized]

/-- Exact changed and unchanged fields of a successful waiting prepend. -/
theorem prependWaiting?_exact
    {before after : SequentialStackState}
    {boundary : RawTokenAge} {conclusion : Vertex}
    (equation :
      before.prependWaiting? boundary conclusion = some after) :
    ∃ payload,
      before.waiting[boundary]? = some (.initialized payload) ∧
      after.waiting =
        before.waiting.setIfInBounds boundary
          (.initialized (conclusion :: payload)) ∧
      after.waiting[boundary]? =
        some (.initialized (conclusion :: payload)) ∧
      after.marks = before.marks ∧
      after.nextAge = before.nextAge ∧
      after.sigma = before.sigma ∧
      after.ready = before.ready := by
  rcases prependWaiting?_some_iff.mp equation with ⟨step⟩
  rcases step with ⟨payload, initialized, rfl⟩
  have boundaryBound : boundary < before.waiting.size :=
    (Array.getElem?_eq_some_iff.mp initialized).1
  exact ⟨payload, initialized, rfl, by simp [boundaryBound],
    rfl, rfl, rfl, rfl⟩

/-- A waiting prepend changes no bucket at a different raw-age index. -/
theorem prependWaiting?_of_ne
    {before after : SequentialStackState}
    {boundary other : RawTokenAge} {conclusion : Vertex}
    (equation :
      before.prependWaiting? boundary conclusion = some after)
    (different : other ≠ boundary) :
    after.waiting[other]? = before.waiting[other]? := by
  rcases prependWaiting?_exact equation with
    ⟨payload, initialized, waitingEquation, _, _⟩
  rw [waitingEquation]
  exact Array.getElem?_setIfInBounds_ne different.symm

/-- Prepend one conclusion to the current (last) ready bucket.

This local primitive deliberately performs no global queued-occurrence scan.
Its preservation theorem below therefore receives the exact local
duplicate-freedom and carrier-bound facts as proof inputs. -/
def prependReadyTop? (state : SequentialStackState)
    (conclusion : Vertex) : Option SequentialStackState :=
  match state.ready.getLast? with
  | none => none
  | some activeReady =>
      some {
        state with
        ready :=
          state.ready.dropLast ++ [conclusion :: activeReady] }

/-- Proof-relevant exact specification of one successful ready-top prepend. -/
structure PrependReadyTopStep (before after : SequentialStackState)
    (conclusion : Vertex) : Type where
  readyPrefix : List (List Vertex)
  activeReady : List Vertex
  ready_eq : before.ready = readyPrefix ++ [activeReady]
  after_eq :
    after = {
      before with
      ready := readyPrefix ++ [conclusion :: activeReady] }

/-- Ready-top prepend succeeds exactly when the ready stack is nonempty. -/
theorem prependReadyTop?_some_iff
    {before after : SequentialStackState} {conclusion : Vertex} :
    before.prependReadyTop? conclusion = some after ↔
      Nonempty (PrependReadyTopStep before after conclusion) := by
  constructor
  · intro equation
    unfold prependReadyTop? at equation
    cases lookup : before.ready.getLast? with
    | none =>
        simp [lookup] at equation
    | some activeReady =>
        simp [lookup] at equation
        subst after
        rcases List.getLast?_eq_some_iff.mp lookup with
          ⟨readyPrefix, readyEquation⟩
        exact ⟨{
          readyPrefix
          activeReady
          ready_eq := readyEquation
          after_eq := by
            rw [readyEquation]
            simp }⟩
  · rintro ⟨step⟩
    rcases step with
      ⟨readyPrefix, activeReady, readyEquation, rfl⟩
    simp [prependReadyTop?, readyEquation]

/-- Exact changed and unchanged fields of a successful ready-top prepend. -/
theorem prependReadyTop?_exact
    {before after : SequentialStackState} {conclusion : Vertex}
    (equation : before.prependReadyTop? conclusion = some after) :
    ∃ readyPrefix activeReady,
      before.ready = readyPrefix ++ [activeReady] ∧
      after.ready =
        readyPrefix ++ [conclusion :: activeReady] ∧
      after.marks = before.marks ∧
      after.nextAge = before.nextAge ∧
      after.sigma = before.sigma ∧
      after.waiting = before.waiting := by
  rcases prependReadyTop?_some_iff.mp equation with ⟨step⟩
  rcases step with
    ⟨readyPrefix, activeReady, readyEquation, rfl⟩
  exact ⟨readyPrefix, activeReady, readyEquation, rfl,
    rfl, rfl, rfl, rfl⟩

/-- Merge the two top scheduler buckets at an exact previous boundary.

The deterministic list refinement is
`conclusion :: (payload ++ previousReady ++ activeReady)`: Guerrini's paper
uses sets inside its ready/waiting cells, so this list order is a project
choice fixed here for executable reproducibility.  The operation drains
`W(previousBoundary)`, makes that cell undefined because it becomes active,
and pops only the active `sigma`/ready level.  It performs no global
`queuedVertices` scan. -/
def mergeTopReadyWaiting? (state : SequentialStackState)
    (previousBoundary : RawTokenAge) (conclusion : Vertex) :
    Option SequentialStackState :=
  match state.sigma.getLast?,
      state.sigma.dropLast.getLast?,
      state.ready.getLast?,
      state.ready.dropLast.getLast?,
      state.waiting[previousBoundary]? with
  | some _activeBoundary, some actualPrevious,
      some activeReady, some previousReady,
      some (.initialized payload) =>
      if actualPrevious == previousBoundary then
        some {
          state with
          sigma := state.sigma.dropLast
          ready :=
            state.ready.dropLast.dropLast ++
              [conclusion ::
                (payload ++ previousReady ++ activeReady)]
          waiting :=
            state.waiting.setIfInBounds previousBoundary
              .undefined }
      else
        none
  | _, _, _, _, _ => none

/-- Proof-relevant exact specification of one successful two-level merge. -/
structure MergeTopReadyWaitingStep
    (before after : SequentialStackState)
    (previousBoundary : RawTokenAge) (conclusion : Vertex) : Type where
  sigmaPrefix : List RawTokenAge
  activeBoundary : RawTokenAge
  readyPrefix : List (List Vertex)
  previousReady : List Vertex
  activeReady : List Vertex
  payload : List Vertex
  sigma_eq :
    before.sigma =
      sigmaPrefix ++ [previousBoundary, activeBoundary]
  ready_eq :
    before.ready =
      readyPrefix ++ [previousReady, activeReady]
  waiting_initialized :
    before.waiting[previousBoundary]? =
      some (.initialized payload)
  after_eq :
    after = {
      before with
      sigma := sigmaPrefix ++ [previousBoundary]
      ready :=
        readyPrefix ++
          [conclusion ::
            (payload ++ previousReady ++ activeReady)]
      waiting :=
        before.waiting.setIfInBounds previousBoundary
          .undefined }

/-- The two-level merge succeeds exactly when both stacks expose two levels,
the requested boundary is the previous `sigma` boundary, and its waiting cell
is initialized. -/
theorem mergeTopReadyWaiting?_some_iff
    {before after : SequentialStackState}
    {previousBoundary : RawTokenAge} {conclusion : Vertex} :
    before.mergeTopReadyWaiting? previousBoundary conclusion =
        some after ↔
      Nonempty
        (MergeTopReadyWaitingStep before after
          previousBoundary conclusion) := by
  constructor
  · intro equation
    unfold mergeTopReadyWaiting? at equation
    split at equation <;> try contradiction
    next activeBoundary actualPrevious activeReady previousReady payload
        activeLookup previousLookup activeReadyLookup
        previousReadyLookup waitingLookup =>
      split at equation
      next same =>
        have previousEquation :
            actualPrevious = previousBoundary := by
          simpa using same
        subst actualPrevious
        simp at equation
        subst after
        rcases List.getLast?_eq_some_iff.mp activeLookup with
          ⟨activePrefix, sigmaEquation⟩
        have sigmaDrop :
            before.sigma.dropLast = activePrefix := by
          rw [sigmaEquation]
          simp
        rw [sigmaDrop] at previousLookup
        rcases List.getLast?_eq_some_iff.mp previousLookup with
          ⟨sigmaPrefix, activePrefixEquation⟩
        rcases List.getLast?_eq_some_iff.mp activeReadyLookup with
          ⟨activeReadyPrefix, readyEquation⟩
        have readyDrop :
            before.ready.dropLast = activeReadyPrefix := by
          rw [readyEquation]
          simp
        rw [readyDrop] at previousReadyLookup
        rcases List.getLast?_eq_some_iff.mp previousReadyLookup with
          ⟨readyPrefix, activeReadyPrefixEquation⟩
        have fullSigmaEquation :
            before.sigma =
              sigmaPrefix ++
                [previousBoundary, activeBoundary] := by
          calc
            before.sigma =
                activePrefix ++ [activeBoundary] :=
              sigmaEquation
            _ =
                sigmaPrefix ++
                  [previousBoundary, activeBoundary] := by
              rw [activePrefixEquation]
              simp [List.append_assoc]
        have fullReadyEquation :
            before.ready =
              readyPrefix ++ [previousReady, activeReady] := by
          calc
            before.ready =
                activeReadyPrefix ++ [activeReady] :=
              readyEquation
            _ =
                readyPrefix ++
                  [previousReady, activeReady] := by
              rw [activeReadyPrefixEquation]
              simp [List.append_assoc]
        exact ⟨{
          sigmaPrefix
          activeBoundary
          readyPrefix
          previousReady
          activeReady
          payload
          sigma_eq := fullSigmaEquation
          ready_eq := fullReadyEquation
          waiting_initialized := waitingLookup
          after_eq := by
            simp [fullSigmaEquation, fullReadyEquation,
              List.append_assoc] }⟩
      next different =>
        simp at equation
  · rintro ⟨step⟩
    rcases step with
      ⟨sigmaPrefix, activeBoundary, readyPrefix,
        previousReady, activeReady, payload,
        sigmaEquation, readyEquation, waitingInitialized, rfl⟩
    simp [mergeTopReadyWaiting?, sigmaEquation, readyEquation,
      waitingInitialized, List.append_assoc]

/-- Exact changed and unchanged fields of a successful two-level merge. -/
theorem mergeTopReadyWaiting?_exact
    {before after : SequentialStackState}
    {previousBoundary : RawTokenAge} {conclusion : Vertex}
    (equation :
      before.mergeTopReadyWaiting? previousBoundary conclusion =
        some after) :
    ∃ sigmaPrefix activeBoundary readyPrefix previousReady
        activeReady payload,
      before.sigma =
        sigmaPrefix ++ [previousBoundary, activeBoundary] ∧
      before.ready =
        readyPrefix ++ [previousReady, activeReady] ∧
      before.waiting[previousBoundary]? =
        some (.initialized payload) ∧
      after.sigma = sigmaPrefix ++ [previousBoundary] ∧
      after.ready =
        readyPrefix ++
          [conclusion ::
            (payload ++ previousReady ++ activeReady)] ∧
      after.waiting =
        before.waiting.setIfInBounds previousBoundary
          .undefined ∧
      after.waiting[previousBoundary]? = some .undefined ∧
      after.marks = before.marks ∧
      after.nextAge = before.nextAge := by
  rcases mergeTopReadyWaiting?_some_iff.mp equation with ⟨step⟩
  rcases step with
    ⟨sigmaPrefix, activeBoundary, readyPrefix,
      previousReady, activeReady, payload,
      sigmaEquation, readyEquation, waitingInitialized, rfl⟩
  have boundaryBound :
      previousBoundary < before.waiting.size :=
    (Array.getElem?_eq_some_iff.mp waitingInitialized).1
  exact ⟨sigmaPrefix, activeBoundary, readyPrefix,
    previousReady, activeReady, payload,
    sigmaEquation, readyEquation, waitingInitialized,
    rfl, rfl, rfl, by simp [boundaryBound], rfl, rfl⟩

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

/-- The waiting-table cell at `age` has been initialized, with an arbitrary
current payload.  This intentionally distinguishes initialized empty `∅` from
paper-level undefined `⊥`. -/
def WaitingInitializedAt (state : SequentialStackState)
    (age : RawTokenAge) : Prop :=
  ∃ payload, state.waiting[age]? = some (.initialized payload)

/-- Operational waiting-domain alignment for the sequential scheduler.

Among allocated raw ages, initialized waiting cells are exactly the inactive
`sigma` boundaries.  The current active boundary (the last element of
`sigma`) is therefore still `⊥`; an age outside the allocated horizon is
handled separately by the executable fresh-cell guard.

This is the coherent invariant needed by `wait`/`unify`.  Guerrini's printed
Figure 7 writes `W[j ↦ ∅]` at the freshly pushed age, but the surrounding prose
defines `W` on nonactive boundaries and `unify` reads the old boundary.  The
literal printed transition is retained below for auditability, while the
production bridge uses the operational transition proved to preserve this
invariant. -/
structure OperationalWaitingDomain
    (state : SequentialStackState) : Prop where
  initialized_iff_inactive :
    ∀ {age : RawTokenAge}, age < state.nextAge →
      (state.WaitingInitializedAt age ↔ age ∈ state.sigma.dropLast)

/-- In a two-level scheduler state, any allocated waiting cell that actually
contains an occurrence lies strictly before the previous boundary when that
previous boundary is initialized empty.  The explicit allocation bound is
necessary because `OperationalWaitingDomain` intentionally constrains only
raw ages below `nextAge`; arbitrary fixed-capacity cells beyond that horizon
are outside its contract. -/
theorem OperationalWaitingDomain.payload_boundary_lt_previous
    {state : SequentialStackState}
    (domain : state.OperationalWaitingDomain)
    (partition : SigmaAgePartition state.nextAge state.sigma)
    {sigmaPrefix : List RawTokenAge}
    {previous active boundary : RawTokenAge}
    {payload : List Vertex} {conclusion : Vertex}
    (sigmaEquation :
      state.sigma = sigmaPrefix ++ [previous, active])
    (previousEmpty :
      state.waiting[previous]? = some (.initialized []))
    (boundaryBound : boundary < state.nextAge)
    (waitingLookup :
      state.waiting[boundary]? = some (.initialized payload))
    (conclusionMembership : conclusion ∈ payload) :
    boundary < previous := by
  have inactiveMembership :
      boundary ∈ state.sigma.dropLast :=
    (domain.initialized_iff_inactive boundaryBound).mp
      ⟨payload, waitingLookup⟩
  have reducedMembership :
      boundary ∈ sigmaPrefix ++ [previous] := by
    rw [sigmaEquation] at inactiveMembership
    simpa [List.append_assoc] using inactiveMembership
  have increasing := partition.strictIncreasing
  rw [sigmaEquation] at increasing
  have prefixBeforeSuffix :=
    (List.pairwise_append.mp increasing).2.2
  simp only [List.mem_append, List.mem_singleton]
    at reducedMembership
  rcases reducedMembership with inPrefix | rfl
  · exact prefixBeforeSuffix boundary inPrefix previous (by simp)
  · have payloadEquation : payload = [] := by
      exact WaitingCell.initialized.inj
        (Option.some.inj (waitingLookup.symm.trans previousEmpty))
    subst payload
    simp at conclusionMembership

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

/-- In a well-shaped operational state, the active `sigma` boundary is the
paper-level undefined waiting cell. -/
theorem OperationalWaitingDomain.active_undefined
    {state : SequentialStackState} {carrierSize : Nat}
    (domain : state.OperationalWaitingDomain)
    (wellShaped : state.WellShaped carrierSize)
    {active : RawTokenAge}
    (activeEquation : state.sigma.getLast? = some active) :
    state.waiting[active]? = some .undefined := by
  have activeMembership : active ∈ state.sigma := by
    rcases List.getLast?_eq_some_iff.mp activeEquation with
      ⟨sigmaPrefix, sigmaEquation⟩
    rw [sigmaEquation]
    simp
  have activeBound : active < state.nextAge :=
    wellShaped.sigma_partition.boundary_lt active activeMembership
  have activeNotInactive : active ∉ state.sigma.dropLast := by
    rcases List.getLast?_eq_some_iff.mp activeEquation with
      ⟨sigmaPrefix, sigmaEquation⟩
    have increasing :
        (sigmaPrefix ++ [active]).Pairwise (· < ·) := by
      simpa [sigmaEquation] using
        wellShaped.sigma_partition.strictIncreasing
    have cross := (List.pairwise_append.mp increasing).2.2
    intro activeInPrefix
    have activeInPrefix' : active ∈ sigmaPrefix := by
      simpa [sigmaEquation] using activeInPrefix
    have activeLtSelf :=
      cross active activeInPrefix' active (by simp)
    exact Nat.lt_irrefl active activeLtSelf
  have notInitialized :
      ¬ state.WaitingInitializedAt active := by
    intro initialized
    exact activeNotInactive
      ((OperationalWaitingDomain.initialized_iff_inactive
        domain activeBound).mp initialized)
  rcases wellShaped.waiting_lookup_exists activeBound with
    ⟨cell, cellEquation⟩
  cases cell with
  | undefined =>
      exact cellEquation
  | initialized payload =>
      exact False.elim (notInitialized ⟨payload, cellEquation⟩)

/-- Waiting prepend preserves scheduler shape; it changes only one payload
inside an already initialized fixed-capacity cell. -/
theorem prependWaiting?_wellShaped
    {before after : SequentialStackState} {carrierSize : Nat}
    {boundary : RawTokenAge} {conclusion : Vertex}
    (wellShaped : before.WellShaped carrierSize)
    (equation :
      before.prependWaiting? boundary conclusion = some after) :
    after.WellShaped carrierSize := by
  rcases prependWaiting?_some_iff.mp equation with ⟨step⟩
  rcases step with ⟨payload, initialized, rfl⟩
  exact {
    marks_size := wellShaped.marks_size
    waiting_size := by
      simpa using wellShaped.waiting_size
    assigned_age_bound := wellShaped.assigned_age_bound
    sigma_partition := wellShaped.sigma_partition
    ready_aligned := wellShaped.ready_aligned
    ready_nodup := wellShaped.ready_nodup
    ready_in_bounds := wellShaped.ready_in_bounds
    nextAge_le_waiting := by
      simpa using wellShaped.nextAge_le_waiting }

/-- Waiting prepend preserves the exact initialized waiting domain. -/
theorem prependWaiting?_operationalWaitingDomain
    {before after : SequentialStackState}
    {boundary : RawTokenAge} {conclusion : Vertex}
    (domain : before.OperationalWaitingDomain)
    (equation :
      before.prependWaiting? boundary conclusion = some after) :
    after.OperationalWaitingDomain := by
  rcases prependWaiting?_some_iff.mp equation with ⟨step⟩
  rcases step with ⟨payload, initialized, rfl⟩
  have boundaryBound : boundary < before.waiting.size :=
    (Array.getElem?_eq_some_iff.mp initialized).1
  exact {
    initialized_iff_inactive := by
      intro age ageBound
      have oldDomain :=
        domain.initialized_iff_inactive ageBound
      by_cases same : age = boundary
      · subst age
        constructor
        · intro _
          exact oldDomain.mp ⟨payload, initialized⟩
        · intro _
          exact ⟨conclusion :: payload, by
            simp [boundaryBound]⟩
      · constructor
        · rintro ⟨stored, storedEquation⟩
          apply oldDomain.mp
          exact ⟨stored, by
            rw [Array.getElem?_setIfInBounds_ne (Ne.symm same)]
                at storedEquation
            exact storedEquation⟩
        · intro inactive
          rcases oldDomain.mpr inactive with
            ⟨stored, storedEquation⟩
          exact ⟨stored, by
            rw [Array.getElem?_setIfInBounds_ne (Ne.symm same)]
            exact storedEquation⟩ }

/-- Ready-top prepend preserves scheduler shape from explicit local
duplicate-freedom and carrier-bound evidence.  No global queue ownership is
claimed or searched for. -/
theorem prependReadyTop?_wellShaped
    {before after : SequentialStackState} {carrierSize : Nat}
    {conclusion : Vertex}
    (wellShaped : before.WellShaped carrierSize)
    (equation :
      before.prependReadyTop? conclusion = some after)
    (conclusionBound : conclusion < carrierSize)
    (mergedNodup :
      ∀ {activeReady},
        before.ready.getLast? = some activeReady →
          (conclusion :: activeReady).Nodup) :
    after.WellShaped carrierSize := by
  rcases prependReadyTop?_some_iff.mp equation with ⟨step⟩
  rcases step with
    ⟨readyPrefix, activeReady, readyEquation, rfl⟩
  have activeLookup :
      before.ready.getLast? = some activeReady := by
    rw [readyEquation]
    simp
  have nextNodup :
      (conclusion :: activeReady).Nodup :=
    mergedNodup activeLookup
  exact {
    marks_size := wellShaped.marks_size
    waiting_size := wellShaped.waiting_size
    assigned_age_bound := wellShaped.assigned_age_bound
    sigma_partition := wellShaped.sigma_partition
    ready_aligned := by
      have oldAligned := wellShaped.ready_aligned
      rw [readyEquation] at oldAligned
      simpa using oldAligned
    ready_nodup := by
      intro bucket membership
      simp only [List.mem_append, List.mem_singleton]
        at membership
      rcases membership with inPrefix | rfl
      · apply wellShaped.ready_nodup bucket
        rw [readyEquation]
        exact List.mem_append_left _ inPrefix
      · exact nextNodup
    ready_in_bounds := by
      intro bucket membership vertex vertexMembership
      simp only [List.mem_append, List.mem_singleton]
        at membership
      rcases membership with inPrefix | rfl
      · apply wellShaped.ready_in_bounds bucket
          (by
            rw [readyEquation]
            exact List.mem_append_left _ inPrefix)
          vertex vertexMembership
      · simp only [List.mem_cons] at vertexMembership
        rcases vertexMembership with rfl | inActive
        · exact conclusionBound
        · apply wellShaped.ready_in_bounds activeReady
            (by rw [readyEquation]; simp)
            vertex inActive
    nextAge_le_waiting := wellShaped.nextAge_le_waiting }

/-- Ready-top prepend changes neither the boundary stack nor waiting storage,
so it preserves the operational waiting domain exactly. -/
theorem prependReadyTop?_operationalWaitingDomain
    {before after : SequentialStackState}
    {conclusion : Vertex}
    (domain : before.OperationalWaitingDomain)
    (equation :
      before.prependReadyTop? conclusion = some after) :
    after.OperationalWaitingDomain := by
  rcases prependReadyTop?_some_iff.mp equation with ⟨step⟩
  rcases step with
    ⟨readyPrefix, activeReady, readyEquation, rfl⟩
  exact {
    initialized_iff_inactive :=
      domain.initialized_iff_inactive }

/-- The two-level merge preserves scheduler shape when its newly assembled
bucket is explicitly duplicate-free, the newly queued conclusion is
in-bounds, and every drained waiting occurrence is in-bounds.  Existing ready
bucket bounds are inherited; no ownership theorem is inferred from a runtime
scan. -/
theorem mergeTopReadyWaiting?_wellShaped
    {before after : SequentialStackState} {carrierSize : Nat}
    {previousBoundary : RawTokenAge} {conclusion : Vertex}
    (wellShaped : before.WellShaped carrierSize)
    (equation :
      before.mergeTopReadyWaiting? previousBoundary conclusion =
        some after)
    (conclusionBound : conclusion < carrierSize)
    (payloadInBounds :
      ∀ {payload},
        before.waiting[previousBoundary]? =
            some (.initialized payload) →
          ∀ vertex ∈ payload, vertex < carrierSize)
    (mergedNodup :
      ∀ {previousReady activeReady payload},
        before.ready.dropLast.getLast? = some previousReady →
        before.ready.getLast? = some activeReady →
        before.waiting[previousBoundary]? =
            some (.initialized payload) →
          (conclusion ::
            (payload ++ previousReady ++ activeReady)).Nodup) :
    after.WellShaped carrierSize := by
  rcases mergeTopReadyWaiting?_some_iff.mp equation with ⟨step⟩
  rcases step with
    ⟨sigmaPrefix, activeBoundary, readyPrefix,
      previousReady, activeReady, payload,
      sigmaEquation, readyEquation, waitingInitialized, rfl⟩
  have previousReadyLookup :
      before.ready.dropLast.getLast? = some previousReady := by
    rw [readyEquation]
    simp
  have activeReadyLookup :
      before.ready.getLast? = some activeReady := by
    rw [readyEquation]
    simp
  have nextNodup :
      (conclusion ::
        (payload ++ previousReady ++ activeReady)).Nodup :=
    mergedNodup previousReadyLookup activeReadyLookup
      waitingInitialized
  have previousReadyMembership :
      previousReady ∈ before.ready := by
    rw [readyEquation]
    simp
  have activeReadyMembership :
      activeReady ∈ before.ready := by
    rw [readyEquation]
    simp
  have nextPartition :
      SigmaAgePartition before.nextAge
        (sigmaPrefix ++ [previousBoundary]) :=
    wellShaped.sigma_partition.popActive sigmaEquation
  exact {
    marks_size := wellShaped.marks_size
    waiting_size := by
      simpa using wellShaped.waiting_size
    assigned_age_bound := wellShaped.assigned_age_bound
    sigma_partition := nextPartition
    ready_aligned := by
      have oldAligned := wellShaped.ready_aligned
      rw [readyEquation] at oldAligned
      rw [sigmaEquation] at oldAligned
      simpa using oldAligned
    ready_nodup := by
      intro bucket membership
      simp only [List.mem_append, List.mem_singleton]
        at membership
      rcases membership with inPrefix | rfl
      · apply wellShaped.ready_nodup bucket
        rw [readyEquation]
        exact List.mem_append_left _ inPrefix
      · exact nextNodup
    ready_in_bounds := by
      intro bucket membership vertex vertexMembership
      simp only [List.mem_append, List.mem_singleton]
        at membership
      rcases membership with inPrefix | rfl
      · apply wellShaped.ready_in_bounds bucket
          (by
            rw [readyEquation]
            exact List.mem_append_left _ inPrefix)
          vertex vertexMembership
      · simp only [List.mem_cons, List.mem_append]
          at vertexMembership
        rcases vertexMembership with
          rfl | inPayloadOrPrevious | inActive
        · exact conclusionBound
        · rcases inPayloadOrPrevious with
            inPayload | inPrevious
          · exact payloadInBounds waitingInitialized
              vertex inPayload
          · exact wellShaped.ready_in_bounds previousReady
              previousReadyMembership vertex inPrevious
        · exact wellShaped.ready_in_bounds activeReady
            activeReadyMembership vertex inActive
    nextAge_le_waiting := by
      simpa using wellShaped.nextAge_le_waiting }

/-- Draining the previous initialized waiting bucket and making it the new
active boundary preserves the exact operational waiting domain. -/
theorem mergeTopReadyWaiting?_operationalWaitingDomain
    {before after : SequentialStackState}
    {previousBoundary : RawTokenAge} {conclusion : Vertex}
    (wellShaped : before.WellShaped before.marks.size)
    (domain : before.OperationalWaitingDomain)
    (equation :
      before.mergeTopReadyWaiting? previousBoundary conclusion =
        some after) :
    after.OperationalWaitingDomain := by
  rcases mergeTopReadyWaiting?_some_iff.mp equation with ⟨step⟩
  rcases step with
    ⟨sigmaPrefix, activeBoundary, readyPrefix,
      previousReady, activeReady, payload,
      sigmaEquation, readyEquation, waitingInitialized, rfl⟩
  have previousBound :
      previousBoundary < before.waiting.size :=
    (Array.getElem?_eq_some_iff.mp waitingInitialized).1
  have previousNotPrefix :
      previousBoundary ∉ sigmaPrefix := by
    have oldIncreasing := wellShaped.sigma_partition.strictIncreasing
    rw [sigmaEquation] at oldIncreasing
    have reducedIncreasing :
        (sigmaPrefix ++ [previousBoundary]).Pairwise (· < ·) :=
      (List.pairwise_append.mp (by
        simpa [List.append_assoc] using oldIncreasing)).1
    have cross :=
      (List.pairwise_append.mp reducedIncreasing).2.2
    intro membership
    have impossible :=
      cross previousBoundary membership previousBoundary (by simp)
    exact Nat.lt_irrefl previousBoundary impossible
  exact {
    initialized_iff_inactive := by
      intro age ageBound
      have oldDomain :=
        domain.initialized_iff_inactive ageBound
      by_cases same : age = previousBoundary
      · subst age
        constructor
        · rintro ⟨stored, storedEquation⟩
          simp [previousBound] at storedEquation
        · intro inactive
          simp [previousNotPrefix] at inactive
      · constructor
        · rintro ⟨stored, storedEquation⟩
          have oldStored :
              before.WaitingInitializedAt age := by
            exact ⟨stored, by
              rw [Array.getElem?_setIfInBounds_ne
                (Ne.symm same)] at storedEquation
              exact storedEquation⟩
          have oldInactive := oldDomain.mp oldStored
          rw [sigmaEquation] at oldInactive
          simpa [same, List.append_assoc] using oldInactive
        · intro inactive
          have inPrefix : age ∈ sigmaPrefix := by
            simpa using inactive
          have oldInactive :
              age ∈ before.sigma.dropLast := by
            rw [sigmaEquation]
            simpa [same, List.append_assoc] using inPrefix
          rcases oldDomain.mpr oldInactive with
            ⟨stored, storedEquation⟩
          exact ⟨stored, by
            rw [Array.getElem?_setIfInBounds_ne
              (Ne.symm same)]
            exact storedEquation⟩ }

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

/-- The empty fixed-carrier state has the exact empty operational waiting
domain. -/
theorem empty_operationalWaitingDomain (carrierSize : Nat) :
    (empty carrierSize).OperationalWaitingDomain := by
  exact {
    initialized_iff_inactive :=
      fun {age : RawTokenAge}
          (ageBound : age < (empty carrierSize).nextAge) => by
      simp [empty] at ageBound }

/-- Explicit failures of the Figure-7 pop-before-mark primitive.

`markOutOfBounds` is deliberately distinct from `alreadyMarked`: array lookup
`none` is a carrier error, while `some (some age)` is an in-carrier occurrence
that already has a raw mark.  An in-carrier unmarked occurrence has lookup
`some none` and is the only successful case. -/
inductive PopReadyMarkError where
  | noReadyBucket
  | emptyTopBucket
  | noSigmaBoundary
  | markOutOfBounds (vertex : Vertex)
  | alreadyMarked (vertex : Vertex) (rawAge : RawTokenAge)
  deriving Repr, DecidableEq

/-- Executable output of one Figure-7 pop-before-mark action.  The selected
vertex is removed from the top (last) ready bucket, but the bucket itself is
retained even when `remainingTop = []`. -/
structure PopReadyMarkResult where
  vertex : Vertex
  rawAge : RawTokenAge
  remainingTop : List Vertex
  after : SequentialStackState
  deriving Repr, DecidableEq

/-- Pop the first selected vertex from the top (last) ready bucket and mark it
with the old top raw-age boundary.

This is only the common first line of the non-`init` rules in Guerrini
Figure 7.  It does not inspect the link below the selected vertex, mutate
`sigma` or `waiting`, or run `NEXTAXIOM`. -/
def popReadyMark?
    (state : SequentialStackState) :
    Except PopReadyMarkError PopReadyMarkResult :=
  match state.ready.getLast? with
  | none => .error .noReadyBucket
  | some [] => .error .emptyTopBucket
  | some (vertex :: remainingTop) =>
      match state.sigma.getLast? with
      | none => .error .noSigmaBoundary
      | some rawAge =>
          match state.marks[vertex]? with
          | none => .error (.markOutOfBounds vertex)
          | some none =>
              .ok {
                vertex := vertex
                rawAge := rawAge
                remainingTop := remainingTop
                after := {
                  state with
                  marks :=
                    state.marks.setIfInBounds vertex (some rawAge)
                  ready :=
                    state.ready.dropLast ++ [remainingTop] } }
          | some (some previousRawAge) =>
              .error (.alreadyMarked vertex previousRawAge)

/-- Proof-relevant exact specification of one successful pop-before-mark
action. -/
structure PopReadyMarkStep (before : SequentialStackState)
    (result : PopReadyMarkResult) : Type where
  top_eq :
    before.ready.getLast? =
      some (result.vertex :: result.remainingTop)
  sigma_top_eq :
    before.sigma.getLast? = some result.rawAge
  unmarked :
    before.marks[result.vertex]? = some none
  after_eq :
    result.after = {
      before with
      marks :=
        before.marks.setIfInBounds result.vertex (some result.rawAge)
      ready :=
        before.ready.dropLast ++ [result.remainingTop] }

/-- Executable success is equivalent to the exact dependent
pop-before-mark witness. -/
theorem popReadyMark?_ok_iff
    {state : SequentialStackState} {result : PopReadyMarkResult} :
    state.popReadyMark? = .ok result ↔
      Nonempty (PopReadyMarkStep state result) := by
  cases result with
  | mk resultVertex resultAge resultTail resultAfter =>
      constructor
      · intro equation
        unfold popReadyMark? at equation
        cases topEquation : state.ready.getLast? with
        | none =>
            simp [topEquation] at equation
        | some top =>
            cases top with
            | nil =>
                simp [topEquation] at equation
            | cons vertex remainingTop =>
                cases sigmaEquation : state.sigma.getLast? with
                | none =>
                    simp [topEquation, sigmaEquation] at equation
                | some rawAge =>
                    cases markEquation : state.marks[vertex]? with
                    | none =>
                        simp [topEquation, sigmaEquation, markEquation]
                          at equation
                    | some mark =>
                        cases mark with
                        | none =>
                            simp [topEquation, sigmaEquation, markEquation]
                              at equation
                            rcases equation with
                              ⟨rfl, rfl, rfl, rfl⟩
                            exact ⟨{
                              top_eq := topEquation
                              sigma_top_eq := sigmaEquation
                              unmarked := markEquation
                              after_eq := rfl }⟩
                        | some previousRawAge =>
                            simp [topEquation, sigmaEquation, markEquation]
                              at equation
      · rintro ⟨step⟩
        rcases step with
          ⟨topEquation, sigmaEquation, unmarked, afterEquation⟩
        simp [popReadyMark?, topEquation, sigmaEquation, unmarked]
          at afterEquation ⊢
        exact afterEquation.symm

/-- Exact changed and unchanged stack fields of a successful
pop-before-mark action. -/
theorem popReadyMark?_exact
    {state : SequentialStackState} {result : PopReadyMarkResult}
    (equation : state.popReadyMark? = .ok result) :
    state.ready.getLast? =
        some (result.vertex :: result.remainingTop) ∧
      state.sigma.getLast? = some result.rawAge ∧
      state.marks[result.vertex]? = some none ∧
      result.after.marks =
        state.marks.setIfInBounds result.vertex (some result.rawAge) ∧
      result.after.nextAge = state.nextAge ∧
      result.after.sigma = state.sigma ∧
      result.after.ready =
        state.ready.dropLast ++ [result.remainingTop] ∧
      result.after.waiting = state.waiting ∧
      result.after.marks[result.vertex]? =
        some (some result.rawAge) := by
  rcases popReadyMark?_ok_iff.mp equation with ⟨step⟩
  have vertexBound : result.vertex < state.marks.size :=
    (Array.getElem?_eq_some_iff.mp step.unmarked).1
  refine ⟨step.top_eq, step.sigma_top_eq, step.unmarked,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [step.after_eq]
  · rw [step.after_eq]
  · rw [step.after_eq]
  · rw [step.after_eq]
  · rw [step.after_eq]
  · rw [step.after_eq]
    simp [vertexBound]

/-- The common Figure-7 pop-before-mark action preserves scheduler shape.

The explicit successful-step guards supply all facts needed here: the selected
vertex is an in-bounds member of the old top bucket, and the assigned raw age
is the old top `sigma` boundary.  No semantic readiness claim is inferred. -/
theorem popReadyMark?_wellShaped
    {state : SequentialStackState} {result : PopReadyMarkResult}
    {carrierSize : Nat}
    (wellShaped : state.WellShaped carrierSize)
    (equation : state.popReadyMark? = .ok result) :
    result.after.WellShaped carrierSize := by
  rcases popReadyMark?_exact equation with
    ⟨topEquation, sigmaTopEquation, unmarked, marksEquation,
      nextAgeEquation, sigmaEquation, readyEquation, waitingEquation,
      marked⟩
  rcases List.getLast?_eq_some_iff.mp topEquation with
    ⟨readyPrefix, readyDecomposition⟩
  rcases List.getLast?_eq_some_iff.mp sigmaTopEquation with
    ⟨sigmaPrefix, sigmaDecomposition⟩
  have topMembership :
      result.vertex :: result.remainingTop ∈ state.ready := by
    rw [readyDecomposition]
    simp
  have topNodup :
      (result.vertex :: result.remainingTop).Nodup :=
    wellShaped.ready_nodup _ topMembership
  have rawAgeMembership : result.rawAge ∈ state.sigma := by
    rw [sigmaDecomposition]
    simp
  have rawAgeBound : result.rawAge < state.nextAge :=
    wellShaped.sigma_partition.boundary_lt
      result.rawAge rawAgeMembership
  have vertexBound : result.vertex < state.marks.size :=
    (Array.getElem?_eq_some_iff.mp unmarked).1
  exact {
    marks_size := by
      rw [marksEquation]
      simpa using wellShaped.marks_size
    waiting_size := by
      rw [waitingEquation]
      exact wellShaped.waiting_size
    assigned_age_bound := by
      intro vertex rawAge assigned
      rw [marksEquation] at assigned
      by_cases same : result.vertex = vertex
      · subst vertex
        simp [vertexBound] at assigned
        subst rawAge
        rw [nextAgeEquation]
        exact rawAgeBound
      · have oldAssigned :
            state.marks[vertex]? = some (some rawAge) := by
          simpa [Array.getElem?_setIfInBounds, same] using assigned
        rw [nextAgeEquation]
        exact wellShaped.assigned_age_bound vertex rawAge oldAssigned
    sigma_partition := by
      rw [sigmaEquation, nextAgeEquation]
      exact wellShaped.sigma_partition
    ready_aligned := by
      rw [readyEquation, sigmaEquation]
      calc
        (state.ready.dropLast ++ [result.remainingTop]).length =
            state.ready.length := by
          rw [readyDecomposition]
          simp
        _ = state.sigma.length := wellShaped.ready_aligned
    ready_nodup := by
      intro bucket membership
      rw [readyEquation] at membership
      simp only [List.mem_append, List.mem_singleton] at membership
      rcases membership with oldMembership | rfl
      · exact wellShaped.ready_nodup bucket
          (Graph.mem_of_mem_dropLast oldMembership)
      · exact topNodup.tail
    ready_in_bounds := by
      intro bucket membership vertex vertexMembership
      rw [readyEquation] at membership
      simp only [List.mem_append, List.mem_singleton] at membership
      rcases membership with oldMembership | rfl
      · exact wellShaped.ready_in_bounds bucket
          (Graph.mem_of_mem_dropLast oldMembership)
          vertex vertexMembership
      · exact wellShaped.ready_in_bounds
          (result.vertex :: result.remainingTop)
          topMembership vertex
          (List.mem_cons_of_mem result.vertex vertexMembership)
    nextAge_le_waiting := by
      rw [nextAgeEquation, waitingEquation]
      exact wellShaped.nextAge_le_waiting }

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

/-- Strict delayed initialization establishes the exact operational waiting
domain: the sole active boundary `0` remains `⊥`, so no allocated waiting cell
is initialized. -/
theorem initEnqueue?_operationalWaitingDomain
    {state after : SequentialStackState} {reached partner : Vertex}
    (equation : initEnqueue? state reached partner = some after) :
    after.OperationalWaitingDomain := by
  rcases initEnqueue?_some_iff.mp equation with ⟨ready, rfl⟩
  rcases ready with
    ⟨nextAgeZero, sigmaEmpty, readyEmpty, allMarks, allWaiting,
      waitingPositive, reachedBound, partnerBound, distinct⟩
  exact {
    initialized_iff_inactive :=
      fun {age : RawTokenAge}
          (ageBound :
            age < (initAfter state reached partner).nextAge) => by
      constructor
      · rintro ⟨payload, initialized⟩
        have ageWaitingBound : age < state.waiting.size := by
          have ageZero : age = 0 := by
            simpa [initAfter] using ageBound
          subst age
          exact waitingPositive
        have undefined := allWaiting.lookup ageWaitingBound
        rw [show
            (initAfter state reached partner).waiting = state.waiting by rfl,
          undefined] at initialized
        cases Option.some.inj initialized
      · intro inactive
        simp [initAfter] at inactive }

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

/-- Literal guard for the `new` line printed in Guerrini's Figure 7.

This display-level transition initializes the freshly pushed age.  It is
retained to make the source discrepancy auditable, but it does not preserve the
operational waiting-domain semantics required by the surrounding prose and
`unify`; production scheduler code uses `operationalNewEnqueue?` below. -/
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

/-- Literal transcription of the printed Figure-7 `new` waiting update.

This is not the production scheduler transition: it writes the fresh top
waiting cell, whereas the prose-defined waiting domain requires initializing
the old active boundary.  Use `operationalNewEnqueue?` for composable scheduler
work. -/
def newEnqueue? (state : SequentialStackState)
    (reached partner : Vertex) : Option SequentialStackState :=
  if NewReady state reached partner then
    some (newAfter state reached partner)
  else
    none

/-- Public proof-relevant specification of the literal printed `new` display.
The output equation avoids exposing the private executable helper. -/
structure PrintedNewStep
    (before after : SequentialStackState)
    (reached partner : Vertex) : Type where
  ready : NewReady before reached partner
  after_eq :
    after = {
      marks := before.marks
      nextAge := before.nextAge + 1
      sigma := before.sigma ++ [before.nextAge]
      ready := before.ready ++ [[reached, partner]]
      waiting :=
        before.waiting.setIfInBounds before.nextAge (.initialized []) }

private theorem newEnqueue?_some_iff_internal
    {state after : SequentialStackState} {reached partner : Vertex} :
    newEnqueue? state reached partner = some after ↔
      NewReady state reached partner ∧
        after = newAfter state reached partner := by
  simp [newEnqueue?, eq_comm]

/-- The literal printed `new` display succeeds exactly under its local guard.
This theorem specifies the source-audit helper, not the production transition. -/
theorem newEnqueue?_some_iff
    {state after : SequentialStackState} {reached partner : Vertex} :
    newEnqueue? state reached partner = some after ↔
      Nonempty (PrintedNewStep state after reached partner) := by
  constructor
  · intro equation
    rcases newEnqueue?_some_iff_internal.mp equation with ⟨ready, rfl⟩
    exact ⟨{
      ready := ready
      after_eq := rfl }⟩
  · rintro ⟨step⟩
    have helperEquation :
        after = newAfter state reached partner := by
      simpa [newAfter] using step.after_eq
    exact newEnqueue?_some_iff_internal.mpr ⟨step.ready, helperEquation⟩

/-- Exact fields of the literal printed `new` display, including its fresh-cell
write.  That write is retained for source comparison and is not operational. -/
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
  rcases newEnqueue?_some_iff_internal.mp equation with ⟨ready, rfl⟩
  rcases ready with
    ⟨positive, reachedBound, partnerBound, distinct, reachedUnmarked,
      partnerUnmarked, waitingFresh⟩
  have freshBound :
      state.nextAge < state.waiting.size :=
    (Array.getElem?_eq_some_iff.mp waitingFresh).1
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp [newAfter, freshBound]

/-- The literal printed `new` display changes no non-fresh waiting cell. -/
theorem newEnqueue?_waiting_of_ne
    {state after : SequentialStackState} {reached partner : Vertex}
    {index : RawTokenAge}
    (equation : newEnqueue? state reached partner = some after)
    (different : index ≠ state.nextAge) :
    after.waiting[index]? = state.waiting[index]? := by
  rw [(newEnqueue?_exact equation).2.2.2.2.1]
  exact Array.getElem?_setIfInBounds_ne different.symm

/-- The literal printed `new` display leaves both endpoints unmarked. -/
theorem newEnqueue?_endpoint_unmarked
    {state after : SequentialStackState} {reached partner : Vertex}
    (equation : newEnqueue? state reached partner = some after) :
    after.marks[reached]? = some none ∧
      after.marks[partner]? = some none := by
  rcases newEnqueue?_some_iff_internal.mp equation with ⟨ready, rfl⟩
  rcases ready with
    ⟨positive, reachedBound, partnerBound, distinct, reachedUnmarked,
      partnerUnmarked, waitingFresh⟩
  exact ⟨reachedUnmarked, partnerUnmarked⟩

/-- The literal printed transition preserves the deliberately weak shape
invariant.  It does not preserve `OperationalWaitingDomain`. -/
theorem newEnqueue?_wellShaped
    {state after : SequentialStackState} {carrierSize : Nat}
    {reached partner : Vertex}
    (wellShaped : state.WellShaped carrierSize)
    (equation : newEnqueue? state reached partner = some after) :
    after.WellShaped carrierSize := by
  rcases newEnqueue?_some_iff_internal.mp equation with ⟨ready, rfl⟩
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

/-- Executable guard for the operationally coherent later reservation.

`active` is the old top `sigma` boundary.  It must still have an undefined
waiting cell, while the fresh raw age at `nextAge` must also be unused.  The
new endpoints are required to be globally absent from both the ready stack and
every waiting payload, so this local transition cannot introduce a duplicate
that a later `unify` would drain back into ready work. -/
def OperationalNewReadyAt (state : SequentialStackState)
    (active : RawTokenAge) (reached partner : Vertex) : Prop :=
  0 < state.nextAge ∧
  state.sigma.getLast? = some active ∧
  active < state.nextAge ∧
  reached < state.marks.size ∧
  partner < state.marks.size ∧
  reached ≠ partner ∧
  reached ∉ state.queuedVertices ∧
  partner ∉ state.queuedVertices ∧
  state.marks[reached]? = some none ∧
  state.marks[partner]? = some none ∧
  state.waiting[active]? = some .undefined ∧
  state.waiting[state.nextAge]? = some .undefined

instance (state : SequentialStackState) (active : RawTokenAge)
    (reached partner : Vertex) :
    Decidable (OperationalNewReadyAt state active reached partner) := by
  unfold OperationalNewReadyAt
  infer_instance

private def operationalNewAfter (state : SequentialStackState)
    (active : RawTokenAge) (reached partner : Vertex) :
    SequentialStackState where
  marks := state.marks
  nextAge := state.nextAge + 1
  sigma := state.sigma ++ [state.nextAge]
  ready := state.ready ++ [[reached, partner]]
  waiting :=
    state.waiting.setIfInBounds active (.initialized [])

/-- Operational later reservation.

The freshly allocated raw age becomes the new active top and remains `⊥`.
Instead, the old active boundary becomes inactive and is initialized to `∅`.
This is the chosen one-cell interpretation compatible with the prose
definition of `W`, the `wait` lookup, and the `unify` rule that later drains
that boundary.  No author-confirmed erratum or uniqueness theorem is claimed. -/
def operationalNewEnqueue? (state : SequentialStackState)
    (reached partner : Vertex) : Option SequentialStackState :=
  match state.sigma.getLast? with
  | none => none
  | some active =>
      if OperationalNewReadyAt state active reached partner then
        some (operationalNewAfter state active reached partner)
      else
        none

/-- Public proof-relevant specification of one successful operational `new`.

The output equation is stated as an explicit record rather than exposing the
private executable helper in the public theorem signature. -/
structure OperationalNewStep
    (before after : SequentialStackState)
    (reached partner : Vertex) : Type where
  active : RawTokenAge
  ready : OperationalNewReadyAt before active reached partner
  after_eq :
    after = {
      marks := before.marks
      nextAge := before.nextAge + 1
      sigma := before.sigma ++ [before.nextAge]
      ready := before.ready ++ [[reached, partner]]
      waiting :=
        before.waiting.setIfInBounds active (.initialized []) }

private theorem operationalNewEnqueue?_some_iff_internal
    {state after : SequentialStackState} {reached partner : Vertex} :
    operationalNewEnqueue? state reached partner = some after ↔
      ∃ active,
        state.sigma.getLast? = some active ∧
        OperationalNewReadyAt state active reached partner ∧
        after = operationalNewAfter state active reached partner := by
  cases activeEquation : state.sigma.getLast? with
  | none =>
      simp [operationalNewEnqueue?, activeEquation]
  | some active =>
      simp [operationalNewEnqueue?, activeEquation, eq_comm]

/-- Executable success is equivalent to the public exact operational step. -/
theorem operationalNewEnqueue?_some_iff
    {state after : SequentialStackState} {reached partner : Vertex} :
    operationalNewEnqueue? state reached partner = some after ↔
      Nonempty (OperationalNewStep state after reached partner) := by
  constructor
  · intro equation
    rcases operationalNewEnqueue?_some_iff_internal.mp equation with
      ⟨active, activeEquation, ready, rfl⟩
    exact ⟨{
      active := active
      ready := ready
      after_eq := rfl }⟩
  · rintro ⟨step⟩
    have helperEquation :
        after = operationalNewAfter state step.active reached partner := by
      simpa [operationalNewAfter] using step.after_eq
    exact operationalNewEnqueue?_some_iff_internal.mpr
      ⟨step.active, step.ready.2.1, step.ready, helperEquation⟩

/-- Exact fields of the operational later reservation.  The witness exposes
both the initialized old boundary and the still-undefined fresh top. -/
theorem operationalNewEnqueue?_exact
    {state after : SequentialStackState} {reached partner : Vertex}
    (equation :
      operationalNewEnqueue? state reached partner = some after) :
    ∃ active,
      state.sigma.getLast? = some active ∧
      active < state.nextAge ∧
      after.marks = state.marks ∧
      after.nextAge = state.nextAge + 1 ∧
      after.sigma = state.sigma ++ [state.nextAge] ∧
      after.ready = state.ready ++ [[reached, partner]] ∧
      after.waiting =
        state.waiting.setIfInBounds active (.initialized []) ∧
      after.waiting[active]? = some (.initialized []) ∧
      after.waiting[state.nextAge]? = some .undefined := by
  rcases operationalNewEnqueue?_some_iff_internal.mp equation with
    ⟨active, activeEquation, ready, rfl⟩
  rcases ready with
    ⟨positive, activeEquation', activeLt, reachedBound, partnerBound,
      distinct, reachedAbsentQueued, partnerAbsentQueued, reachedUnmarked,
      partnerUnmarked, activeUndefined, freshUndefined⟩
  have activeWaitingBound : active < state.waiting.size :=
    (Array.getElem?_eq_some_iff.mp activeUndefined).1
  have activeNeFresh : active ≠ state.nextAge :=
    Nat.ne_of_lt activeLt
  refine ⟨active, activeEquation, activeLt, rfl, rfl, rfl, rfl, rfl,
    ?_, ?_⟩
  · simp [operationalNewAfter, activeWaitingBound]
  · rw [show
        (operationalNewAfter state active reached partner).waiting =
          state.waiting.setIfInBounds active (.initialized []) by rfl]
    rw [Array.getElem?_setIfInBounds_ne activeNeFresh]
    exact freshUndefined

/-- Operational `new` leaves both newly enqueued endpoints unmarked. -/
theorem operationalNewEnqueue?_endpoint_unmarked
    {state after : SequentialStackState} {reached partner : Vertex}
    (equation :
      operationalNewEnqueue? state reached partner = some after) :
    after.marks[reached]? = some none ∧
      after.marks[partner]? = some none := by
  rcases operationalNewEnqueue?_some_iff_internal.mp equation with
    ⟨active, activeEquation, ready, rfl⟩
  exact ⟨ready.2.2.2.2.2.2.2.2.1, ready.2.2.2.2.2.2.2.2.2.1⟩

/-- Operational `new` preserves the deliberately structural `WellShaped`
invariant. -/
theorem operationalNewEnqueue?_wellShaped
    {state after : SequentialStackState} {carrierSize : Nat}
    {reached partner : Vertex}
    (wellShaped : state.WellShaped carrierSize)
    (equation :
      operationalNewEnqueue? state reached partner = some after) :
    after.WellShaped carrierSize := by
  rcases operationalNewEnqueue?_some_iff_internal.mp equation with
    ⟨active, activeEquation, ready, rfl⟩
  rcases ready with
    ⟨positive, activeEquation', activeLt, reachedBound, partnerBound,
      distinct, reachedAbsentQueued, partnerAbsentQueued, reachedUnmarked,
      partnerUnmarked, activeUndefined, freshUndefined⟩
  have reachedAbsent : reached ∉ state.ready.flatten := by
    intro membership
    exact reachedAbsentQueued (by
      simp [queuedVertices, membership])
  have partnerAbsent : partner ∉ state.ready.flatten := by
    intro membership
    exact partnerAbsentQueued (by
      simp [queuedVertices, membership])
  have reachedCarrier : reached < carrierSize := by
    rw [← wellShaped.marks_size]
    exact reachedBound
  have partnerCarrier : partner < carrierSize := by
    rw [← wellShaped.marks_size]
    exact partnerBound
  have activeWaitingBound : active < state.waiting.size :=
    (Array.getElem?_eq_some_iff.mp activeUndefined).1
  have freshWaitingBound : state.nextAge < state.waiting.size :=
    (Array.getElem?_eq_some_iff.mp freshUndefined).1
  exact {
    marks_size := wellShaped.marks_size
    waiting_size := by
      simpa [operationalNewAfter] using wellShaped.waiting_size
    assigned_age_bound := by
      intro vertex age assigned
      have oldBound :=
        wellShaped.assigned_age_bound vertex age assigned
      exact Nat.lt_trans oldBound (Nat.lt_succ_self _)
    sigma_partition :=
      SigmaAgePartition.appendFresh wellShaped.sigma_partition positive
    ready_aligned := by
      simp [operationalNewAfter, wellShaped.ready_aligned]
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
        (state.waiting.setIfInBounds active (.initialized [])).size
      simpa using (Nat.succ_le_of_lt freshWaitingBound) }

/-- Operational `new` preserves the exact initialized waiting domain.

Before the push, initialized cells correspond to `sigma.dropLast`; setting the
old last boundary initializes exactly the one additional member needed for the
new inactive set `sigma`.  The fresh new top is checked to remain undefined. -/
theorem operationalNewEnqueue?_operationalWaitingDomain
    {state after : SequentialStackState} {carrierSize : Nat}
    {reached partner : Vertex}
    (domain : state.OperationalWaitingDomain)
    (wellShaped : state.WellShaped carrierSize)
    (equation :
      operationalNewEnqueue? state reached partner = some after) :
    after.OperationalWaitingDomain := by
  rcases operationalNewEnqueue?_some_iff_internal.mp equation with
    ⟨active, activeEquation, ready, rfl⟩
  rcases List.getLast?_eq_some_iff.mp activeEquation with
    ⟨sigmaPrefix, sigmaEquation⟩
  rcases ready with
    ⟨positive, activeEquation', activeLt, reachedBound, partnerBound,
      distinct, reachedAbsentQueued, partnerAbsentQueued, reachedUnmarked,
      partnerUnmarked, activeUndefined, freshUndefined⟩
  have activeWaitingBound : active < state.waiting.size :=
    (Array.getElem?_eq_some_iff.mp activeUndefined).1
  have activeNeFresh : active ≠ state.nextAge :=
    Nat.ne_of_lt activeLt
  have freshNotMember : state.nextAge ∉ state.sigma := by
    intro membership
    have boundaryLt :=
      wellShaped.sigma_partition.boundary_lt
        state.nextAge membership
    exact (Nat.lt_irrefl state.nextAge boundaryLt)
  exact {
    initialized_iff_inactive :=
      fun {age : RawTokenAge}
          (ageBound :
            age <
              (operationalNewAfter
                state active reached partner).nextAge) => by
      have ageBound' : age < state.nextAge + 1 := by
        simpa [operationalNewAfter] using ageBound
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ageBound') with
        oldAge | freshAge
      · by_cases ageActive : age = active
        · subst age
          simp [WaitingInitializedAt, operationalNewAfter,
            activeWaitingBound, sigmaEquation]
        · have oldDomain :=
            OperationalWaitingDomain.initialized_iff_inactive
              domain oldAge
          change
            (∃ payload,
              (state.waiting.setIfInBounds active (.initialized []))[age]? =
                some (.initialized payload)) ↔
              age ∈ (state.sigma ++ [state.nextAge]).dropLast
          rw [Array.getElem?_setIfInBounds_ne (Ne.symm ageActive)]
          simpa [WaitingInitializedAt, sigmaEquation, ageActive] using
            oldDomain
      · subst age
        constructor
        · rintro ⟨payload, initialized⟩
          rw [show
              (operationalNewAfter state active reached partner).waiting =
                state.waiting.setIfInBounds active (.initialized []) by rfl,
            Array.getElem?_setIfInBounds_ne activeNeFresh] at initialized
          rw [freshUndefined] at initialized
          cases Option.some.inj initialized
        · intro membership
          simp [operationalNewAfter, freshNotMember] at membership }

end SequentialStackState

end SequentialSchedulerState

end ProofNetIR
