import ProofNetIR.UnificationSemantics

namespace ProofNetIR

/-- A partially parsed proof component used by the executable Guerrini-style
unification pass. `frontier` records the formula occurrences currently exposed
by `tree`, in exactly the order inferred by the derivation. -/
structure UnificationComponent where
  tree : CutFreeDerivation
  frontier : List Vertex
  deriving Repr, DecidableEq

namespace UnificationComponent

/-- A partial component is formula-consistent when its derivation infers
exactly the certificate labels of its exposed occurrence frontier. -/
def FormulaConsistent (certificate : Certificate)
    (component : UnificationComponent) : Prop :=
  ∃ sequent,
    component.tree.infer? = some sequent ∧
      component.frontier.mapM certificate.formula? = some sequent

end UnificationComponent

/-- Runtime state for the deterministic unification pass.

`marks[v]` is the token initially assigned to `v`; `parents` represents the
current token partition; and only representative entries of `components`
contain a live parsed component. The implementation deliberately keeps this
state proof-irrelevant and validates the final derivation independently with
`Certificate.verifyDerivation?`. -/
structure UnificationState where
  marks : Array (Option Nat)
  parents : Array Nat
  components : Array (Option UnificationComponent)
  startedAxioms : Nat
  firedConnectives : Nat
  deriving Repr, DecidableEq

namespace UnificationState

/-- Every stored live component denotes a formula-consistent partial
derivation. Retired `none` slots impose no obligation. -/
def ComponentsFormulaConsistent (certificate : Certificate)
    (state : UnificationState) : Prop :=
  ∀ {index : Nat} {component : UnificationComponent},
    state.components[index]? = some (some component) →
      component.FormulaConsistent certificate

/-- Appending one formula-consistent live component preserves consistency of
every previously stored slot. -/
theorem ComponentsFormulaConsistent.push
    {certificate : Certificate} {state : UnificationState}
    (consistent : state.ComponentsFormulaConsistent certificate)
    {component : UnificationComponent}
    (componentConsistent : component.FormulaConsistent certificate) :
    ({ state with
      components := state.components.push (some component) } :
      UnificationState).ComponentsFormulaConsistent certificate := by
  intro index candidate lookup
  by_cases atNew : index = state.components.size
  · subst index
    simp at lookup
    subst candidate
    exact componentConsistent
  · have oldLookup :
        state.components[index]? = some (some candidate) := by
      simpa [Array.getElem?_push, atNew] using lookup
    exact consistent oldLookup

/-- Replacing one component slot with a formula-consistent component
preserves consistency of all live slots. -/
theorem ComponentsFormulaConsistent.set
    {certificate : Certificate} {state : UnificationState}
    (consistent : state.ComponentsFormulaConsistent certificate)
    {index : Nat} {component : UnificationComponent}
    (componentConsistent : component.FormulaConsistent certificate) :
    ({ state with
      components :=
        state.components.setIfInBounds index (some component) } :
      UnificationState).ComponentsFormulaConsistent certificate := by
  intro candidateIndex candidate lookup
  by_cases same : index = candidateIndex
  · subst candidateIndex
    by_cases bound : index < state.components.size
    · simp [bound] at lookup
      subst candidate
      exact componentConsistent
    · have oldLookup :
          state.components[index]? = some (some candidate) := by
        simp [bound] at lookup
      exact consistent oldLookup
  · have oldLookup :
        state.components[candidateIndex]? =
          some (some candidate) := by
      simpa [Array.getElem?_setIfInBounds, same] using lookup
    exact consistent oldLookup

/-- Clearing one component slot cannot introduce an inconsistent live
component. -/
theorem ComponentsFormulaConsistent.clear
    {certificate : Certificate} {state : UnificationState}
    (consistent : state.ComponentsFormulaConsistent certificate)
    (index : Nat) :
    ({ state with
      components := state.components.setIfInBounds index none } :
      UnificationState).ComponentsFormulaConsistent certificate := by
  intro candidateIndex candidate lookup
  by_cases same : index = candidateIndex
  · subst candidateIndex
    by_cases bound : index < state.components.size
    · simp [bound] at lookup
    · have oldLookup :
          state.components[index]? = some (some candidate) := by
        simp [bound] at lookup
      exact consistent oldLookup
  · have oldLookup :
        state.components[candidateIndex]? =
          some (some candidate) := by
      simpa [Array.getElem?_setIfInBounds, same] using lookup
    exact consistent oldLookup

end UnificationState

/-- Observable work counters for the eager repeated-scan implementation.

`linkVisits` counts only link-list entries inspected by saturation. It
does not count frontier search, union-find traversal, final derivation
verification, or a hybrid fallback. -/
structure UnificationScanStats where
  passes : Nat
  linkVisits : Nat
  successfulFirings : Nat
  deriving Repr, DecidableEq, BEq

/-- A derivation candidate together with proof-relevant bounds for the exact
eager scan schedule that produced it. -/
structure UnificationCandidateResult (certificate : Certificate) where
  tree : CutFreeDerivation
  stats : UnificationScanStats
  passesBound : stats.passes ≤ certificate.links.length
  linkVisitsExact :
    stats.linkVisits = stats.passes * certificate.links.length

namespace UnificationCandidateResult

/-- The eager candidate generator visits at most the square of the submitted
link count. This theorem concerns link-list visits only. -/
theorem linkVisitsBound {certificate : Certificate}
    (result : UnificationCandidateResult certificate) :
    result.stats.linkVisits ≤
      certificate.links.length * certificate.links.length := by
  rw [result.linkVisitsExact]
  exact Nat.mul_le_mul_right certificate.links.length result.passesBound

end UnificationCandidateResult

/-- A proof-bearing unification result retaining the exact scan statistics of
the candidate that passed independent verification. -/
structure UnificationVerificationResult (certificate : Certificate) where
  candidate : UnificationCandidateResult certificate
  verification : DerivationVerificationResult certificate

/-- Observable counters for the event-driven ready/waiting worklist
prototype. No asymptotic theorem is attached to these counters yet. -/
structure UnificationWorklistStats where
  initialEnqueues : Nat
  dependencyEnqueues : Nat
  waitingRequeues : Nat
  linkAttempts : Nat
  successfulFirings : Nat
  deriving Repr, DecidableEq, BEq

/-- Conservative executable link-attempt budget for the current worklist.
The proof layer establishes that canonical production runs exhaust their queue
within this fuel; that scheduler theorem is not yet correct-net completeness or
a whole-program complexity theorem. -/
def UnificationWorklistStats.attemptBudget (linkCount : Nat) : Nat :=
  linkCount * (linkCount + 4) + 1

/-- Derivation candidate produced by the event-driven ready/waiting worklist
prototype. -/
structure UnificationWorklistCandidateResult
    (certificate : Certificate) where
  tree : CutFreeDerivation
  stats : UnificationWorklistStats
  attemptsBound :
    stats.linkAttempts ≤
      UnificationWorklistStats.attemptBudget certificate.links.length

namespace UnificationWorklistCandidateResult

/-- Every successful worklist candidate stays within the conservative
executable link-attempt budget. A separate internal scheduler theorem proves
canonical queue exhaustion; correct-net progress remains open. -/
theorem linkAttemptsWithinBudget {certificate : Certificate}
    (result : UnificationWorklistCandidateResult certificate) :
    result.stats.linkAttempts ≤
      UnificationWorklistStats.attemptBudget certificate.links.length :=
  result.attemptsBound

end UnificationWorklistCandidateResult

/-- Independently verified worklist candidate with its operational counters. -/
structure UnificationWorklistVerificationResult
    (certificate : Certificate) where
  candidate : UnificationWorklistCandidateResult certificate
  verification : DerivationVerificationResult certificate

/-- Stable failure category for deterministic unification. A fast-path failure
does not by itself prove that the submitted certificate is incorrect. -/
inductive UnificationErrorCode where
  | malformedInput
  | axiomInitializationFailed
  | incompleteMarking
  | incompleteLinkFiring
  | nonUniqueThread
  | boundaryMismatch
  | candidateVerificationFailed
  deriving Repr, DecidableEq, BEq

/-- Structured diagnostic for the deterministic unification tier. -/
structure UnificationError where
  code : UnificationErrorCode
  message : String
  formulaCount : Nat
  linkCount : Nat
  deriving Repr, DecidableEq, BEq

namespace UnificationError

/-- Human-readable diagnostic preserving the stable machine category. -/
def render (error : UnificationError) : String :=
  s!"{repr error.code}: {error.message} " ++
    s!"(formulas={error.formulaCount}, links={error.linkCount})"

end UnificationError

namespace UnificationState

/-- Follow at most `fuel` parent pointers. Union always points a larger root to
a smaller root, so `parents.size` is a conservative executable bound. -/
private def representativeWithFuel (parents : Array Nat) :
    Nat → Nat → Nat
  | 0, token => token
  | fuel + 1, token =>
      match parents[token]? with
      | none => token
      | some parent =>
          if parent == token then token
          else representativeWithFuel parents fuel parent

/-- A missing parent entry is stable under every remaining fuel value. -/
private theorem representativeWithFuel_of_lookup_none
    (parents : Array Nat) {token : Nat}
    (lookup : parents[token]? = none) (fuel : Nat) :
    representativeWithFuel parents fuel token = token := by
  cases fuel with
  | zero =>
      rfl
  | succ fuel =>
      simp [representativeWithFuel, lookup]

/-- A self-parent root is stable under every remaining fuel value. -/
private theorem representativeWithFuel_of_lookup_self
    (parents : Array Nat) {token : Nat}
    (lookup : parents[token]? = some token) (fuel : Nat) :
    representativeWithFuel parents fuel token = token := by
  cases fuel with
  | zero =>
      rfl
  | succ fuel =>
      simp [representativeWithFuel, lookup]

/-- Following `first` pointers and then `second` more is the same as following
their total fuel in one run. -/
private theorem representativeWithFuel_add
    (parents : Array Nat) (first second token : Nat) :
    representativeWithFuel parents (first + second) token =
      representativeWithFuel parents second
        (representativeWithFuel parents first token) := by
  induction first generalizing token with
  | zero =>
      simp [representativeWithFuel]
  | succ first induction =>
      simp only [Nat.succ_add, representativeWithFuel]
      cases lookup : parents[token]? with
      | none =>
          rw [representativeWithFuel_of_lookup_none
            parents lookup second]
      | some parent =>
          by_cases self : parent = token
          · subst parent
            simp [representativeWithFuel_of_lookup_self
                parents lookup second]
          · simp [self]
            exact induction parent

/-- Current canonical representative of a token. -/
def representative (state : UnificationState) (token : Nat) : Nat :=
  representativeWithFuel state.parents state.parents.size token

/-- Raw token assigned to a formula occurrence, before representative lookup.
This is the marking field used by the independent transition semantics. -/
def assignedToken? (state : UnificationState) (vertex : Vertex) :
    Option Nat :=
  state.marks[vertex]?.join

/-- A successful raw-token lookup exposes the exact nested mark-array entry. -/
theorem assignedToken?_some_raw
    {state : UnificationState} {vertex token : Nat}
    (marked : state.assignedToken? vertex = some token) :
    state.marks[vertex]? = some (some token) := by
  unfold assignedToken? at marked
  cases lookup : state.marks[vertex]? with
  | none =>
      simp [lookup] at marked
  | some assigned =>
      cases assigned with
      | none =>
          simp [lookup] at marked
      | some stored =>
          simp [lookup] at marked
          subst stored
          rfl

/-- Two allocated tokens lie in the same executable union-find class. -/
def SameThread (state : UnificationState) (first second : Nat) : Prop :=
  state.representative first = state.representative second

/-- Bounds required to interpret an executable state as an independent
`UnificationMarking`. Later preservation theorems will discharge this contract
for every reachable state. -/
structure Abstractable (certificate : Certificate)
    (state : UnificationState) : Prop where
  markArraySize :
    state.marks.size = certificate.formulas.size
  markedVertexBound :
    ∀ {vertex token}, state.assignedToken? vertex = some token →
      vertex < certificate.formulas.size
  markedTokenBound :
    ∀ {vertex token}, state.assignedToken? vertex = some token →
      token < state.parents.size
  representativeBound :
    ∀ {token}, token < state.parents.size →
      state.representative token < state.parents.size
  representativeIdempotent :
    ∀ {token}, token < state.parents.size →
      state.representative (state.representative token) =
        state.representative token

/-- For an in-domain formula occurrence, semantic absence of a raw token is
exactly the concrete `some none` array state required by firing guards. -/
theorem Abstractable.markSlotReady_of_unassigned
    {certificate : Certificate} {state : UnificationState}
    (abstractable : state.Abstractable certificate)
    {vertex : Vertex}
    (vertexBound : vertex < certificate.formulas.size)
    (unassigned : state.assignedToken? vertex = none) :
    state.marks[vertex]? = some none := by
  cases lookup : state.marks[vertex]? with
  | none =>
      have outOfBounds := Array.getElem?_eq_none_iff.mp lookup
      have inBounds : vertex < state.marks.size := by
        simpa [abstractable.markArraySize] using vertexBound
      exact False.elim ((Nat.not_lt_of_ge outOfBounds) inBounds)
  | some assigned =>
      cases assigned with
      | none =>
          simp
      | some token =>
          unfold assignedToken? at unassigned
          simp [lookup] at unassigned

/-- Equality of exactly the executable fields observed by the independent
unification semantics. Parsed derivation components and work counters are
intentionally ignored. -/
structure ObservationEquivalent
    (first second : UnificationState) : Prop where
  marks : first.marks = second.marks
  parents : first.parents = second.parents

/-- Observation-equivalent states compute exactly the same representative
for every token. -/
theorem ObservationEquivalent.representative_eq
    {first second : UnificationState}
    (equivalent : first.ObservationEquivalent second)
    (token : Nat) :
    second.representative token = first.representative token := by
  unfold UnificationState.representative
  rw [← equivalent.parents]

/-- During the eager axiom-start phase every allocated token is still its own
union-find parent. No connective union has fired yet. -/
def IdentityParents (state : UnificationState) : Prop :=
  ∀ {token}, token < state.parents.size →
    state.parents[token]? = some token

/-- Every parent pointer is nonincreasing in token number. Consequently each
non-root pointer is strictly decreasing, ruling out the fuel-artifact cycles
that the bounds-only abstraction contract intentionally does not exclude. -/
def OrderedParents (state : UnificationState) : Prop :=
  ∀ {token parent : Nat}, state.parents[token]? = some parent →
    parent ≤ token

/-- Following any finite number of pointers in an ordered parent array cannot
increase the starting token. -/
private theorem OrderedParents.representativeWithFuel_le
    {state : UnificationState}
    (ordered : state.OrderedParents)
    (fuel token : Nat) :
    representativeWithFuel state.parents fuel token ≤ token := by
  induction fuel generalizing token with
  | zero =>
      exact Nat.le_refl token
  | succ fuel induction =>
      simp only [representativeWithFuel]
      cases lookup : state.parents[token]? with
      | none =>
          exact Nat.le_refl token
      | some parent =>
          by_cases self : parent = token
          · subst parent
            simp
          · simp [self]
            exact Nat.le_trans (induction parent) (ordered lookup)

/-- An ordered union-find forest always returns a no-larger representative. -/
theorem OrderedParents.representative_le
    {state : UnificationState}
    (ordered : state.OrderedParents)
    (token : Nat) :
    state.representative token ≤ token := by
  exact ordered.representativeWithFuel_le state.parents.size token

/-- Representatives of allocated tokens remain allocated. -/
theorem OrderedParents.representative_lt
    {state : UnificationState}
    (ordered : state.OrderedParents)
    {token : Nat} (bound : token < state.parents.size) :
    state.representative token < state.parents.size :=
  Nat.lt_of_le_of_lt (ordered.representative_le token) bound

/-- Once fuel exceeds the starting token number, ordered-parent traversal is
independent of the exact fuel value. -/
private theorem OrderedParents.representativeWithFuel_eq_of_token_lt
    {state : UnificationState}
    (ordered : state.OrderedParents)
    {firstFuel secondFuel token : Nat}
    (firstEnough : token < firstFuel)
    (secondEnough : token < secondFuel) :
    representativeWithFuel state.parents firstFuel token =
      representativeWithFuel state.parents secondFuel token := by
  induction token using Nat.strongRecOn
      generalizing firstFuel secondFuel with
  | ind token induction =>
      cases firstFuel with
      | zero =>
          omega
      | succ firstFuel =>
          cases secondFuel with
          | zero =>
              omega
          | succ secondFuel =>
              simp only [representativeWithFuel]
              cases lookup : state.parents[token]? with
              | none =>
                  rfl
              | some parent =>
                  by_cases self : parent = token
                  · subst parent
                    simp
                  · have parentLt : parent < token := by
                      have parentLe := ordered lookup
                      omega
                    simp [self]
                    apply induction parent parentLt
                    · omega
                    · omega

/-- Ordered-parent traversal is idempotent on every allocated token. -/
theorem OrderedParents.representative_idempotent
    {state : UnificationState}
    (ordered : state.OrderedParents)
    {token : Nat} (bound : token < state.parents.size) :
    state.representative (state.representative token) =
      state.representative token := by
  unfold UnificationState.representative
  calc
    representativeWithFuel state.parents state.parents.size
        (representativeWithFuel state.parents state.parents.size token) =
      representativeWithFuel state.parents
        (state.parents.size + state.parents.size) token := by
          symm
          exact representativeWithFuel_add state.parents
            state.parents.size state.parents.size token
    _ = representativeWithFuel state.parents state.parents.size token := by
      apply ordered.representativeWithFuel_eq_of_token_lt
      · omega
      · exact bound

/-- An allocated token that is already its own representative is stored as a
self-parent root. -/
theorem OrderedParents.lookup_self_of_representative_eq
    {state : UnificationState}
    (ordered : state.OrderedParents)
    {token : Nat} (bound : token < state.parents.size)
    (root : state.representative token = token) :
    state.parents[token]? = some token := by
  cases lookup : state.parents[token]? with
  | none =>
      have outOfBounds := Array.getElem?_eq_none_iff.mp lookup
      omega
  | some parent =>
      by_cases self : parent = token
      · subst parent
        rfl
      · have parentLt : parent < token := by
          have parentLe := ordered lookup
          omega
        cases sizeEquation : state.parents.size with
        | zero =>
            omega
        | succ fuel =>
            have traversal :
                representativeWithFuel state.parents fuel parent = token := by
              simpa [representative, sizeEquation,
                representativeWithFuel, lookup, self] using root
            have traversalLe :=
              ordered.representativeWithFuel_le fuel parent
            rw [traversal] at traversalLe
            omega

/-- Every allocated representative is backed by a self-parent root entry. -/
theorem OrderedParents.representative_lookup_self
    {state : UnificationState}
    (ordered : state.OrderedParents)
    {token : Nat} (bound : token < state.parents.size) :
    state.parents[state.representative token]? =
      some (state.representative token) := by
  apply ordered.lookup_self_of_representative_eq
    (ordered.representative_lt bound)
  exact ordered.representative_idempotent bound

/-- An allocated token and its stored parent have the same representative. -/
theorem OrderedParents.representative_eq_representative_parent
    {state : UnificationState}
    (ordered : state.OrderedParents)
    {token parent : Nat}
    (tokenBound : token < state.parents.size)
    (lookup : state.parents[token]? = some parent) :
    state.representative token = state.representative parent := by
  by_cases self : parent = token
  · subst parent
    rfl
  · have parentLt : parent < token := by
      have parentLe := ordered lookup
      omega
    cases sizeEquation : state.parents.size with
    | zero =>
        omega
    | succ fuel =>
        unfold representative
        simp only [sizeEquation]
        have firstStep :
            representativeWithFuel state.parents (fuel + 1) token =
              representativeWithFuel state.parents fuel parent := by
          simp [representativeWithFuel, lookup, self]
        rw [firstStep]
        apply ordered.representativeWithFuel_eq_of_token_lt
        · omega
        · omega

/-- A stored self-parent entry is returned as its own representative. -/
theorem representative_eq_of_lookup_self
    {state : UnificationState} {token : Nat}
    (lookup : state.parents[token]? = some token) :
    state.representative token = token := by
  unfold UnificationState.representative
  exact representativeWithFuel_of_lookup_self
    state.parents lookup state.parents.size

/-- Unallocated carrier elements are represented by themselves. -/
theorem representative_eq_of_size_le
    (state : UnificationState) {token : Nat}
    (outOfBounds : state.parents.size ≤ token) :
    state.representative token = token := by
  unfold representative
  exact representativeWithFuel_of_lookup_none state.parents
    (Array.getElem?_eq_none outOfBounds) state.parents.size

/-- Mark-domain bounds plus an ordered parent forest suffice to construct the
full executable abstraction contract; representative range and idempotence
are consequences rather than independent assumptions. -/
theorem OrderedParents.abstractable
    {certificate : Certificate} {state : UnificationState}
    (ordered : state.OrderedParents)
    (markArraySize :
      state.marks.size = certificate.formulas.size)
    (markedVertexBound :
      ∀ {vertex token}, state.assignedToken? vertex = some token →
        vertex < certificate.formulas.size)
    (markedTokenBound :
      ∀ {vertex token}, state.assignedToken? vertex = some token →
        token < state.parents.size) :
    state.Abstractable certificate where
  markArraySize := markArraySize
  markedVertexBound := markedVertexBound
  markedTokenBound := markedTokenBound
  representativeBound := ordered.representative_lt
  representativeIdempotent := ordered.representative_idempotent

/-- Identity-parent states return each allocated token as its own
representative. -/
theorem IdentityParents.representative_eq
    {state : UnificationState}
    (identity : state.IdentityParents)
    {token : Nat} (bound : token < state.parents.size) :
    state.representative token = token := by
  unfold representative
  cases sizeEquation : state.parents.size with
  | zero =>
      omega
  | succ fuel =>
      simp [representativeWithFuel, identity bound]

/-- Identity-parent states return every natural-number carrier element as its
own representative, including token numbers not yet allocated. -/
theorem IdentityParents.representative_eq_all
    {state : UnificationState}
    (identity : state.IdentityParents)
    (token : Nat) :
    state.representative token = token := by
  by_cases bound : token < state.parents.size
  · exact identity.representative_eq bound
  · unfold representative
    cases sizeEquation : state.parents.size with
    | zero =>
        simp [representativeWithFuel]
    | succ fuel =>
        have lookup : state.parents[token]? = none :=
          Array.getElem?_eq_none (Nat.le_of_not_gt bound)
        simp [representativeWithFuel, lookup]

/-- In the identity-parent phase, executable thread equivalence is ordinary
token identity on the entire fixed carrier. -/
theorem IdentityParents.sameThread_iff
    {state : UnificationState}
    (identity : state.IdentityParents)
    (first second : Nat) :
    state.SameThread first second ↔ first = second := by
  simp [SameThread, identity.representative_eq_all]

/-- The identity-parent phase is an ordered union-find forest. -/
theorem IdentityParents.orderedParents
    {state : UnificationState}
    (identity : state.IdentityParents) :
    state.OrderedParents := by
  intro token parent lookup
  have tokenBound : token < state.parents.size :=
    (Array.getElem?_eq_some_iff.mp lookup).choose
  have self := identity tokenBound
  rw [lookup] at self
  injection self with equality
  exact Nat.le_of_eq equality

/-- Appending the fresh self-parent preserves the identity-parent phase
invariant. -/
theorem IdentityParents.push_fresh
    {state : UnificationState}
    (identity : state.IdentityParents) :
    ∀ {token}, token < (state.parents.push state.parents.size).size →
      (state.parents.push state.parents.size)[token]? = some token := by
  intro token bound
  by_cases fresh : token = state.parents.size
  · subst token
    exact Array.getElem?_push_size
  · rw [Array.getElem?_push, if_neg fresh]
    apply identity
    simpa using Nat.lt_of_le_of_ne
      (Nat.le_of_lt_succ (by simpa using bound)) fresh

/-- Observation-equivalent states satisfy the same abstraction contract. -/
theorem ObservationEquivalent.abstractable
    {certificate : Certificate} {first second : UnificationState}
    (equivalent : first.ObservationEquivalent second)
    (abstractable : first.Abstractable certificate) :
    second.Abstractable certificate := by
  refine {
    markArraySize := by
      rw [← equivalent.marks]
      exact abstractable.markArraySize
    markedVertexBound := ?_
    markedTokenBound := ?_
    representativeBound := ?_
    representativeIdempotent := ?_
  }
  · intro vertex token marked
    apply abstractable.markedVertexBound
    unfold assignedToken? at marked ⊢
    rw [equivalent.marks]
    exact marked
  · intro vertex token marked
    have oldMarked : first.assignedToken? vertex = some token := by
      unfold assignedToken? at marked ⊢
      rw [equivalent.marks]
      exact marked
    rw [← equivalent.parents]
    exact abstractable.markedTokenBound oldMarked
  · intro token bound
    have oldBound : token < first.parents.size := by
      simpa [equivalent.parents] using bound
    simpa [representative, equivalent.parents] using
      abstractable.representativeBound oldBound
  · intro token bound
    have oldBound : token < first.parents.size := by
      simpa [equivalent.parents] using bound
    simpa [representative, equivalent.parents] using
      abstractable.representativeIdempotent oldBound

/-- Observation-equivalent states either both satisfy or both violate the
ordered-parent forest invariant. -/
theorem ObservationEquivalent.orderedParents
    {first second : UnificationState}
    (equivalent : first.ObservationEquivalent second)
    (ordered : first.OrderedParents) :
    second.OrderedParents := by
  intro token parent lookup
  apply ordered
  rw [equivalent.parents]
  exact lookup

/-- Observation-equivalent states either both have identity parent arrays or
both do not. -/
theorem ObservationEquivalent.identityParents
    {first second : UnificationState}
    (equivalent : first.ObservationEquivalent second)
    (identity : first.IdentityParents) :
    second.IdentityParents := by
  intro token bound
  have oldBound : token < first.parents.size := by
    simpa [equivalent.parents] using bound
  have oldLookup := identity oldBound
  simpa [equivalent.parents] using oldLookup

/-- Forget arrays, parsed derivation components, counters, and worklist data,
retaining exactly the marking and thread partition observed by the independent
Figure-5 semantics. -/
def toMarking (state : UnificationState) (certificate : Certificate)
    (abstractable : state.Abstractable certificate) :
    UnificationMarking certificate where
  tokenCount := state.parents.size
  mark := state.assignedToken?
  sameThread := state.SameThread
  sameThreadEquivalence :=
    ⟨fun _ => rfl, fun equality => equality.symm,
      fun first second => first.trans second⟩
  markedVertexBound := abstractable.markedVertexBound
  markedTokenBound := abstractable.markedTokenBound

/-- Abstracting an executable state exposes exactly one token slot per
union-find parent entry. -/
@[simp]
theorem toMarking_tokenCount (state : UnificationState)
    (certificate : Certificate)
    (abstractable : state.Abstractable certificate) :
    (state.toMarking certificate abstractable).tokenCount =
      state.parents.size :=
  rfl

/-- Abstract-state marking lookup is the executable raw assigned token lookup,
before representative normalization. -/
@[simp]
theorem toMarking_mark (state : UnificationState)
    (certificate : Certificate)
    (abstractable : state.Abstractable certificate)
    (vertex : Vertex) :
    (state.toMarking certificate abstractable).mark vertex =
      state.assignedToken? vertex :=
  rfl

/-- Abstract thread equivalence is equality of executable union-find
representatives. -/
@[simp]
theorem toMarking_sameThread (state : UnificationState)
    (certificate : Certificate)
    (abstractable : state.Abstractable certificate)
    (first second : Nat) :
    (state.toMarking certificate abstractable).sameThread first second ↔
      state.representative first = state.representative second :=
  Iff.rfl

/-- Observation-equivalent executable states have identical independent
marking abstractions. -/
theorem ObservationEquivalent.toMarking_eq
    {certificate : Certificate} {first second : UnificationState}
    (equivalent : first.ObservationEquivalent second)
    (abstractable : first.Abstractable certificate) :
    second.toMarking certificate
        (equivalent.abstractable abstractable) =
      first.toMarking certificate abstractable := by
  apply UnificationMarking.ext
  · simp only [toMarking_tokenCount]
    exact congrArg Array.size equivalent.parents.symm
  · funext vertex
    simp only [toMarking_mark]
    unfold assignedToken?
    rw [← equivalent.marks]
  · funext left right
    apply propext
    simp only [toMarking_sameThread]
    unfold representative
    rw [← equivalent.parents]

/-- Apply the token-semantic part of an axiom/start firing: mark both axiom
occurrences with one fresh token and append that token as its own parent. -/
def startMarking (state : UnificationState)
    (left right : Vertex) : UnificationState :=
  let token := state.parents.size
  { state with
    marks :=
      (state.marks.setIfInBounds left (some token))
        |>.setIfInBounds right (some token)
    parents := state.parents.push token
    startedAxioms := state.startedAxioms + 1 }

/-- The start update stays in the pre-union identity-parent phase. -/
theorem IdentityParents.startMarking
    {state : UnificationState}
    (identity : state.IdentityParents)
    (left right : Vertex) :
    (state.startMarking left right).IdentityParents := by
  intro token bound
  change token < (state.parents.push state.parents.size).size at bound
  exact identity.push_fresh bound

/-- Starting an axiom preserves the ordered-forest invariant. -/
theorem OrderedParents.startMarking
    {state : UnificationState}
    (ordered : state.OrderedParents)
    (left right : Vertex) :
    (state.startMarking left right).OrderedParents := by
  intro token parent lookup
  by_cases fresh : token = state.parents.size
  · subst token
    change
      (state.parents.push state.parents.size)[state.parents.size]? =
        some parent at lookup
    rw [Array.getElem?_push_size] at lookup
    injection lookup with equality
    exact Nat.le_of_eq equality.symm
  · apply ordered
    simpa [UnificationState.startMarking,
      Array.getElem?_push, fresh] using lookup

/-- Starting an in-domain axiom in the identity-parent phase preserves the
executable abstraction contract. -/
theorem Abstractable.startMarking
    {certificate : Certificate} {state : UnificationState}
    (abstractable : state.Abstractable certificate)
    (identity : state.IdentityParents)
    {left right : Vertex}
    (leftBound : left < certificate.formulas.size)
    (rightBound : right < certificate.formulas.size) :
    (state.startMarking left right).Abstractable certificate := by
  have nextIdentity :
      (state.startMarking left right).IdentityParents :=
    IdentityParents.startMarking identity left right
  refine {
    markArraySize := by
      simp [UnificationState.startMarking, abstractable.markArraySize]
    markedVertexBound := ?_
    markedTokenBound := ?_
    representativeBound := ?_
    representativeIdempotent := ?_
  }
  · intro vertex token marked
    by_cases atRight : right = vertex
    · simpa [atRight] using rightBound
    · by_cases atLeft : left = vertex
      · simpa [atLeft] using leftBound
      · apply abstractable.markedVertexBound
        simpa [UnificationState.startMarking, assignedToken?,
          Array.getElem?_setIfInBounds, atRight, atLeft] using marked
  · intro vertex token marked
    by_cases atRight : right = vertex
    · subst vertex
      simp [UnificationState.startMarking, assignedToken?, rightBound,
        abstractable.markArraySize] at marked
      subst token
      change state.parents.size <
        (state.parents.push state.parents.size).size
      simp
    · by_cases atLeft : left = vertex
      · subst vertex
        simp [UnificationState.startMarking, assignedToken?, atRight, leftBound,
          abstractable.markArraySize] at marked
        subst token
        change state.parents.size <
          (state.parents.push state.parents.size).size
        simp
      · have oldMarked :
          state.assignedToken? vertex = some token := by
          simpa [UnificationState.startMarking, assignedToken?,
            Array.getElem?_setIfInBounds, atRight, atLeft] using marked
        have oldBound := abstractable.markedTokenBound oldMarked
        simpa [UnificationState.startMarking] using
          Nat.lt_succ_of_lt oldBound
  · intro token bound
    rw [nextIdentity.representative_eq bound]
    exact bound
  · intro token bound
    rw [nextIdentity.representative_eq bound]
    exact nextIdentity.representative_eq bound

/-- In the fixed-carrier abstraction, the next token number exposed by an
identity-parent state is isolated from every allocated token. -/
theorem IdentityParents.toMarking_isFreshToken
    {certificate : Certificate} {state : UnificationState}
    (identity : state.IdentityParents)
    (abstractable : state.Abstractable certificate) :
    (state.toMarking certificate abstractable).IsFreshToken
      (state.toMarking certificate abstractable).tokenCount := by
  intro old oldBound synchronized
  change old < state.parents.size at oldBound
  change state.SameThread old state.parents.size at synchronized
  have equal : old = state.parents.size :=
    (identity.sameThread_iff old state.parents.size).mp synchronized
  omega

/-- Forgetting a concrete axiom/start marking update is exactly the two
abstract `setMark` updates with one fresh token. -/
theorem startMarking_toMarking_mark
    {certificate : Certificate} {state : UnificationState}
    (abstractable : state.Abstractable certificate)
    (identity : state.IdentityParents)
    {left right : Vertex}
    (leftBound : left < certificate.formulas.size)
    (rightBound : right < certificate.formulas.size) :
    ((state.startMarking left right).toMarking certificate
      (abstractable.startMarking identity leftBound rightBound)).mark =
        UnificationMarking.setMark
          (UnificationMarking.setMark
            (state.toMarking certificate abstractable).mark
            left state.parents.size)
          right state.parents.size := by
  funext vertex
  by_cases atRight : vertex = right
  · subst vertex
    simp [UnificationState.startMarking, toMarking, assignedToken?,
      UnificationMarking.setMark, rightBound,
      abstractable.markArraySize]
  · by_cases atLeft : vertex = left
    · subst vertex
      have different : right ≠ left := Ne.symm atRight
      simp [UnificationState.startMarking, toMarking, assignedToken?,
        UnificationMarking.setMark, atRight, different, leftBound,
        abstractable.markArraySize]
    · have rightDifferent : right ≠ vertex := Ne.symm atRight
      have leftDifferent : left ≠ vertex := Ne.symm atLeft
      simp [UnificationState.startMarking, toMarking, assignedToken?,
        UnificationMarking.setMark, atRight, atLeft,
        rightDifferent, leftDifferent]

/-- The concrete token-semantic axiom update refines one independent start
step while union-find parents are still identities. -/
theorem startMarking_startStep
    {certificate : Certificate} {state : UnificationState}
    (abstractable : state.Abstractable certificate)
    (identity : state.IdentityParents)
    {left right : Vertex}
    (linkMembership :
      Link.axiom left right ∈ certificate.links)
    (leftBound : left < certificate.formulas.size)
    (rightBound : right < certificate.formulas.size)
    (leftUnmarked : state.assignedToken? left = none)
    (rightUnmarked : state.assignedToken? right = none) :
    UnificationStep certificate
      (state.toMarking certificate abstractable)
      ((state.startMarking left right).toMarking certificate
        (abstractable.startMarking identity leftBound rightBound)) := by
  apply UnificationStep.start linkMembership
  · exact leftUnmarked
  · exact rightUnmarked
  · exact identity.toMarking_isFreshToken abstractable
  · change (state.parents.push state.parents.size).size =
      state.parents.size + 1
    simp
  · exact state.startMarking_toMarking_mark abstractable identity
      leftBound rightBound
  · intro first second
    change (state.startMarking left right).SameThread first second ↔
      state.SameThread first second
    have nextIdentity :
        (state.startMarking left right).IdentityParents :=
      IdentityParents.startMarking identity left right
    rw [nextIdentity.sameThread_iff, identity.sameThread_iff]

/-- Update one union-find parent pointer without changing marks, parsed
components, or work counters. -/
def setParent (state : UnificationState)
    (token parent : Nat) : UnificationState :=
  { state with
    parents := state.parents.setIfInBounds token parent }

/-- Pointing a token to a no-larger parent preserves the ordered-forest
invariant. -/
theorem OrderedParents.setParent
    {state : UnificationState}
    (ordered : state.OrderedParents)
    {token parent : Nat}
    (parentLe : parent ≤ token) :
    (state.setParent token parent).OrderedParents := by
  intro candidate candidateParent lookup
  by_cases same : token = candidate
  · subst candidate
    by_cases bound : token < state.parents.size
    · simp [UnificationState.setParent, bound] at lookup
      subst candidateParent
      exact parentLe
    · simp [UnificationState.setParent, bound] at lookup
  · apply ordered
    simpa [UnificationState.setParent,
      Array.getElem?_setIfInBounds, same] using lookup

/-- Updating one pointer inside an ordered forest preserves the executable
abstraction contract; the ordered invariant supplies the new representative
bounds and idempotence. -/
theorem Abstractable.setParent
    {certificate : Certificate} {state : UnificationState}
    (abstractable : state.Abstractable certificate)
    (ordered : state.OrderedParents)
    {token parent : Nat}
    (parentLe : parent ≤ token) :
    (state.setParent token parent).Abstractable certificate := by
  have nextOrdered :
      (state.setParent token parent).OrderedParents :=
    OrderedParents.setParent ordered parentLe
  apply nextOrdered.abstractable
  · exact abstractable.markArraySize
  · intro vertex markedToken marked
    apply abstractable.markedVertexBound
    exact marked
  · intro vertex markedToken marked
    have oldBound := abstractable.markedTokenBound marked
    simpa [UnificationState.setParent] using oldBound

/-- Pointing one allocated root at a smaller allocated root changes exactly the
old retired class to the surviving representative. -/
theorem OrderedParents.setParent_representative
    {state : UnificationState}
    (ordered : state.OrderedParents)
    {survivor retired : Nat}
    (survivorBound : survivor < state.parents.size)
    (retiredBound : retired < state.parents.size)
    (survivorLt : survivor < retired)
    (survivorRoot : state.representative survivor = survivor)
    (retiredRoot : state.representative retired = retired)
    {token : Nat} (tokenBound : token < state.parents.size) :
    (state.setParent retired survivor).representative token =
      if state.representative token = retired then
        survivor
      else
        state.representative token := by
  have nextOrdered :
      (state.setParent retired survivor).OrderedParents :=
    OrderedParents.setParent ordered (Nat.le_of_lt survivorLt)
  induction token using Nat.strongRecOn with
  | ind token induction =>
      cases lookup : state.parents[token]? with
      | none =>
          have outOfBounds := Array.getElem?_eq_none_iff.mp lookup
          omega
      | some parent =>
          by_cases atRetired : token = retired
          · subst token
            have nextLookup :
                (state.setParent retired survivor).parents[retired]? =
                  some survivor := by
              simp [UnificationState.setParent, retiredBound]
            have nextRetiredBound :
                retired <
                  (state.setParent retired survivor).parents.size := by
              simpa [UnificationState.setParent] using retiredBound
            have nextStep :=
              nextOrdered.representative_eq_representative_parent
                nextRetiredBound nextLookup
            have survivorLookup :
                state.parents[survivor]? = some survivor :=
              ordered.lookup_self_of_representative_eq
                survivorBound survivorRoot
            have different : retired ≠ survivor := by
              omega
            have nextSurvivorLookup :
                (state.setParent retired survivor).parents[survivor]? =
                  some survivor := by
              simpa [UnificationState.setParent,
                Array.getElem?_setIfInBounds, different] using
                survivorLookup
            have nextSurvivorRoot :
                (state.setParent retired survivor).representative survivor =
                  survivor :=
              representative_eq_of_lookup_self nextSurvivorLookup
            rw [nextStep, nextSurvivorRoot, retiredRoot]
            simp
          · have different : retired ≠ token := Ne.symm atRetired
            have nextLookup :
                (state.setParent retired survivor).parents[token]? =
                  some parent := by
              simpa [UnificationState.setParent,
                Array.getElem?_setIfInBounds, different] using lookup
            have nextTokenBound :
                token <
                  (state.setParent retired survivor).parents.size := by
              simpa [UnificationState.setParent] using tokenBound
            have nextStep :=
              nextOrdered.representative_eq_representative_parent
                nextTokenBound nextLookup
            have oldStep :=
              ordered.representative_eq_representative_parent
                tokenBound lookup
            by_cases self : parent = token
            · subst parent
              have oldRoot : state.representative token = token :=
                representative_eq_of_lookup_self lookup
              have nextRoot :
                  (state.setParent retired survivor).representative token =
                    token :=
                representative_eq_of_lookup_self nextLookup
              rw [oldRoot, nextRoot]
              simp [atRetired]
            · have parentLt : parent < token := by
                have parentLe := ordered lookup
                omega
              have parentBound : parent < state.parents.size := by
                omega
              rw [nextStep, oldStep,
                induction parent parentLt parentBound]

/-- The executable same-thread relation after a root update is exactly the
equivalence closure that merges the surviving and retired old classes. -/
theorem OrderedParents.setParent_sameThread
    {state : UnificationState}
    (ordered : state.OrderedParents)
    {survivor retired : Nat}
    (survivorBound : survivor < state.parents.size)
    (retiredBound : retired < state.parents.size)
    (survivorLt : survivor < retired)
    (survivorRoot : state.representative survivor = survivor)
    (retiredRoot : state.representative retired = retired)
    {first second : Nat}
    (firstBound : first < state.parents.size)
    (secondBound : second < state.parents.size) :
    (state.setParent retired survivor).SameThread first second ↔
      state.SameThread first second ∨
        ((state.SameThread first survivor ∨
            state.SameThread first retired) ∧
          (state.SameThread second survivor ∨
            state.SameThread second retired)) := by
  unfold SameThread
  rw [ordered.setParent_representative survivorBound retiredBound
      survivorLt survivorRoot retiredRoot firstBound,
    ordered.setParent_representative survivorBound retiredBound
      survivorLt survivorRoot retiredRoot secondBound]
  have different : survivor ≠ retired := Nat.ne_of_lt survivorLt
  by_cases firstRetired :
      state.representative first = retired
  · by_cases secondRetired :
        state.representative second = retired
    · simp [firstRetired, secondRetired, survivorRoot,
        retiredRoot]
    · simp [firstRetired, secondRetired, survivorRoot,
        retiredRoot, eq_comm]
      intro equality
      exact (secondRetired equality.symm).elim
  · by_cases secondRetired :
        state.representative second = retired
    · simp [firstRetired, secondRetired, survivorRoot,
        retiredRoot, different, eq_comm]
    · simp [firstRetired, secondRetired, survivorRoot,
        retiredRoot]
      intro firstSurvivor secondSurvivor
      exact firstSurvivor.trans secondSurvivor.symm

/-- The root-update characterization holds on the full fixed `Nat` carrier,
including unallocated singleton elements. -/
theorem OrderedParents.setParent_sameThread_all
    {state : UnificationState}
    (ordered : state.OrderedParents)
    {survivor retired : Nat}
    (survivorBound : survivor < state.parents.size)
    (retiredBound : retired < state.parents.size)
    (survivorLt : survivor < retired)
    (survivorRoot : state.representative survivor = survivor)
    (retiredRoot : state.representative retired = retired)
    (first second : Nat) :
    (state.setParent retired survivor).SameThread first second ↔
      state.SameThread first second ∨
        ((state.SameThread first survivor ∨
            state.SameThread first retired) ∧
          (state.SameThread second survivor ∨
            state.SameThread second retired)) := by
  have nextOrdered :
      (state.setParent retired survivor).OrderedParents :=
    OrderedParents.setParent ordered (Nat.le_of_lt survivorLt)
  by_cases firstBound : first < state.parents.size
  · by_cases secondBound : second < state.parents.size
    · exact ordered.setParent_sameThread survivorBound retiredBound
        survivorLt survivorRoot retiredRoot firstBound secondBound
    · have secondOut : state.parents.size ≤ second :=
        Nat.le_of_not_gt secondBound
      have oldSecond :
          state.representative second = second :=
        representative_eq_of_size_le state secondOut
      have nextSecond :
          (state.setParent retired survivor).representative second =
            second :=
        representative_eq_of_size_le
          (state.setParent retired survivor) (by
            simpa [UnificationState.setParent] using secondOut)
      have oldFirstBound :
          state.representative first < state.parents.size :=
        ordered.representative_lt firstBound
      have nextFirstBound :
          (state.setParent retired survivor).representative first <
            state.parents.size := by
        have allocated :
            first < (state.setParent retired survivor).parents.size := by
          simpa [UnificationState.setParent] using firstBound
        simpa [UnificationState.setParent] using
          nextOrdered.representative_lt allocated
      unfold SameThread
      rw [oldSecond, nextSecond, survivorRoot, retiredRoot]
      have oldDifferent :
          state.representative first ≠ second := by omega
      have nextDifferent :
          (state.setParent retired survivor).representative first ≠
            second := by omega
      have survivorDifferent : second ≠ survivor := by omega
      have retiredDifferent : second ≠ retired := by omega
      simp [oldDifferent, nextDifferent,
        survivorDifferent, retiredDifferent]
  · have firstOut : state.parents.size ≤ first :=
      Nat.le_of_not_gt firstBound
    by_cases secondBound : second < state.parents.size
    · have oldFirst :
          state.representative first = first :=
        representative_eq_of_size_le state firstOut
      have nextFirst :
          (state.setParent retired survivor).representative first =
            first :=
        representative_eq_of_size_le
          (state.setParent retired survivor) (by
            simpa [UnificationState.setParent] using firstOut)
      have oldSecondBound :
          state.representative second < state.parents.size :=
        ordered.representative_lt secondBound
      have nextSecondBound :
          (state.setParent retired survivor).representative second <
            state.parents.size := by
        have allocated :
            second < (state.setParent retired survivor).parents.size := by
          simpa [UnificationState.setParent] using secondBound
        simpa [UnificationState.setParent] using
          nextOrdered.representative_lt allocated
      unfold SameThread
      rw [oldFirst, nextFirst, survivorRoot, retiredRoot]
      have oldDifferent :
          first ≠ state.representative second := by omega
      have nextDifferent :
          first ≠
            (state.setParent retired survivor).representative second := by
        omega
      have survivorDifferent : first ≠ survivor := by omega
      have retiredDifferent : first ≠ retired := by omega
      simp [oldDifferent, nextDifferent,
        survivorDifferent, retiredDifferent]
    · have secondOut : state.parents.size ≤ second :=
        Nat.le_of_not_gt secondBound
      have oldFirst :
          state.representative first = first :=
        representative_eq_of_size_le state firstOut
      have oldSecond :
          state.representative second = second :=
        representative_eq_of_size_le state secondOut
      have nextFirst :
          (state.setParent retired survivor).representative first =
            first :=
        representative_eq_of_size_le
          (state.setParent retired survivor) (by
            simpa [UnificationState.setParent] using firstOut)
      have nextSecond :
          (state.setParent retired survivor).representative second =
            second :=
        representative_eq_of_size_le
          (state.setParent retired survivor) (by
            simpa [UnificationState.setParent] using secondOut)
      unfold SameThread
      rw [oldFirst, oldSecond, nextFirst, nextSecond,
        survivorRoot, retiredRoot]
      have firstSurvivor : first ≠ survivor := by omega
      have firstRetired : first ≠ retired := by omega
      have secondSurvivor : second ≠ survivor := by omega
      have secondRetired : second ≠ retired := by omega
      simp [firstSurvivor, firstRetired,
        secondSurvivor, secondRetired]

/-- Mark one connective conclusion and increment the connective counter,
without changing the token partition or parsed components. -/
def markConclusion (state : UnificationState)
    (conclusion token : Nat) : UnificationState :=
  { state with
    marks := state.marks.setIfInBounds conclusion (some token)
    firedConnectives := state.firedConnectives + 1 }

/-- Marking a conclusion leaves the ordered parent forest unchanged. -/
theorem OrderedParents.markConclusion
    {state : UnificationState}
    (ordered : state.OrderedParents)
    (conclusion token : Nat) :
    (state.markConclusion conclusion token).OrderedParents := by
  intro candidate parent lookup
  apply ordered
  exact lookup

/-- Mark one tensor conclusion and point the retired representative at the
surviving representative. Parsed components remain outside this token-semantic
update. -/
def mergeConclusion (state : UnificationState)
    (conclusion representative retired : Nat) : UnificationState :=
  (state.markConclusion conclusion representative)
    |>.setParent retired representative

/-- The token-semantic tensor update preserves ordered parents when the chosen
representative is no larger than the retired root. -/
theorem OrderedParents.mergeConclusion
    {state : UnificationState}
    (ordered : state.OrderedParents)
    (conclusion representative retired : Nat)
    (representativeLe : representative ≤ retired) :
    (state.mergeConclusion conclusion representative retired)
      |>.OrderedParents := by
  have markedOrdered :
      (state.markConclusion conclusion representative).OrderedParents :=
    OrderedParents.markConclusion ordered conclusion representative
  have mergedOrdered :
      ((state.markConclusion conclusion representative)
        |>.setParent retired representative).OrderedParents :=
    OrderedParents.setParent markedOrdered representativeLe
  change ((state.markConclusion conclusion representative)
    |>.setParent retired representative).OrderedParents
  exact mergedOrdered

/-- Marking an in-domain conclusion with an allocated token preserves the
executable-to-abstract-state contract. -/
theorem Abstractable.markConclusion
    {certificate : Certificate} {state : UnificationState}
    (abstractable : state.Abstractable certificate)
    {conclusion token : Nat}
    (conclusionBound : conclusion < certificate.formulas.size)
    (tokenBound : token < state.parents.size) :
    (state.markConclusion conclusion token).Abstractable certificate := by
  refine {
    markArraySize := by
      simp [UnificationState.markConclusion,
        abstractable.markArraySize]
    markedVertexBound := ?_
    markedTokenBound := ?_
    representativeBound := abstractable.representativeBound
    representativeIdempotent := abstractable.representativeIdempotent
  }
  · intro vertex markedToken marked
    by_cases same : conclusion = vertex
    · simpa [same] using conclusionBound
    · apply abstractable.markedVertexBound
      simpa [UnificationState.markConclusion, assignedToken?,
        Array.getElem?_setIfInBounds, same] using marked
  · intro vertex markedToken marked
    by_cases same : conclusion = vertex
    · subst vertex
      simp [UnificationState.markConclusion, assignedToken?,
        conclusionBound, abstractable.markArraySize] at marked
      subst markedToken
      exact tokenBound
    · apply abstractable.markedTokenBound
      simpa [UnificationState.markConclusion, assignedToken?,
        Array.getElem?_setIfInBounds, same] using marked

/-- Marking a tensor conclusion and merging two ordered roots preserves the
full executable abstraction contract. -/
theorem Abstractable.mergeConclusion
    {certificate : Certificate} {state : UnificationState}
    (abstractable : state.Abstractable certificate)
    (ordered : state.OrderedParents)
    {conclusion representative retired : Nat}
    (conclusionBound : conclusion < certificate.formulas.size)
    (representativeBound : representative < state.parents.size)
    (representativeLe : representative ≤ retired) :
    (state.mergeConclusion conclusion representative retired)
      |>.Abstractable certificate := by
  have markedAbstractable :
      (state.markConclusion conclusion representative)
        |>.Abstractable certificate :=
    Abstractable.markConclusion abstractable
      conclusionBound representativeBound
  have markedOrdered :
      (state.markConclusion conclusion representative).OrderedParents :=
    OrderedParents.markConclusion ordered conclusion representative
  change ((state.markConclusion conclusion representative)
    |>.setParent retired representative).Abstractable certificate
  exact Abstractable.setParent markedAbstractable
    markedOrdered representativeLe

/-- Forgetting a concrete conclusion-marking update is exactly the abstract
`setMark` update; scheduler counters and parsed components are invisible. -/
theorem markConclusion_toMarking_mark
    {certificate : Certificate} {state : UnificationState}
    (abstractable : state.Abstractable certificate)
    {conclusion token : Nat}
    (conclusionBound : conclusion < certificate.formulas.size)
    (tokenBound : token < state.parents.size) :
    ((state.markConclusion conclusion token).toMarking certificate
      (abstractable.markConclusion conclusionBound tokenBound)).mark =
        UnificationMarking.setMark
          (state.toMarking certificate abstractable).mark
          conclusion token := by
  funext vertex
  by_cases same : vertex = conclusion
  · subst vertex
    simp [UnificationState.markConclusion, toMarking, assignedToken?,
      UnificationMarking.setMark, conclusionBound,
      abstractable.markArraySize]
  · have different : conclusion ≠ vertex := Ne.symm same
    simp [UnificationState.markConclusion, toMarking, assignedToken?,
      UnificationMarking.setMark, same, different]

/-- Merging two token classes does not add any further raw marks beyond the
conclusion mark performed before the parent update. -/
theorem mergeConclusion_toMarking_mark
    {certificate : Certificate} {state : UnificationState}
    (abstractable : state.Abstractable certificate)
    (ordered : state.OrderedParents)
    {conclusion representative retired : Nat}
    (conclusionBound : conclusion < certificate.formulas.size)
    (representativeBound : representative < state.parents.size)
    (representativeLe : representative ≤ retired) :
    ((state.mergeConclusion conclusion representative retired).toMarking
      certificate
      (abstractable.mergeConclusion ordered conclusionBound
        representativeBound representativeLe)).mark =
        UnificationMarking.setMark
          (state.toMarking certificate abstractable).mark
          conclusion representative := by
  funext vertex
  by_cases same : vertex = conclusion
  · subst vertex
    simp [UnificationState.mergeConclusion, UnificationState.setParent,
      UnificationState.markConclusion, toMarking, assignedToken?,
      UnificationMarking.setMark, conclusionBound,
      abstractable.markArraySize]
  · have different : conclusion ≠ vertex := Ne.symm same
    simp [UnificationState.mergeConclusion, UnificationState.setParent,
      UnificationState.markConclusion, toMarking, assignedToken?,
      UnificationMarking.setMark, same, different]

/-- The concrete marking update refines the independent forward rule whenever
the executable guards and submitted par-link membership hold. Component
construction is deliberately outside this proof-irrelevant theorem. -/
theorem markConclusion_forwardStep
    {certificate : Certificate} {state : UnificationState}
    (abstractable : state.Abstractable certificate)
    {left right conclusion : Vertex}
    {leftToken rightToken outputToken : Nat}
    (linkMembership :
      Link.par left right conclusion ∈ certificate.links)
    (conclusionBound : conclusion < certificate.formulas.size)
    (conclusionUnmarked : state.assignedToken? conclusion = none)
    (leftMarked : state.assignedToken? left = some leftToken)
    (rightMarked : state.assignedToken? right = some rightToken)
    (premisesSynchronized : state.SameThread leftToken rightToken)
    (outputTokenAllocated : outputToken < state.parents.size)
    (outputTokenSynchronized :
      state.SameThread outputToken leftToken) :
    UnificationStep certificate
      (state.toMarking certificate abstractable)
      ((state.markConclusion conclusion outputToken).toMarking certificate
        (abstractable.markConclusion conclusionBound
          outputTokenAllocated)) := by
  apply UnificationStep.forward linkMembership
  · exact conclusionUnmarked
  · exact leftMarked
  · exact rightMarked
  · exact premisesSynchronized
  · exact outputTokenAllocated
  · exact outputTokenSynchronized
  · rfl
  · exact state.markConclusion_toMarking_mark abstractable
      conclusionBound outputTokenAllocated
  · rfl

/-- Current token class yielded by a marked formula occurrence. -/
def tokenAt? (state : UnificationState) (vertex : Vertex) : Option Nat := do
  let assigned ← state.marks[vertex]?
  let token ← assigned
  pure (state.representative token)

/-- Check exactly the token-level guards of a unary/par forward firing and
return the representative token to place on the conclusion. -/
def forwardToken? (state : UnificationState)
    (left right conclusion : Vertex) : Option Nat :=
  match state.marks[conclusion]? with
  | some none =>
      match state.tokenAt? left with
      | some leftToken =>
          match state.tokenAt? right with
          | some rightToken =>
              if leftToken == rightToken then some leftToken else none
          | none => none
      | none => none
  | _ => none

/-- A successful token-level forward check exposes every executable guard and
uses the same representative for both premises. -/
theorem forwardToken?_success
    {state : UnificationState}
    {left right conclusion outputToken : Nat}
    (equation :
      state.forwardToken? left right conclusion = some outputToken) :
    state.marks[conclusion]? = some none ∧
      state.tokenAt? left = some outputToken ∧
      state.tokenAt? right = some outputToken := by
  unfold forwardToken? at equation
  split at equation <;> simp_all
  split at equation <;> simp_all
  split at equation <;> simp_all

/-- Check exactly the token-level guards of a binary/tensor unify firing and
return its two distinct current representatives. -/
def unifyTokens? (state : UnificationState)
    (left right conclusion : Vertex) : Option (Nat × Nat) :=
  match state.marks[conclusion]? with
  | some none =>
      match state.tokenAt? left with
      | some leftToken =>
          match state.tokenAt? right with
          | some rightToken =>
              if leftToken == rightToken then none
              else some (leftToken, rightToken)
          | none => none
      | none => none
  | _ => none

/-- A successful token-level unify check exposes every executable guard and
returns two distinct representatives. -/
theorem unifyTokens?_success
    {state : UnificationState}
    {left right conclusion leftToken rightToken : Nat}
    (equation :
      state.unifyTokens? left right conclusion =
        some (leftToken, rightToken)) :
    state.marks[conclusion]? = some none ∧
      state.tokenAt? left = some leftToken ∧
      state.tokenAt? right = some rightToken ∧
      leftToken ≠ rightToken := by
  unfold unifyTokens? at equation
  split at equation <;> simp_all
  split at equation <;> simp_all
  split at equation <;> simp_all
  omega

/-- A successful representative lookup always comes from a concrete raw mark
on the queried occurrence. -/
theorem tokenAt?_some_witness
    {state : UnificationState} {vertex token : Nat}
    (yielded : state.tokenAt? vertex = some token) :
    ∃ rawToken,
      state.assignedToken? vertex = some rawToken ∧
        state.representative rawToken = token := by
  unfold tokenAt? at yielded
  cases lookup : state.marks[vertex]? with
  | none =>
      rw [lookup] at yielded
      contradiction
  | some assigned =>
      rw [lookup] at yielded
      cases assigned with
      | none =>
          contradiction
      | some rawToken =>
          injection yielded with representativeEquation
          exact ⟨rawToken, by
            unfold assignedToken?
            rw [lookup]
            rfl, representativeEquation⟩

/-- Every raw-assigned occurrence exposes some current representative token. -/
theorem tokenAt?_exists_of_assigned
    {state : UnificationState} {vertex : Vertex}
    (assigned : state.assignedToken? vertex ≠ none) :
    ∃ token, state.tokenAt? vertex = some token := by
  cases lookup : state.assignedToken? vertex with
  | none =>
      exact False.elim (assigned lookup)
  | some rawToken =>
      have rawLookup :
          state.marks[vertex]? = some (some rawToken) :=
        assignedToken?_some_raw lookup
      exact ⟨state.representative rawToken, by
        unfold tokenAt?
        rw [rawLookup]
        rfl⟩

/-- In an abstractable state, the representative returned by `tokenAt?` lies
in the same semantic thread as its witnessed raw mark. -/
theorem Abstractable.tokenAt?_sameThread_witness
    {certificate : Certificate} {state : UnificationState}
    (abstractable : state.Abstractable certificate)
    {vertex token : Nat}
    (yielded : state.tokenAt? vertex = some token) :
    ∃ rawToken,
      state.assignedToken? vertex = some rawToken ∧
        state.SameThread token rawToken := by
  rcases state.tokenAt?_some_witness yielded with
    ⟨rawToken, marked, representativeEquation⟩
  refine ⟨rawToken, marked, ?_⟩
  unfold SameThread
  rw [← representativeEquation]
  apply abstractable.representativeIdempotent
  exact abstractable.markedTokenBound marked

/-- Every representative yielded by a marked occurrence in an abstractable
executable state remains inside the allocated union-find token range. -/
theorem Abstractable.tokenAt?_bound
    {certificate : Certificate} {state : UnificationState}
    (abstractable : state.Abstractable certificate)
    {vertex token : Nat}
    (yielded : state.tokenAt? vertex = some token) :
    token < state.parents.size := by
  unfold tokenAt? at yielded
  cases lookup : state.marks[vertex]? with
  | none =>
      rw [lookup] at yielded
      contradiction
  | some assigned =>
      rw [lookup] at yielded
      cases assigned with
      | none =>
          contradiction
      | some rawToken =>
          injection yielded with representativeEquation
          subst token
          apply abstractable.representativeBound
          apply abstractable.markedTokenBound
            (vertex := vertex) (token := rawToken)
          unfold assignedToken?
          rw [lookup]
          rfl

/-- A token returned by `tokenAt?` is a union-find root whenever the state is
abstractable. -/
theorem Abstractable.tokenAt?_root
    {certificate : Certificate} {state : UnificationState}
    (abstractable : state.Abstractable certificate)
    {vertex token : Nat}
    (yielded : state.tokenAt? vertex = some token) :
    state.representative token = token := by
  rcases state.tokenAt?_some_witness yielded with
    ⟨rawToken, marked, representativeEquation⟩
  rw [← representativeEquation]
  exact abstractable.representativeIdempotent
    (abstractable.markedTokenBound marked)

/-- A successful executable forward-token check, together with submitted link
membership, produces one independent forward step and a valid updated
abstraction. -/
theorem forwardToken?_refines
    {certificate : Certificate} {state : UnificationState}
    (abstractable : state.Abstractable certificate)
    {left right conclusion outputToken : Nat}
    (linkMembership :
      Link.par left right conclusion ∈ certificate.links)
    (equation :
      state.forwardToken? left right conclusion = some outputToken) :
    ∃ nextAbstractable :
        (state.markConclusion conclusion outputToken)
          |>.Abstractable certificate,
      UnificationStep certificate
        (state.toMarking certificate abstractable)
        ((state.markConclusion conclusion outputToken).toMarking
          certificate nextAbstractable) := by
  have guards := state.forwardToken?_success equation
  have conclusionIndexBound : conclusion < state.marks.size :=
    (Array.getElem?_eq_some_iff.mp guards.1).1
  have conclusionBound : conclusion < certificate.formulas.size := by
    simpa [abstractable.markArraySize] using conclusionIndexBound
  have conclusionUnmarked :
      state.assignedToken? conclusion = none := by
    unfold assignedToken?
    rw [guards.1]
    rfl
  rcases abstractable.tokenAt?_sameThread_witness guards.2.1 with
    ⟨leftRawToken, leftMarked, outputSynchronizedLeft⟩
  rcases abstractable.tokenAt?_sameThread_witness guards.2.2 with
    ⟨rightRawToken, rightMarked, outputSynchronizedRight⟩
  have premisesSynchronized :
      state.SameThread leftRawToken rightRawToken := by
    unfold SameThread at outputSynchronizedLeft outputSynchronizedRight ⊢
    exact outputSynchronizedLeft.symm.trans outputSynchronizedRight
  have outputAllocated : outputToken < state.parents.size :=
    abstractable.tokenAt?_bound guards.2.1
  let nextAbstractable :=
    abstractable.markConclusion conclusionBound outputAllocated
  refine ⟨nextAbstractable, ?_⟩
  exact state.markConclusion_forwardStep abstractable linkMembership
    conclusionBound conclusionUnmarked leftMarked rightMarked
    premisesSynchronized outputAllocated outputSynchronizedLeft

/-- A successful executable tensor guard refines exactly one independent
Figure-5 unify step. The proof relates raw premise marks, their current
representatives, the ordered root update, and the full fixed-carrier thread
relation; parsed component construction remains observationally irrelevant. -/
theorem unifyTokens?_refines
    {certificate : Certificate} {state : UnificationState}
    (abstractable : state.Abstractable certificate)
    (ordered : state.OrderedParents)
    {left right conclusion leftRepresentative rightRepresentative : Nat}
    (linkMembership :
      Link.tensor left right conclusion ∈ certificate.links)
    (equation :
      state.unifyTokens? left right conclusion =
        some (leftRepresentative, rightRepresentative)) :
    ∃ nextAbstractable :
        (state.mergeConclusion conclusion
          (min leftRepresentative rightRepresentative)
          (max leftRepresentative rightRepresentative))
          |>.Abstractable certificate,
      UnificationStep certificate
        (state.toMarking certificate abstractable)
        ((state.mergeConclusion conclusion
          (min leftRepresentative rightRepresentative)
          (max leftRepresentative rightRepresentative)).toMarking
            certificate nextAbstractable) := by
  have guards := state.unifyTokens?_success equation
  have conclusionIndexBound : conclusion < state.marks.size :=
    (Array.getElem?_eq_some_iff.mp guards.1).1
  have conclusionBound : conclusion < certificate.formulas.size := by
    simpa [abstractable.markArraySize] using conclusionIndexBound
  have conclusionUnmarked :
      state.assignedToken? conclusion = none := by
    unfold assignedToken?
    rw [guards.1]
    rfl
  rcases abstractable.tokenAt?_sameThread_witness guards.2.1 with
    ⟨leftRawToken, leftMarked, leftSynchronized⟩
  rcases abstractable.tokenAt?_sameThread_witness guards.2.2.1 with
    ⟨rightRawToken, rightMarked, rightSynchronized⟩
  have leftBound : leftRepresentative < state.parents.size :=
    abstractable.tokenAt?_bound guards.2.1
  have rightBound : rightRepresentative < state.parents.size :=
    abstractable.tokenAt?_bound guards.2.2.1
  have leftRoot :
      state.representative leftRepresentative = leftRepresentative :=
    abstractable.tokenAt?_root guards.2.1
  have rightRoot :
      state.representative rightRepresentative = rightRepresentative :=
    abstractable.tokenAt?_root guards.2.2.1
  have representativesDistinct :
      leftRepresentative ≠ rightRepresentative :=
    guards.2.2.2
  have premisesDistinct :
      ¬state.SameThread leftRawToken rightRawToken := by
    intro synchronized
    apply representativesDistinct
    unfold SameThread at leftSynchronized rightSynchronized synchronized
    rw [leftRoot] at leftSynchronized
    rw [rightRoot] at rightSynchronized
    exact leftSynchronized.trans
      (synchronized.trans rightSynchronized.symm)
  have survivorBound :
      min leftRepresentative rightRepresentative <
        state.parents.size :=
    Nat.lt_of_le_of_lt
      (Nat.min_le_left leftRepresentative rightRepresentative)
      leftBound
  have retiredBound :
      max leftRepresentative rightRepresentative <
        state.parents.size :=
    Nat.max_lt.mpr ⟨leftBound, rightBound⟩
  have survivorLt :
      min leftRepresentative rightRepresentative <
        max leftRepresentative rightRepresentative := by
    rcases Nat.lt_or_gt_of_ne representativesDistinct with
      leftLess | rightLess
    · simpa [Nat.min_eq_left (Nat.le_of_lt leftLess),
        Nat.max_eq_right (Nat.le_of_lt leftLess)] using leftLess
    · simpa [Nat.min_eq_right (Nat.le_of_lt rightLess),
        Nat.max_eq_left (Nat.le_of_lt rightLess)] using rightLess
  have survivorRoot :
      state.representative
          (min leftRepresentative rightRepresentative) =
        min leftRepresentative rightRepresentative := by
    rcases Nat.lt_or_gt_of_ne representativesDistinct with
      leftLess | rightLess
    · simpa [Nat.min_eq_left (Nat.le_of_lt leftLess)] using leftRoot
    · simpa [Nat.min_eq_right (Nat.le_of_lt rightLess)] using rightRoot
  have retiredRoot :
      state.representative
          (max leftRepresentative rightRepresentative) =
        max leftRepresentative rightRepresentative := by
    rcases Nat.lt_or_gt_of_ne representativesDistinct with
      leftLess | rightLess
    · simpa [Nat.max_eq_right (Nat.le_of_lt leftLess)] using rightRoot
    · simpa [Nat.max_eq_left (Nat.le_of_lt rightLess)] using leftRoot
  have outputFromPremise :
      state.SameThread
          (min leftRepresentative rightRepresentative) leftRawToken ∨
        state.SameThread
          (min leftRepresentative rightRepresentative)
          rightRawToken := by
    rcases Nat.lt_or_gt_of_ne representativesDistinct with
      leftLess | rightLess
    · exact Or.inl (by
        simpa [Nat.min_eq_left (Nat.le_of_lt leftLess)] using
          leftSynchronized)
    · exact Or.inr (by
        simpa [Nat.min_eq_right (Nat.le_of_lt rightLess)] using
          rightSynchronized)
  let nextAbstractable :=
    abstractable.mergeConclusion ordered conclusionBound survivorBound
      (Nat.le_of_lt survivorLt)
  refine ⟨nextAbstractable, ?_⟩
  apply UnificationStep.unify linkMembership
  · exact conclusionUnmarked
  · exact leftMarked
  · exact rightMarked
  · exact premisesDistinct
  · exact survivorBound
  · exact outputFromPremise
  · simp [UnificationState.mergeConclusion,
      UnificationState.markConclusion, UnificationState.setParent]
  · exact state.mergeConclusion_toMarking_mark abstractable ordered
      conclusionBound survivorBound (Nat.le_of_lt survivorLt)
  · intro first second
    have rootMerge :=
      ordered.setParent_sameThread_all survivorBound retiredBound
        survivorLt survivorRoot retiredRoot first second
    have representativeMerge :
        (state.toMarking certificate abstractable).MergeExtension
            (min leftRepresentative rightRepresentative)
            (max leftRepresentative rightRepresentative) =
          (state.toMarking certificate abstractable).MergeExtension
            leftRepresentative rightRepresentative := by
      rcases Nat.lt_or_gt_of_ne representativesDistinct with
        leftLess | rightLess
      · simp [Nat.min_eq_left (Nat.le_of_lt leftLess),
          Nat.max_eq_right (Nat.le_of_lt leftLess)]
      · rw [Nat.min_eq_right (Nat.le_of_lt rightLess),
          Nat.max_eq_left (Nat.le_of_lt rightLess)]
        exact
          UnificationMarking.mergeExtension_comm
            (state.toMarking certificate abstractable)
            rightRepresentative leftRepresentative
    have rawMerge :
        (state.toMarking certificate abstractable).MergeExtension
            leftRepresentative rightRepresentative =
          (state.toMarking certificate abstractable).MergeExtension
            leftRawToken rightRawToken :=
      UnificationMarking.mergeExtension_congr
        (state.toMarking certificate abstractable)
        leftSynchronized rightSynchronized
    change
      (state.setParent
          (max leftRepresentative rightRepresentative)
          (min leftRepresentative rightRepresentative)).SameThread
            first second ↔
        (state.toMarking certificate abstractable).MergeExtension
          leftRawToken rightRawToken first second
    rw [rootMerge]
    change
      (state.toMarking certificate abstractable).MergeExtension
          (min leftRepresentative rightRepresentative)
          (max leftRepresentative rightRepresentative) first second ↔
        (state.toMarking certificate abstractable).MergeExtension
          leftRawToken rightRawToken first second
    rw [representativeMerge, rawMerge]

/-- Live parsed component for a representative token. -/
def componentAt? (state : UnificationState) (token : Nat) :
    Option UnificationComponent := do
  let component ← state.components[state.representative token]?
  component

/-- A successful live-component lookup exposes the exact nested array entry
at the current representative. -/
theorem componentAt?_some_raw
    {state : UnificationState} {token : Nat}
    {component : UnificationComponent}
    (yielded : state.componentAt? token = some component) :
    state.components[state.representative token]? =
      some (some component) := by
  unfold componentAt? at yielded
  cases lookup :
      state.components[state.representative token]? with
  | none =>
      simp [lookup] at yielded
  | some assigned =>
      cases assigned with
      | none =>
          simp [lookup] at yielded
      | some stored =>
          simp [lookup] at yielded
          subst stored
          rfl

/-- Every marked premise of a still-unfired connective is exposed by the live
parsed component of its current token representative.  Consumed premises stay
marked permanently, so requiring *all* marked occurrences to remain on a
frontier would be false; the pending-link qualification is essential. -/
def PendingPremisesCovered (certificate : Certificate)
    (state : UnificationState) : Prop :=
  ∀ {link : Link}, link ∈ certificate.links →
    match link with
    | .axiom _ _ => True
    | .par left right conclusion
    | .tensor left right conclusion =>
        state.marks[conclusion]? = some none →
          ∀ {premise token : Nat}, premise ∈ [left, right] →
            state.tokenAt? premise = some token →
              ∃ component,
                state.componentAt? token = some component ∧
                  premise ∈ component.frontier

/-- A list filtered to one accepted value cannot contain two different
accepted members. -/
private theorem mem_filter_length_one_unique
    {α : Type} {values : List α} {predicate : α → Bool}
    {first second : α}
    (count : (values.filter predicate).length = 1)
    (firstMembership : first ∈ values)
    (firstAccepted : predicate first = true)
    (secondMembership : second ∈ values)
    (secondAccepted : predicate second = true) :
    first = second := by
  have firstFiltered : first ∈ values.filter predicate := by
    simp [firstMembership, firstAccepted]
  have secondFiltered : second ∈ values.filter predicate := by
    simp [secondMembership, secondAccepted]
  rcases List.length_eq_one_iff.mp count with
    ⟨only, filterEquation⟩
  rw [filterEquation] at firstFiltered secondFiltered
  simp at firstFiltered secondFiltered
  exact firstFiltered.trans secondFiltered.symm

/-- Structural resource ownership makes the parent connective of every
premise occurrence unique.  This is the exact linear-use fact needed to show
that firing one link cannot consume a frontier occurrence still needed by a
different pending link. -/
theorem StructurallyWellFormed.parentLink_unique
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {premise : Vertex} {first second : Link}
    (firstMembership : first ∈ certificate.links)
    (firstPremise : premise ∈ first.premises)
    (secondMembership : second ∈ certificate.links)
    (secondPremise : premise ∈ second.premises) :
    first = second := by
  have firstWellFormed :=
    structural.2.2.2.2.1 first firstMembership
  have premiseBound : premise < certificate.formulas.size := by
    cases first with
    | «axiom» left right =>
        simp [Link.premises] at firstPremise
    | tensor left right conclusion =>
        rcases firstWellFormed with
          ⟨_, _, _, leftBound, rightBound, _, _⟩
        simp [Link.premises] at firstPremise
        rcases firstPremise with rfl | rfl
        · exact leftBound
        · exact rightBound
    | «par» left right conclusion =>
        rcases firstWellFormed with
          ⟨_, _, _, leftBound, rightBound, _, _⟩
        simp [Link.premises] at firstPremise
        rcases firstPremise with rfl | rfl
        · exact leftBound
        · exact rightBound
  have firstUses : first.usesAsPremise premise = true := by
    simpa [Link.usesAsPremise] using firstPremise
  have secondUses : second.usesAsPremise premise = true := by
    simpa [Link.usesAsPremise] using secondPremise
  have node := structural.2.2.2.2.2 premise premiseBound
  have notBoundary : premise ∉ certificate.conclusions := by
    intro boundary
    have parentZero : certificate.parentUseCount premise = 0 := by
      simpa [boundary] using node.2
    have filtered :
        first ∈ certificate.links.filter
          (·.usesAsPremise premise) := by
      simp [firstMembership, firstUses]
    have positive := List.length_pos_of_mem filtered
    unfold Certificate.parentUseCount at parentZero
    omega
  have parentCount : certificate.parentUseCount premise = 1 := by
    simpa [notBoundary] using node.2
  unfold Certificate.parentUseCount at parentCount
  exact mem_filter_length_one_unique parentCount
    firstMembership firstUses secondMembership secondUses

/-- Structural ownership also makes the connective producer of every
compound occurrence unique, including across the tensor/par constructors. -/
theorem StructurallyWellFormed.producerLink_unique
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {conclusion : Vertex} {first second : Link}
    (firstMembership : first ∈ certificate.links)
    (firstProduces : first.produces conclusion = true)
    (secondMembership : second ∈ certificate.links)
    (secondProduces : second.produces conclusion = true) :
    first = second := by
  have firstWellFormed :=
    structural.2.2.2.2.1 first firstMembership
  have conclusionBound : conclusion < certificate.formulas.size := by
    cases first with
    | «axiom» left right =>
        simp [Link.produces] at firstProduces
    | tensor left right produced =>
        simp [Link.produces] at firstProduces
        subst produced
        exact firstWellFormed.2.2.2.2.2.1
    | «par» left right produced =>
        simp [Link.produces] at firstProduces
        subst produced
        exact firstWellFormed.2.2.2.2.2.1
  have formulaShape :
      ∃ formula,
        certificate.formula? conclusion = some formula ∧
          formula.isAtom = false := by
    cases first with
    | «axiom» left right =>
        simp [Link.produces] at firstProduces
    | tensor left right produced =>
        simp [Link.produces] at firstProduces
        subst produced
        rcases firstWellFormed.tensor_conclusionFormula with
          ⟨leftFormula, rightFormula, formula⟩
        exact ⟨.tensor leftFormula rightFormula, formula, rfl⟩
    | «par» left right produced =>
        simp [Link.produces] at firstProduces
        subst produced
        rcases firstWellFormed.par_conclusionFormula with
          ⟨leftFormula, rightFormula, formula⟩
        exact ⟨.par leftFormula rightFormula, formula, rfl⟩
  rcases formulaShape with ⟨formula, formulaLookup, compound⟩
  have node := structural.2.2.2.2.2 conclusion conclusionBound
  have producerCount : certificate.producerCount conclusion = 1 := by
    cases formula <;>
      simp [Certificate.NodeWellFormed, formulaLookup] at compound node
    · contradiction
    · exact node.1
    · exact node.1
  unfold Certificate.producerCount at producerCount
  exact mem_filter_length_one_unique producerCount
    firstMembership firstProduces secondMembership secondProduces

/-- Every component returned through the representative-indexed lookup
inherits the state's stored-component formula invariant. -/
theorem ComponentsFormulaConsistent.componentAt
    {certificate : Certificate} {state : UnificationState}
    (consistent : state.ComponentsFormulaConsistent certificate)
    {token : Nat} {component : UnificationComponent}
    (yielded : state.componentAt? token = some component) :
    component.FormulaConsistent certificate := by
  unfold componentAt? at yielded
  cases lookup : state.components[state.representative token]? with
  | none =>
      simp [lookup] at yielded
  | some assigned =>
      cases assigned with
      | none =>
          simp [lookup] at yielded
      | some stored =>
          simp [lookup] at yielded
          subst stored
          exact consistent lookup

/-- Whether every formula occurrence has received a token. -/
def allMarked (state : UnificationState) : Bool :=
  state.marks.all Option.isSome

/-- Live representatives remaining after all performed unions. -/
def liveComponents (state : UnificationState) :
    List UnificationComponent :=
  state.components.toList.filterMap id

end UnificationState

namespace Certificate

/-- Every in-domain formula occurrence has an exact submitted source slot:
atoms are owned by one axiom endpoint and compounds by one connective
conclusion.  Returning the list index makes the ownership theorem directly
usable by the concrete scheduler. -/
private theorem structurallyWellFormed_sourceLink_exists
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {vertex : Vertex}
    (vertexBound : vertex < certificate.formulas.size) :
    ∃ (formula : Formula) (link : Link) (index : Nat),
      certificate.formula? vertex = some formula ∧
        certificate.links[index]? = some link ∧
          match formula with
          | .atom _ _ =>
              link.containsAxiomEndpoint vertex = true
          | .tensor _ _ | .par _ _ =>
              link.produces vertex = true := by
  have formulaExists :
      ∃ formula, certificate.formula? vertex = some formula := by
    exact
      ⟨certificate.formulas[vertex],
        Array.getElem?_eq_getElem vertexBound⟩
  rcases formulaExists with ⟨formula, formulaLookup⟩
  have node := structural.2.2.2.2.2 vertex vertexBound
  cases formula with
  | atom name positive =>
      have count : certificate.axiomCount vertex = 1 := by
        simpa [Certificate.NodeWellFormed, formulaLookup] using node.1
      unfold Certificate.axiomCount at count
      rcases List.length_eq_one_iff.mp count with
        ⟨link, filterEquation⟩
      have filtered :
          link ∈ certificate.links.filter
            (·.containsAxiomEndpoint vertex) := by
        rw [filterEquation]
        simp
      have parts := List.mem_filter.mp filtered
      rcases List.mem_iff_getElem?.mp parts.1 with
        ⟨index, linkLookup⟩
      exact
        ⟨.atom name positive, link, index,
          formulaLookup, linkLookup, parts.2⟩
  | tensor left right =>
      have count : certificate.producerCount vertex = 1 := by
        simpa [Certificate.NodeWellFormed, formulaLookup] using node.1
      unfold Certificate.producerCount at count
      rcases List.length_eq_one_iff.mp count with
        ⟨link, filterEquation⟩
      have filtered :
          link ∈ certificate.links.filter (·.produces vertex) := by
        rw [filterEquation]
        simp
      have parts := List.mem_filter.mp filtered
      rcases List.mem_iff_getElem?.mp parts.1 with
        ⟨index, linkLookup⟩
      exact
        ⟨.tensor left right, link, index,
          formulaLookup, linkLookup, parts.2⟩
  | par left right =>
      have count : certificate.producerCount vertex = 1 := by
        simpa [Certificate.NodeWellFormed, formulaLookup] using node.1
      unfold Certificate.producerCount at count
      rcases List.length_eq_one_iff.mp count with
        ⟨link, filterEquation⟩
      have filtered :
          link ∈ certificate.links.filter (·.produces vertex) := by
        rw [filterEquation]
        simp
      have parts := List.mem_filter.mp filtered
      rcases List.mem_iff_getElem?.mp parts.1 with
        ⟨index, linkLookup⟩
      exact
        ⟨.par left right, link, index,
          formulaLookup, linkLookup, parts.2⟩

private def initialUnificationState (certificate : Certificate) :
    UnificationState where
  marks := Array.replicate certificate.formulas.size none
  parents := #[]
  components := #[]
  startedAxioms := 0
  firedConnectives := 0

private theorem initialUnificationState_abstractable
    (certificate : Certificate) :
    certificate.initialUnificationState.Abstractable certificate := by
  refine {
    markArraySize := by
      simp [initialUnificationState]
    markedVertexBound := ?_
    markedTokenBound := ?_
    representativeBound := ?_
    representativeIdempotent := ?_
  }
  · intro vertex token marked
    simp [initialUnificationState, UnificationState.assignedToken?,
      Array.getElem?_replicate] at marked
    split at marked <;> simp at marked
  · intro vertex token marked
    simp [initialUnificationState, UnificationState.assignedToken?,
      Array.getElem?_replicate] at marked
    split at marked <;> simp at marked
  · intro token bound
    simp [initialUnificationState] at bound
  · intro token bound
    simp [initialUnificationState] at bound

/-- The empty executable marking has no marked occurrence, so its semantic
thread-connectivity contract holds vacuously. -/
private theorem initialUnificationState_threadConnected
    (certificate : Certificate) :
    (certificate.initialUnificationState.toMarking certificate
      (initialUnificationState_abstractable certificate)).ThreadConnected := by
  intro firstVertex secondVertex firstToken secondToken
    firstMarked _secondMarked _synchronized
  simp [initialUnificationState, UnificationState.toMarking,
    UnificationState.assignedToken?, Array.getElem?_replicate] at firstMarked
  split at firstMarked <;> simp at firstMarked

/-- The empty executable marking is causally closed and has no active
reference edge, so its exact threading contract holds vacuously. -/
private theorem initialUnificationState_causallyThreaded
    (certificate : Certificate) :
    (certificate.initialUnificationState.toMarking certificate
      (initialUnificationState_abstractable certificate)).CausallyThreaded := by
  constructor
  · intro link _membership
    cases link with
    | «axiom» left right =>
        trivial
    | «par» left right conclusion =>
        intro marked
        simp [initialUnificationState, UnificationState.toMarking,
          UnificationState.assignedToken?, Array.getElem?_replicate] at marked
        split at marked <;> simp at marked
    | tensor left right conclusion =>
        intro marked
        simp [initialUnificationState, UnificationState.toMarking,
          UnificationState.assignedToken?, Array.getElem?_replicate] at marked
        split at marked <;> simp at marked
  · intro link _membership
    cases link with
    | «axiom» left right =>
        intro leftToken rightToken leftMarked
        simp [initialUnificationState, UnificationState.toMarking,
          UnificationState.assignedToken?, Array.getElem?_replicate]
            at leftMarked
        split at leftMarked <;> simp at leftMarked
    | «par» left right conclusion =>
        intro leftToken conclusionToken leftMarked
        simp [initialUnificationState, UnificationState.toMarking,
          UnificationState.assignedToken?, Array.getElem?_replicate]
            at leftMarked
        split at leftMarked <;> simp at leftMarked
    | tensor left right conclusion =>
        constructor
        · intro leftToken conclusionToken leftMarked
          simp [initialUnificationState, UnificationState.toMarking,
            UnificationState.assignedToken?, Array.getElem?_replicate]
              at leftMarked
          split at leftMarked <;> simp at leftMarked
        · intro rightToken conclusionToken rightMarked
          simp [initialUnificationState, UnificationState.toMarking,
            UnificationState.assignedToken?, Array.getElem?_replicate]
              at rightMarked
          split at rightMarked <;> simp at rightMarked

/-- The executable initial state starts with an empty ordered parent forest. -/
private theorem initialUnificationState_orderedParents
    (certificate : Certificate) :
    certificate.initialUnificationState.OrderedParents := by
  intro token parent lookup
  simp [initialUnificationState] at lookup

/-- The empty initial parent array vacuously consists only of roots. -/
private theorem initialUnificationState_identityParents
    (certificate : Certificate) :
    certificate.initialUnificationState.IdentityParents := by
  intro token bound
  simp [initialUnificationState] at bound

/-- The empty initial state has no inconsistent stored component. -/
private theorem initialUnificationState_componentsFormulaConsistent
    (certificate : Certificate) :
    certificate.initialUnificationState.ComponentsFormulaConsistent
      certificate := by
  intro index component lookup
  simp [initialUnificationState] at lookup

/-- Initial component and parent carriers are both empty. -/
private theorem initialUnificationState_componentsParentsAligned
    (certificate : Certificate) :
    certificate.initialUnificationState.components.size =
      certificate.initialUnificationState.parents.size := by
  rfl

/-- Before axiom initialization no premise is marked, so pending-premise
coverage holds vacuously. -/
private theorem initialUnificationState_pendingPremisesCovered
    (certificate : Certificate) :
    certificate.initialUnificationState.PendingPremisesCovered
      certificate := by
  unfold UnificationState.PendingPremisesCovered
  intro link _membership
  cases link with
  | «axiom» left right =>
      trivial
  | «par» left right conclusion =>
      intro _ready premise token _premiseMembership marked
      unfold UnificationState.tokenAt? at marked
      by_cases bound : premise < certificate.formulas.size <;>
        simp [initialUnificationState, bound] at marked
  | tensor left right conclusion =>
      intro _ready premise token _premiseMembership marked
      unfold UnificationState.tokenAt? at marked
      by_cases bound : premise < certificate.formulas.size <;>
        simp [initialUnificationState, bound] at marked

private def unificationError (certificate : Certificate)
    (code : UnificationErrorCode) (message : String) :
    UnificationError :=
  { code
    message
    formulaCount := certificate.formulas.size
    linkCount := certificate.links.length }

/-- Remove the first occurrence of `vertex`, returning its original focus
index and the remaining frontier. -/
private def pickVertex? : List Vertex → Vertex →
    Option (Nat × List Vertex)
  | [], _ => none
  | head :: tail, vertex =>
      if head == vertex then
        some (0, tail)
      else do
        let (index, remaining) ← pickVertex? tail vertex
        pure (index + 1, head :: remaining)

/-- The occurrence picker succeeds exactly by deleting the selected first
occurrence from the frontier.  Recording the remainder explicitly lets the
scheduler layer prove that a distinct second premise is still available. -/
private theorem pickVertex?_remaining_eq_erase
    {source remaining : List Vertex} {vertex index : Nat}
    (picked :
      pickVertex? source vertex = some (index, remaining)) :
    remaining = source.erase vertex := by
  induction source generalizing index remaining with
  | nil =>
      simp [pickVertex?] at picked
  | cons head tail induction =>
      by_cases same : head = vertex
      · subst head
        simp [pickVertex?] at picked
        simpa using picked.2.symm
      · cases tailPicked : pickVertex? tail vertex with
        | none =>
            simp [pickVertex?, same, tailPicked] at picked
        | some result =>
            rcases result with ⟨tailIndex, tailRemaining⟩
            simp [pickVertex?, same, tailPicked] at picked
            rcases picked with ⟨indexEquation, remainingEquation⟩
            subst index
            subst remaining
            rw [induction tailPicked]
            simp [same]

/-- Selecting one occurrence preserves membership of every differently named
occurrence.  Formula occurrences are globally unique vertices in a
well-formed certificate, so value-level erasure is the required operation. -/
private theorem pickVertex?_mem_remaining_of_ne
    {source remaining : List Vertex} {selected candidate index : Nat}
    (picked :
      pickVertex? source selected = some (index, remaining))
    (different : candidate ≠ selected)
    (membership : candidate ∈ source) :
    candidate ∈ remaining := by
  rw [pickVertex?_remaining_eq_erase picked]
  exact (List.mem_erase_of_ne different).2 membership

/-- Every listed occurrence can be selected by the executable frontier
picker. -/
private theorem pickVertex?_exists_of_mem
    {source : List Vertex} {vertex : Nat}
    (membership : vertex ∈ source) :
    ∃ index remaining,
      pickVertex? source vertex = some (index, remaining) := by
  induction source with
  | nil =>
      simp at membership
  | cons head tail induction =>
      by_cases same : head = vertex
      · subst head
        exact ⟨0, tail, by simp [pickVertex?]⟩
      · have inTail : vertex ∈ tail := by
          have reverseDifferent : vertex ≠ head := Ne.symm same
          simpa [reverseDifferent] using membership
        rcases induction inTail with
          ⟨index, remaining, picked⟩
        exact ⟨index + 1, head :: remaining, by
          simp [pickVertex?, same, picked]⟩

/-- Two distinct listed occurrences can be selected in sequence. -/
private theorem pickVertex?_two_of_mem
    {source : List Vertex} {left right : Nat}
    (different : left ≠ right)
    (leftMembership : left ∈ source)
    (rightMembership : right ∈ source) :
    ∃ leftIndex afterLeft rightIndex context,
      pickVertex? source left = some (leftIndex, afterLeft) ∧
        pickVertex? afterLeft right =
          some (rightIndex, context) := by
  rcases pickVertex?_exists_of_mem leftMembership with
    ⟨leftIndex, afterLeft, leftPicked⟩
  have afterEquation :
      afterLeft = source.erase left :=
    pickVertex?_remaining_eq_erase leftPicked
  have rightAfter : right ∈ afterLeft := by
    rw [afterEquation]
    exact (List.mem_erase_of_ne different.symm).2 rightMembership
  rcases pickVertex?_exists_of_mem rightAfter with
    ⟨rightIndex, context, rightPicked⟩
  exact ⟨leftIndex, afterLeft, rightIndex, context,
    leftPicked, rightPicked⟩

/-- Mapping formula labels commutes with the occurrence-oriented frontier
picker, and the returned focus index selects the mapped formula at exactly the
same position. -/
private theorem pickVertex?_mapM
    (mapping : Vertex → Option Formula)
    {source remaining : List Vertex} {vertex index : Nat}
    {sequent : List Formula} {formula : Formula}
    (picked :
      pickVertex? source vertex = some (index, remaining))
    (mapped : source.mapM mapping = some sequent)
    (formulaAt : mapping vertex = some formula) :
    ∃ remainingSequent,
      CutFreeDerivation.pick? sequent index =
        some (formula, remainingSequent) ∧
      remaining.mapM mapping = some remainingSequent := by
  induction source generalizing index remaining sequent with
  | nil =>
      simp [pickVertex?] at picked
  | cons head tail induction =>
      simp only [pickVertex?] at picked
      by_cases same : head = vertex
      · subst head
        simp at picked
        obtain ⟨rfl, rfl⟩ := picked
        cases tailMapped : tail.mapM mapping with
        | none =>
            simp [formulaAt, tailMapped] at mapped
        | some tailSequent =>
            simp [formulaAt, tailMapped] at mapped
            subst sequent
            exact ⟨tailSequent, rfl, rfl⟩
      · have beqFalse : (head == vertex) = false := by
          simpa using same
        rw [beqFalse] at picked
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind]
          at picked
        cases tailPick : pickVertex? tail vertex with
        | none =>
            simp [tailPick] at picked
        | some result =>
            rcases result with ⟨tailIndex, tailRemaining⟩
            simp [tailPick] at picked
            obtain ⟨rfl, rfl⟩ := picked
            cases headMapped : mapping head with
            | none =>
                simp [headMapped] at mapped
            | some headFormula =>
                simp [headMapped] at mapped
                cases tailMapped : tail.mapM mapping with
                | none =>
                    simp [tailMapped] at mapped
                | some tailSequent =>
                    simp [tailMapped] at mapped
                    subst sequent
                    rcases induction tailPick tailMapped with
                      ⟨remainingSequent, selected, restMapped⟩
                    exact ⟨headFormula :: remainingSequent, by
                      simp [CutFreeDerivation.pick?, selected],
                      by simp [headMapped, restMapped]⟩

namespace UnificationComponent

/-- The component created for a well-typed axiom infers exactly its two
frontier occurrence labels. -/
private theorem axiom_formulaConsistent
    {certificate : Certificate} {left right : Vertex}
    {name : String} {positive : Bool}
    (leftFormula :
      certificate.formula? left = some (.atom name positive))
    (rightFormula :
      certificate.formula? right =
        some (Formula.atom name positive).dual) :
    ({ tree := .axiom name positive
       frontier := [left, right] } :
      UnificationComponent).FormulaConsistent certificate := by
  refine ⟨[.atom name positive,
    (Formula.atom name positive).dual], rfl, ?_⟩
  simp [leftFormula, rightFormula]

/-- Applying one well-typed par rule to a consistent component preserves exact
agreement between the derivation sequent and occurrence frontier. -/
private theorem FormulaConsistent.par
    {certificate : Certificate}
    {component : UnificationComponent}
    (consistent : component.FormulaConsistent certificate)
    {left right conclusion leftFocus rightFocus : Nat}
    {afterLeft context : List Vertex}
    {leftFormula rightFormula : Formula}
    (leftPick :
      pickVertex? component.frontier left =
        some (leftFocus, afterLeft))
    (rightPick :
      pickVertex? afterLeft right =
        some (rightFocus, context))
    (leftFormulaAt :
      certificate.formula? left = some leftFormula)
    (rightFormulaAt :
      certificate.formula? right = some rightFormula)
    (conclusionFormula :
      certificate.formula? conclusion =
        some (.par leftFormula rightFormula)) :
    ({ tree := .par leftFocus rightFocus component.tree
       frontier := context ++ [conclusion] } :
      UnificationComponent).FormulaConsistent certificate := by
  rcases consistent with ⟨sequent, inferred, mapped⟩
  rcases pickVertex?_mapM certificate.formula? leftPick mapped
      leftFormulaAt with
    ⟨afterLeftSequent, leftSelected, afterLeftMapped⟩
  rcases pickVertex?_mapM certificate.formula? rightPick
      afterLeftMapped rightFormulaAt with
    ⟨contextSequent, rightSelected, contextMapped⟩
  refine ⟨contextSequent ++ [.par leftFormula rightFormula], ?_, ?_⟩
  · simp [CutFreeDerivation.infer?, inferred,
      leftSelected, rightSelected]
  · simp [contextMapped, conclusionFormula]

/-- Applying one well-typed tensor rule to two consistent components preserves
exact agreement between the combined derivation sequent and frontier. -/
private theorem FormulaConsistent.tensor
    {certificate : Certificate}
    {leftComponent rightComponent : UnificationComponent}
    (leftConsistent :
      leftComponent.FormulaConsistent certificate)
    (rightConsistent :
      rightComponent.FormulaConsistent certificate)
    {left right conclusion leftFocus rightFocus : Nat}
    {leftContext rightContext : List Vertex}
    {leftFormula rightFormula : Formula}
    (leftPick :
      pickVertex? leftComponent.frontier left =
        some (leftFocus, leftContext))
    (rightPick :
      pickVertex? rightComponent.frontier right =
        some (rightFocus, rightContext))
    (leftFormulaAt :
      certificate.formula? left = some leftFormula)
    (rightFormulaAt :
      certificate.formula? right = some rightFormula)
    (conclusionFormula :
      certificate.formula? conclusion =
        some (.tensor leftFormula rightFormula)) :
    ({ tree :=
         .tensor leftFocus rightFocus
           leftComponent.tree rightComponent.tree
       frontier := conclusion :: (leftContext ++ rightContext) } :
      UnificationComponent).FormulaConsistent certificate := by
  rcases leftConsistent with
    ⟨leftSequent, leftInferred, leftMapped⟩
  rcases rightConsistent with
    ⟨rightSequent, rightInferred, rightMapped⟩
  rcases pickVertex?_mapM certificate.formula? leftPick leftMapped
      leftFormulaAt with
    ⟨leftContextSequent, leftSelected, leftContextMapped⟩
  rcases pickVertex?_mapM certificate.formula? rightPick rightMapped
      rightFormulaAt with
    ⟨rightContextSequent, rightSelected, rightContextMapped⟩
  refine ⟨.tensor leftFormula rightFormula ::
    (leftContextSequent ++ rightContextSequent), ?_, ?_⟩
  · simp [CutFreeDerivation.infer?, leftInferred, rightInferred,
      leftSelected, rightSelected]
  · simp [conclusionFormula, leftContextMapped, rightContextMapped]

end UnificationComponent

/-- Compute the exchange order that reads `target` from `source`. -/
private def occurrenceOrder? (source : List Vertex) :
    List Vertex → Option (List Nat)
  | [] => some []
  | vertex :: rest => do
      let index ← source.findIdx? (· == vertex)
      let tail ← occurrenceOrder? source rest
      pure (index :: tail)

/-- Fire one axiom/start rule. Malformed overlaps fail closed even though the
public driver also requires structural well-formedness. -/
private def startAxiom? (certificate : Certificate)
    (state : UnificationState) (left right : Vertex) :
    Option UnificationState := do
  guard (state.marks[left]? = some none)
  guard (state.marks[right]? = some none)
  let leftFormula ← certificate.formula? left
  let (name, positive) ←
    match leftFormula with
    | .atom name positive => some (name, positive)
    | _ => none
  let component : UnificationComponent :=
    { tree := .axiom name positive
      frontier := [left, right] }
  let marked := state.startMarking left right
  pure {
    marked with
    components := state.components.push (some component)
  }

/-- A successful axiom component construction exposes both executable guards
and changes the observable state exactly by the token-semantic start update. -/
private theorem startAxiom?_success
    {certificate : Certificate} {state next : UnificationState}
    {left right : Vertex}
    (equation :
      certificate.startAxiom? state left right = some next) :
    state.marks[left]? = some none ∧
      state.marks[right]? = some none ∧
      UnificationState.ObservationEquivalent
        (state.startMarking left right) next := by
  unfold startAxiom? at equation
  by_cases leftReady : state.marks[left]? = some none
  · simp [guard, leftReady] at equation
    by_cases rightReady : state.marks[right]? = some none
    · simp [rightReady] at equation
      cases formulaLookup : certificate.formula? left with
      | none =>
          simp [formulaLookup] at equation
      | some formula =>
          cases formula with
          | atom name positive =>
              simp [formulaLookup] at equation
              subst next
              exact ⟨leftReady, rightReady, rfl, rfl⟩
          | tensor first second =>
              simp [formulaLookup] at equation
          | par first second =>
              simp [formulaLookup] at equation
    · have failed : (failure : Option Unit) = none := rfl
      simp [rightReady, failed] at equation
  · have failed : (failure : Option Unit) = none := rfl
    simp [guard, leftReady, failed] at equation

/-- A successful axiom start appends exactly one component whose frontier
contains both axiom endpoints. -/
private theorem startAxiom?_success_component_push
    {certificate : Certificate} {state next : UnificationState}
    {left right : Vertex}
    (equation :
      certificate.startAxiom? state left right = some next) :
    ∃ component,
      next.components = state.components.push (some component) ∧
        left ∈ component.frontier ∧ right ∈ component.frontier := by
  unfold startAxiom? at equation
  by_cases leftReady : state.marks[left]? = some none
  · simp [guard, leftReady] at equation
    by_cases rightReady : state.marks[right]? = some none
    · simp [rightReady] at equation
      cases formulaLookup : certificate.formula? left with
      | none =>
          simp [formulaLookup] at equation
      | some formula =>
          cases formula with
          | atom name positive =>
              simp [formulaLookup] at equation
              subst next
              refine
                ⟨{ tree := .axiom name positive
                   frontier := [left, right] }, rfl, ?_, ?_⟩
              · simp
              · simp
          | tensor first second =>
              simp [formulaLookup] at equation
          | par first second =>
              simp [formulaLookup] at equation
    · have failed : (failure : Option Unit) = none := rfl
      simp [rightReady, failed] at equation
  · have failed : (failure : Option Unit) = none := rfl
    simp [guard, leftReady, failed] at equation

/-- Starting an axiom changes no raw mark outside its two endpoints. -/
private theorem startAxiom?_success_mark_of_ne
    {certificate : Certificate} {state next : UnificationState}
    {left right vertex : Vertex}
    (notLeft : vertex ≠ left) (notRight : vertex ≠ right)
    (equation :
      certificate.startAxiom? state left right = some next) :
    next.marks[vertex]? = state.marks[vertex]? := by
  rcases certificate.startAxiom?_success equation with
    ⟨_leftReady, _rightReady, observation⟩
  rw [← observation.marks]
  simp [UnificationState.startMarking,
    notLeft.symm, notRight.symm]

/-- A successful concrete axiom start assigns both endpoint occurrences. -/
private theorem startAxiom?_success_endpoints_assigned
    {certificate : Certificate} {state next : UnificationState}
    {left right : Vertex}
    (equation :
      certificate.startAxiom? state left right = some next) :
    next.assignedToken? left ≠ none ∧
      next.assignedToken? right ≠ none := by
  rcases certificate.startAxiom?_success equation with
    ⟨leftReady, rightReady, observation⟩
  have leftBound : left < state.marks.size :=
    (Array.getElem?_eq_some_iff.mp leftReady).1
  have rightBound : right < state.marks.size :=
    (Array.getElem?_eq_some_iff.mp rightReady).1
  constructor
  · unfold UnificationState.assignedToken?
    rw [← observation.marks]
    by_cases same : left = right
    · subst right
      simp [UnificationState.startMarking, leftBound]
    · simp [UnificationState.startMarking, leftBound,
        Ne.symm same]
  · unfold UnificationState.assignedToken?
    rw [← observation.marks]
    simp [UnificationState.startMarking, rightBound]

/-- A successful axiom start never removes an existing raw assignment. -/
private theorem startAxiom?_success_preserves_assigned
    {certificate : Certificate} {state next : UnificationState}
    {left right vertex : Vertex}
    (marked : state.assignedToken? vertex ≠ none)
    (equation :
      certificate.startAxiom? state left right = some next) :
    next.assignedToken? vertex ≠ none := by
  by_cases isLeft : vertex = left
  · subst vertex
    exact (certificate.startAxiom?_success_endpoints_assigned equation).1
  · by_cases isRight : vertex = right
    · subst vertex
      exact
        (certificate.startAxiom?_success_endpoints_assigned equation).2
    · cases oldLookup : state.assignedToken? vertex with
      | none =>
          exact False.elim (marked oldLookup)
      | some token =>
          have oldRaw :
              state.marks[vertex]? = some (some token) :=
            UnificationState.assignedToken?_some_raw oldLookup
          have nextRaw :
              next.marks[vertex]? = some (some token) := by
            rw [certificate.startAxiom?_success_mark_of_ne
              isLeft isRight equation]
            exact oldRaw
          unfold UnificationState.assignedToken?
          rw [nextRaw]
          simp

/-- During eager initialization, identity representatives make every
non-endpoint current token stable across one successful axiom start. -/
private theorem startAxiom?_success_tokenAt?_of_ne
    {certificate : Certificate} {state next : UnificationState}
    (identity : state.IdentityParents)
    {left right vertex : Vertex}
    (notLeft : vertex ≠ left) (notRight : vertex ≠ right)
    (equation :
      certificate.startAxiom? state left right = some next) :
    next.tokenAt? vertex = state.tokenAt? vertex := by
  rcases certificate.startAxiom?_success equation with
    ⟨_leftReady, _rightReady, observation⟩
  have markedIdentity :
      (state.startMarking left right).IdentityParents :=
    identity.startMarking left right
  have nextIdentity : next.IdentityParents :=
    observation.identityParents markedIdentity
  unfold UnificationState.tokenAt?
  rw [← observation.marks]
  simp [UnificationState.startMarking,
    notLeft.symm, notRight.symm,
    identity.representative_eq_all,
    nextIdentity.representative_eq_all]

/-- Every successful axiom start exposes both new endpoints in the appended
live component at the fresh identity token. -/
private theorem startAxiom?_success_frontier
    {certificate : Certificate} {state next : UnificationState}
    (identity : state.IdentityParents)
    (aligned : state.components.size = state.parents.size)
    {left right : Vertex}
    (different : left ≠ right)
    (equation :
      certificate.startAxiom? state left right = some next) :
    ∃ token component,
      next.tokenAt? left = some token ∧
        next.tokenAt? right = some token ∧
          next.componentAt? token = some component ∧
            left ∈ component.frontier ∧
              right ∈ component.frontier := by
  rcases certificate.startAxiom?_success equation with
    ⟨leftReady, rightReady, observation⟩
  rcases certificate.startAxiom?_success_component_push equation with
    ⟨component, componentPush, leftMembership, rightMembership⟩
  have markedIdentity :
      (state.startMarking left right).IdentityParents :=
    identity.startMarking left right
  have nextIdentity : next.IdentityParents :=
    observation.identityParents markedIdentity
  have leftBound : left < state.marks.size :=
    (Array.getElem?_eq_some_iff.mp leftReady).1
  have rightBound : right < state.marks.size :=
    (Array.getElem?_eq_some_iff.mp rightReady).1
  let fresh := state.parents.size
  have leftToken : next.tokenAt? left = some fresh := by
    unfold UnificationState.tokenAt?
    rw [← observation.marks]
    simp [UnificationState.startMarking, fresh,
      leftBound, Ne.symm different,
      nextIdentity.representative_eq_all]
  have rightToken : next.tokenAt? right = some fresh := by
    unfold UnificationState.tokenAt?
    rw [← observation.marks]
    simp [UnificationState.startMarking, fresh,
      rightBound,
      nextIdentity.representative_eq_all]
  have freshComponent :
      next.componentAt? fresh = some component := by
    unfold UnificationState.componentAt?
    rw [nextIdentity.representative_eq_all, componentPush]
    rw [show fresh = state.components.size by
      simpa [fresh] using aligned.symm]
    simp
  exact
    ⟨fresh, component, leftToken, rightToken, freshComponent,
      leftMembership, rightMembership⟩

/-- A successful axiom start preserves every old non-endpoint frontier
occurrence and its identity token. -/
private theorem startAxiom?_success_frontier_of_ne
    {certificate : Certificate} {state next : UnificationState}
    (identity : state.IdentityParents)
    {left right vertex token : Vertex}
    {component : UnificationComponent}
    (vertexToken : state.tokenAt? vertex = some token)
    (componentLookup : state.componentAt? token = some component)
    (vertexMembership : vertex ∈ component.frontier)
    (notLeft : vertex ≠ left) (notRight : vertex ≠ right)
    (equation :
      certificate.startAxiom? state left right = some next) :
    next.tokenAt? vertex = some token ∧
      next.componentAt? token = some component ∧
        vertex ∈ component.frontier := by
  rcases certificate.startAxiom?_success equation with
    ⟨_leftReady, _rightReady, observation⟩
  rcases certificate.startAxiom?_success_component_push equation with
    ⟨newComponent, componentPush, _leftMembership, _rightMembership⟩
  have markedIdentity :
      (state.startMarking left right).IdentityParents :=
    identity.startMarking left right
  have nextIdentity : next.IdentityParents :=
    observation.identityParents markedIdentity
  have nextVertexToken :
      next.tokenAt? vertex = some token := by
    rw [certificate.startAxiom?_success_tokenAt?_of_ne
      identity notLeft notRight equation]
    exact vertexToken
  have componentRaw :
      state.components[token]? = some (some component) := by
    have rawAtRepresentative :=
      UnificationState.componentAt?_some_raw componentLookup
    simpa [identity.representative_eq_all] using rawAtRepresentative
  have componentBound : token < state.components.size :=
    (Array.getElem?_eq_some_iff.mp componentRaw).1
  have nextComponentLookup :
      next.componentAt? token = some component := by
    unfold UnificationState.componentAt?
    rw [nextIdentity.representative_eq_all, componentPush]
    rw [Array.getElem?_push,
      if_neg (Nat.ne_of_lt componentBound), componentRaw]
    rfl
  exact
    ⟨nextVertexToken, nextComponentLookup, vertexMembership⟩

/-- One successful eager axiom start preserves pending-premise coverage and
adds exact coverage for any connective premise equal to either newly marked
axiom endpoint. -/
private theorem startAxiom?_success_pendingPremisesCovered
    {certificate : Certificate} {state next : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (identity : state.IdentityParents)
    (aligned : state.components.size = state.parents.size)
    (covered : state.PendingPremisesCovered certificate)
    {left right : Vertex}
    (axiomMembership :
      Link.axiom left right ∈ certificate.links)
    (equation :
      certificate.startAxiom? state left right = some next) :
    next.PendingPremisesCovered certificate := by
  have axiomWellFormed :
      certificate.LinkWellFormed (.axiom left right) :=
    structural.2.2.2.2.1 _ axiomMembership
  have different : left ≠ right := axiomWellFormed.1
  rcases certificate.startAxiom?_success_frontier
      identity aligned different equation with
    ⟨fresh, newComponent, leftToken, rightToken,
      newComponentLookup, leftMembership, rightMembership⟩
  have leftMarked : next.assignedToken? left ≠ none := by
    rcases next.tokenAt?_some_witness leftToken with
      ⟨rawToken, marked, _representative⟩
    intro unmarked
    rw [unmarked] at marked
    contradiction
  have rightMarked : next.assignedToken? right ≠ none := by
    rcases next.tokenAt?_some_witness rightToken with
      ⟨rawToken, marked, _representative⟩
    intro unmarked
    rw [unmarked] at marked
    contradiction
  unfold UnificationState.PendingPremisesCovered
  intro link linkMembership
  cases link with
  | «axiom» candidateLeft candidateRight =>
      trivial
  | «par» candidateLeft candidateRight candidateConclusion =>
      intro nextReady premise token premiseMembership nextPremiseToken
      have candidateNotLeft : candidateConclusion ≠ left := by
        intro same
        subst candidateConclusion
        apply leftMarked
        unfold UnificationState.assignedToken?
        simp [nextReady]
      have candidateNotRight : candidateConclusion ≠ right := by
        intro same
        subst candidateConclusion
        apply rightMarked
        unfold UnificationState.assignedToken?
        simp [nextReady]
      have oldReady :
          state.marks[candidateConclusion]? = some none := by
        have unchanged :=
          certificate.startAxiom?_success_mark_of_ne
            candidateNotLeft candidateNotRight equation
        rw [unchanged] at nextReady
        exact nextReady
      by_cases atLeft : premise = left
      · subst premise
        rw [leftToken] at nextPremiseToken
        injection nextPremiseToken with tokenEquation
        subst token
        exact
          ⟨newComponent, newComponentLookup, leftMembership⟩
      · by_cases atRight : premise = right
        · subst premise
          rw [rightToken] at nextPremiseToken
          injection nextPremiseToken with tokenEquation
          subst token
          exact
            ⟨newComponent, newComponentLookup, rightMembership⟩
        · have oldPremiseToken :
              state.tokenAt? premise = some token := by
            have unchanged :=
              certificate.startAxiom?_success_tokenAt?_of_ne
                identity atLeft atRight equation
            rw [unchanged] at nextPremiseToken
            exact nextPremiseToken
          rcases covered linkMembership oldReady premiseMembership
              oldPremiseToken with
            ⟨component, componentLookup, frontierMembership⟩
          rcases certificate.startAxiom?_success_frontier_of_ne
              identity oldPremiseToken componentLookup
                frontierMembership atLeft atRight equation with
            ⟨_nextMarked, nextComponentLookup,
              nextFrontierMembership⟩
          exact
            ⟨component, nextComponentLookup,
              nextFrontierMembership⟩
  | tensor candidateLeft candidateRight candidateConclusion =>
      intro nextReady premise token premiseMembership nextPremiseToken
      have candidateNotLeft : candidateConclusion ≠ left := by
        intro same
        subst candidateConclusion
        apply leftMarked
        unfold UnificationState.assignedToken?
        simp [nextReady]
      have candidateNotRight : candidateConclusion ≠ right := by
        intro same
        subst candidateConclusion
        apply rightMarked
        unfold UnificationState.assignedToken?
        simp [nextReady]
      have oldReady :
          state.marks[candidateConclusion]? = some none := by
        have unchanged :=
          certificate.startAxiom?_success_mark_of_ne
            candidateNotLeft candidateNotRight equation
        rw [unchanged] at nextReady
        exact nextReady
      by_cases atLeft : premise = left
      · subst premise
        rw [leftToken] at nextPremiseToken
        injection nextPremiseToken with tokenEquation
        subst token
        exact
          ⟨newComponent, newComponentLookup, leftMembership⟩
      · by_cases atRight : premise = right
        · subst premise
          rw [rightToken] at nextPremiseToken
          injection nextPremiseToken with tokenEquation
          subst token
          exact
            ⟨newComponent, newComponentLookup, rightMembership⟩
        · have oldPremiseToken :
              state.tokenAt? premise = some token := by
            have unchanged :=
              certificate.startAxiom?_success_tokenAt?_of_ne
                identity atLeft atRight equation
            rw [unchanged] at nextPremiseToken
            exact nextPremiseToken
          rcases covered linkMembership oldReady premiseMembership
              oldPremiseToken with
            ⟨component, componentLookup, frontierMembership⟩
          rcases certificate.startAxiom?_success_frontier_of_ne
              identity oldPremiseToken componentLookup
                frontierMembership atLeft atRight equation with
            ⟨_nextMarked, nextComponentLookup,
              nextFrontierMembership⟩
          exact
            ⟨component, nextComponentLookup,
              nextFrontierMembership⟩

/-- A successful axiom start pushes one component and one parent token, so
their carriers remain aligned. -/
private theorem startAxiom?_success_componentsParentsAligned
    {certificate : Certificate} {state next : UnificationState}
    (aligned : state.components.size = state.parents.size)
    {left right : Vertex}
    (equation :
      certificate.startAxiom? state left right = some next) :
    next.components.size = next.parents.size := by
  rcases certificate.startAxiom?_success equation with
    ⟨_leftReady, _rightReady, observation⟩
  rcases certificate.startAxiom?_success_component_push equation with
    ⟨component, componentPush, _leftMembership, _rightMembership⟩
  rw [componentPush, ← observation.parents]
  simp [UnificationState.startMarking, aligned]

/-- A successful well-typed axiom start appends one formula-consistent partial
derivation and preserves all previously stored components. -/
private theorem startAxiom?_success_componentsFormulaConsistent
    {certificate : Certificate} {state next : UnificationState}
    (consistent :
      state.ComponentsFormulaConsistent certificate)
    {left right : Vertex}
    (wellFormed :
      certificate.LinkWellFormed (.axiom left right))
    (equation :
      certificate.startAxiom? state left right = some next) :
    next.ComponentsFormulaConsistent certificate := by
  unfold startAxiom? at equation
  by_cases leftReady : state.marks[left]? = some none
  · simp [guard, leftReady] at equation
    by_cases rightReady : state.marks[right]? = some none
    · simp [rightReady] at equation
      cases formulaLookup : certificate.formula? left with
      | none =>
          simp [formulaLookup] at equation
      | some formula =>
          cases formula with
          | atom name positive =>
              simp [formulaLookup] at equation
              subst next
              have rightFormula :
                  certificate.formula? right =
                    some (Formula.atom name positive).dual := by
                rcases wellFormed with
                  ⟨_different, _leftBound, _rightBound, typing⟩
                rw [formulaLookup] at typing
                cases rightLookup : certificate.formula? right with
                | none =>
                    simp [rightLookup] at typing
                | some rightValue =>
                    simp [rightLookup] at typing
                    subst rightValue
                    rfl
              have componentConsistent :
                  ({ tree := .axiom name positive
                     frontier := [left, right] } :
                    UnificationComponent).FormulaConsistent certificate :=
                UnificationComponent.axiom_formulaConsistent
                  formulaLookup rightFormula
              exact consistent.push componentConsistent
          | tensor first second =>
              simp [formulaLookup] at equation
          | par first second =>
              simp [formulaLookup] at equation
    · have failed : (failure : Option Unit) = none := rfl
      simp [rightReady, failed] at equation
  · have failed : (failure : Option Unit) = none := rfl
    simp [guard, leftReady, failed] at equation

/-- Every successful concrete axiom initialization, including component
construction, refines one independent Figure-5 start step. -/
private theorem startAxiom?_refines_start
    {certificate : Certificate} {state next : UnificationState}
    (abstractable : state.Abstractable certificate)
    (identity : state.IdentityParents)
    {left right : Vertex}
    (linkMembership :
      Link.axiom left right ∈ certificate.links)
    (equation :
      certificate.startAxiom? state left right = some next) :
    ∃ nextAbstractable : next.Abstractable certificate,
      UnificationStep certificate
        (state.toMarking certificate abstractable)
        (next.toMarking certificate nextAbstractable) := by
  rcases certificate.startAxiom?_success equation with
    ⟨leftReady, rightReady, observation⟩
  have leftMarksBound : left < state.marks.size :=
    (Array.getElem?_eq_some_iff.mp leftReady).choose
  have rightMarksBound : right < state.marks.size :=
    (Array.getElem?_eq_some_iff.mp rightReady).choose
  have leftBound : left < certificate.formulas.size := by
    simpa [abstractable.markArraySize] using leftMarksBound
  have rightBound : right < certificate.formulas.size := by
    simpa [abstractable.markArraySize] using rightMarksBound
  have leftUnmarked : state.assignedToken? left = none := by
    simp [UnificationState.assignedToken?, leftReady]
  have rightUnmarked : state.assignedToken? right = none := by
    simp [UnificationState.assignedToken?, rightReady]
  let markedAbstractable :=
    abstractable.startMarking identity leftBound rightBound
  let nextAbstractable :=
    observation.abstractable markedAbstractable
  refine ⟨nextAbstractable, ?_⟩
  rw [observation.toMarking_eq markedAbstractable]
  exact state.startMarking_startStep abstractable identity
    linkMembership leftBound rightBound leftUnmarked rightUnmarked

/-- Every successful concrete axiom initialization preserves the ordered
parent forest. -/
private theorem startAxiom?_success_ordered
    {certificate : Certificate} {state next : UnificationState}
    (ordered : state.OrderedParents)
    {left right : Vertex}
    (equation :
      certificate.startAxiom? state left right = some next) :
    next.OrderedParents := by
  rcases certificate.startAxiom?_success equation with
    ⟨leftReady, rightReady, observation⟩
  have markedOrdered :
      (state.startMarking left right).OrderedParents :=
    UnificationState.OrderedParents.startMarking ordered left right
  have nextOrdered : next.OrderedParents :=
    UnificationState.ObservationEquivalent.orderedParents
      observation markedOrdered
  intro token parent lookup
  exact nextOrdered lookup

/-- Initialize every axiom thread, preserving link-list order only as the
deterministic fresh-token order. -/
private def startAxioms? (certificate : Certificate) :
    List Link → UnificationState → Option UnificationState
  | [], state => some state
  | .axiom left right :: links, state => do
      let next ← certificate.startAxiom? state left right
      certificate.startAxioms? links next
  | _ :: links, state =>
      certificate.startAxioms? links state

/-- Eager initialization is monotone on raw formula assignments. -/
private theorem startAxioms?_success_preserves_assigned
    (certificate : Certificate)
    {links : List Link} {state next : UnificationState}
    {vertex : Vertex}
    (marked : state.assignedToken? vertex ≠ none)
    (equation :
      certificate.startAxioms? links state = some next) :
    next.assignedToken? vertex ≠ none := by
  induction links generalizing state with
  | nil =>
      simp [startAxioms?] at equation
      subst next
      exact marked
  | cons link links induction =>
      cases link with
      | «axiom» left right =>
          simp only [startAxioms?] at equation
          cases startEquation :
              certificate.startAxiom? state left right with
          | none =>
              rw [startEquation] at equation
              contradiction
          | some started =>
              rw [startEquation] at equation
              exact induction
                (certificate.startAxiom?_success_preserves_assigned
                  marked startEquation)
                equation
      | «par» left right conclusion =>
          simp only [startAxioms?] at equation
          exact induction marked equation
      | «tensor» left right conclusion =>
          simp only [startAxioms?] at equation
          exact induction marked equation

/-- Every axiom endpoint occurring in a successfully initialized submitted
list remains assigned after the entire eager initialization. -/
private theorem startAxioms?_success_axiom_endpoints_assigned
    (certificate : Certificate)
    {links : List Link} {state next : UnificationState}
    {left right : Vertex}
    (membership : Link.axiom left right ∈ links)
    (equation :
      certificate.startAxioms? links state = some next) :
    next.assignedToken? left ≠ none ∧
      next.assignedToken? right ≠ none := by
  induction links generalizing state with
  | nil =>
      simp at membership
  | cons link links induction =>
      cases link with
      | «axiom» headLeft headRight =>
          simp only [startAxioms?] at equation
          cases startEquation :
              certificate.startAxiom? state headLeft headRight with
          | none =>
              rw [startEquation] at equation
              contradiction
          | some started =>
              rw [startEquation] at equation
              rcases List.mem_cons.mp membership with
                head | tail
              · injection head with leftEquation rightEquation
                subst left
                subst right
                have endpoints :=
                  certificate.startAxiom?_success_endpoints_assigned
                    startEquation
                exact
                  ⟨certificate.startAxioms?_success_preserves_assigned
                      endpoints.1 equation,
                    certificate.startAxioms?_success_preserves_assigned
                      endpoints.2 equation⟩
              · exact induction tail equation
      | «par» headLeft headRight headConclusion =>
          simp only [startAxioms?] at equation
          apply induction
          · simpa using membership
          · exact equation
      | «tensor» headLeft headRight headConclusion =>
          simp only [startAxioms?] at equation
          apply induction
          · simpa using membership
          · exact equation

/-- Successful eager axiom initialization preserves the ordered parent forest
across the whole submitted link list. -/
private theorem startAxioms?_success_ordered
    (certificate : Certificate)
    {links : List Link} {state next : UnificationState}
    (ordered : state.OrderedParents)
    (equation :
      certificate.startAxioms? links state = some next) :
    next.OrderedParents := by
  induction links generalizing state with
  | nil =>
      simp [startAxioms?] at equation
      subst next
      exact ordered
  | cons link links induction =>
      cases link with
      | «axiom» left right =>
          simp only [startAxioms?] at equation
          cases startEquation :
              certificate.startAxiom? state left right with
          | none =>
              rw [startEquation] at equation
              contradiction
          | some started =>
              rw [startEquation] at equation
              have startedOrdered : started.OrderedParents :=
                certificate.startAxiom?_success_ordered
                  ordered startEquation
              have result : next.OrderedParents :=
                induction startedOrdered equation
              intro token parent lookup
              exact result lookup
      | «par» left right conclusion =>
          simp only [startAxioms?] at equation
          have result : next.OrderedParents :=
            induction ordered equation
          intro token parent lookup
          exact result lookup
      | «tensor» left right conclusion =>
          simp only [startAxioms?] at equation
          have result : next.OrderedParents :=
            induction ordered equation
          intro token parent lookup
          exact result lookup

/-- Eager initialization preserves identity parents and carrier alignment,
while establishing pending-premise frontier coverage as each axiom endpoint
becomes marked. -/
private theorem startAxioms?_success_identityAlignedCovered
    (certificate : Certificate)
    (structural : certificate.StructurallyWellFormed)
    {links : List Link} {state next : UnificationState}
    (identity : state.IdentityParents)
    (aligned : state.components.size = state.parents.size)
    (covered : state.PendingPremisesCovered certificate)
    (submitted :
      ∀ link, link ∈ links → link ∈ certificate.links)
    (equation :
      certificate.startAxioms? links state = some next) :
    next.IdentityParents ∧
      next.components.size = next.parents.size ∧
        next.PendingPremisesCovered certificate := by
  induction links generalizing state with
  | nil =>
      simp [startAxioms?] at equation
      subst next
      exact ⟨identity, aligned, covered⟩
  | cons link links induction =>
      have tailSubmitted :
          ∀ candidate, candidate ∈ links →
            candidate ∈ certificate.links := by
        intro candidate membership
        exact submitted candidate (by simp [membership])
      cases link with
      | «axiom» left right =>
          have axiomMembership :
              Link.axiom left right ∈ certificate.links :=
            submitted _ (by simp)
          simp only [startAxioms?] at equation
          cases startEquation :
              certificate.startAxiom? state left right with
          | none =>
              rw [startEquation] at equation
              contradiction
          | some started =>
              rw [startEquation] at equation
              rcases certificate.startAxiom?_success startEquation with
                ⟨_leftReady, _rightReady, observation⟩
              have markedIdentity :
                  (state.startMarking left right).IdentityParents :=
                identity.startMarking left right
              have startedIdentity : started.IdentityParents :=
                observation.identityParents markedIdentity
              have startedAligned :
                  started.components.size = started.parents.size :=
                certificate
                  |>.startAxiom?_success_componentsParentsAligned
                    aligned startEquation
              have startedCovered :
                  started.PendingPremisesCovered certificate :=
                certificate
                  |>.startAxiom?_success_pendingPremisesCovered
                    structural identity aligned covered
                      axiomMembership startEquation
              exact induction startedIdentity startedAligned
                startedCovered tailSubmitted equation
      | «par» left right conclusion =>
          simp only [startAxioms?] at equation
          exact induction identity aligned covered
            tailSubmitted equation
      | «tensor» left right conclusion =>
          simp only [startAxioms?] at equation
          exact induction identity aligned covered
            tailSubmitted equation

/-- Successful eager axiom initialization preserves formula consistency of
every stored partial derivation. -/
private theorem startAxioms?_success_componentsFormulaConsistent
    (certificate : Certificate)
    (structural : certificate.StructurallyWellFormed)
    {links : List Link} {state next : UnificationState}
    (consistent :
      state.ComponentsFormulaConsistent certificate)
    (submitted :
      ∀ link, link ∈ links → link ∈ certificate.links)
    (equation :
      certificate.startAxioms? links state = some next) :
    next.ComponentsFormulaConsistent certificate := by
  induction links generalizing state with
  | nil =>
      simp [startAxioms?] at equation
      subst next
      exact consistent
  | cons link links induction =>
      have tailSubmitted :
          ∀ candidate, candidate ∈ links →
            candidate ∈ certificate.links := by
        intro candidate membership
        exact submitted candidate (by simp [membership])
      cases link with
      | «axiom» left right =>
          have linkSubmitted :
              Link.axiom left right ∈ certificate.links :=
            submitted _ (by simp)
          have wellFormed :
              certificate.LinkWellFormed (.axiom left right) :=
            structural.2.2.2.2.1 _ linkSubmitted
          simp only [startAxioms?] at equation
          cases startEquation :
              certificate.startAxiom? state left right with
          | none =>
              rw [startEquation] at equation
              contradiction
          | some started =>
              rw [startEquation] at equation
              have startedConsistent :
                  started.ComponentsFormulaConsistent certificate :=
                certificate.startAxiom?_success_componentsFormulaConsistent
                  consistent wellFormed startEquation
              intro index component lookup
              exact induction startedConsistent tailSubmitted equation lookup
      | «par» left right conclusion =>
          simp only [startAxioms?] at equation
          intro index component lookup
          exact induction consistent tailSubmitted equation lookup
      | «tensor» left right conclusion =>
          simp only [startAxioms?] at equation
          intro index component lookup
          exact induction consistent tailSubmitted equation lookup

/-- Successful eager axiom initialization preserves abstraction and identity
parents, and is simulated by a finite sequence of independent start steps. -/
private theorem startAxioms?_success_refines
    (certificate : Certificate)
    {links : List Link} {state next : UnificationState}
    (abstractable : state.Abstractable certificate)
    (identity : state.IdentityParents)
    (submitted :
      ∀ link, link ∈ links → link ∈ certificate.links)
    (equation :
      certificate.startAxioms? links state = some next) :
    ∃ nextAbstractable : next.Abstractable certificate,
      next.IdentityParents ∧
        UnificationExecution certificate
          (state.toMarking certificate abstractable)
          (next.toMarking certificate nextAbstractable) := by
  induction links generalizing state next with
  | nil =>
      simp [startAxioms?] at equation
      subst next
      exact ⟨abstractable, identity, .refl _⟩
  | cons link links induction =>
      have tailSubmitted :
          ∀ candidate, candidate ∈ links →
            candidate ∈ certificate.links := by
        intro candidate membership
        exact submitted candidate (by simp [membership])
      cases link with
      | «axiom» left right =>
          have linkSubmitted :
              Link.axiom left right ∈ certificate.links :=
            submitted _ (by simp)
          simp only [startAxioms?] at equation
          cases startEquation :
              certificate.startAxiom? state left right with
          | none =>
              rw [startEquation] at equation
              contradiction
          | some started =>
              rw [startEquation] at equation
              rcases certificate.startAxiom?_refines_start
                  abstractable identity linkSubmitted startEquation with
                ⟨startedAbstractable, transition⟩
              rcases certificate.startAxiom?_success startEquation with
                ⟨_leftReady, _rightReady, observation⟩
              have markedIdentity :
                  (state.startMarking left right).IdentityParents :=
                identity.startMarking left right
              have startedIdentity : started.IdentityParents :=
                observation.identityParents markedIdentity
              rcases induction startedAbstractable startedIdentity
                  tailSubmitted equation with
                ⟨nextAbstractable, nextIdentity, rest⟩
              exact ⟨nextAbstractable, nextIdentity,
                UnificationExecution.step transition rest⟩
      | «par» left right conclusion =>
          simp only [startAxioms?] at equation
          exact induction abstractable identity tailSubmitted equation
      | «tensor» left right conclusion =>
          simp only [startAxioms?] at equation
          exact induction abstractable identity tailSubmitted equation

/-- Fire a Guerrini unary/`par` rule when both premises yield the same token.
The corresponding derivation component is updated in lockstep. -/
private def firePar? (state : UnificationState)
    (left right conclusion : Vertex) :
    Option UnificationState :=
  match state.forwardToken? left right conclusion with
  | none => none
  | some leftToken =>
      match state.componentAt? leftToken with
      | none => none
      | some component =>
          match pickVertex? component.frontier left with
          | none => none
          | some (leftFocus, afterLeft) =>
              match pickVertex? afterLeft right with
              | none => none
              | some (rightFocus, context) =>
                  let nextComponent : UnificationComponent :=
                    { tree :=
                        .par leftFocus rightFocus component.tree
                      frontier := context ++ [conclusion] }
                  let marked :=
                    state.markConclusion conclusion leftToken
                  some {
                    marked with
                    components :=
                      state.components.setIfInBounds leftToken
                        (some nextComponent)
                  }

/-- Frontier coverage makes a guard-ready par firing operationally total.
This isolates the only extra invariant needed to turn the scheduler's token
classification into an actual parser step: both distinct premise occurrences
must still be present in their shared live component. -/
private theorem firePar?_exists_of_ready
    {certificate : Certificate} {state : UnificationState}
    (covered : state.PendingPremisesCovered certificate)
    {left right conclusion token : Nat}
    (linkMembership :
      Link.par left right conclusion ∈ certificate.links)
    (different : left ≠ right)
    (conclusionReady : state.marks[conclusion]? = some none)
    (leftReady : state.tokenAt? left = some token)
    (rightReady : state.tokenAt? right = some token) :
    ∃ next,
      firePar? state left right conclusion = some next := by
  have forwardReady :
      state.forwardToken? left right conclusion = some token := by
    simp [UnificationState.forwardToken?, conclusionReady,
      leftReady, rightReady]
  have pendingCoverage :
      ∀ {premise token : Nat}, premise ∈ [left, right] →
        state.tokenAt? premise = some token →
          ∃ component,
            state.componentAt? token = some component ∧
              premise ∈ component.frontier :=
    covered linkMembership conclusionReady
  rcases pendingCoverage (premise := left) (token := token)
      (by simp) leftReady with
    ⟨leftComponent, leftComponentLookup, leftMembership⟩
  rcases pendingCoverage (premise := right) (token := token)
      (by simp) rightReady with
    ⟨rightComponent, rightComponentLookup, rightMembership⟩
  have componentEquation : rightComponent = leftComponent := by
    rw [leftComponentLookup] at rightComponentLookup
    injection rightComponentLookup with equality
    exact equality.symm
  subst rightComponent
  rcases pickVertex?_two_of_mem different
      leftMembership rightMembership with
    ⟨leftIndex, afterLeft, rightIndex, context,
      leftPicked, rightPicked⟩
  simp [firePar?, forwardReady, leftComponentLookup,
    leftPicked, rightPicked]

/-- Successful par component construction changes the abstract executable
state exactly by the already verified conclusion-marking update. -/
private theorem firePar?_success_observation
    {state next : UnificationState}
    {left right conclusion : Vertex}
    (equation : firePar? state left right conclusion = some next) :
    ∃ outputToken,
      state.forwardToken? left right conclusion = some outputToken ∧
        UnificationState.ObservationEquivalent
          (state.markConclusion conclusion outputToken) next := by
  unfold firePar? at equation
  split at equation
  · contradiction
  · rename_i _ outputToken forwardEquation
    refine ⟨outputToken, forwardEquation, ?_⟩
    split at equation
    · contradiction
    · split at equation
      · contradiction
      · split at equation
        · contradiction
        · injection equation with stateEquation
          subst next
          exact ⟨rfl, rfl⟩

/-- Every successful in-domain par firing visibly marks its conclusion. -/
private theorem firePar?_success_conclusion_marked
    {certificate : Certificate} {state next : UnificationState}
    (abstractable : state.Abstractable certificate)
    {left right conclusion : Vertex}
    (conclusionBound : conclusion < certificate.formulas.size)
    (equation : firePar? state left right conclusion = some next) :
    next.assignedToken? conclusion ≠ none := by
  rcases firePar?_success_observation equation with
    ⟨outputToken, _forwardEquation, observation⟩
  unfold UnificationState.assignedToken?
  rw [← observation.marks]
  simp [UnificationState.markConclusion, conclusionBound,
    abstractable.markArraySize]

/-- A successful par firing does not change the current token of any
occurrence other than its newly marked conclusion. -/
private theorem firePar?_success_tokenAt?_of_ne
    {state next : UnificationState}
    {left right conclusion vertex : Vertex}
    (different : vertex ≠ conclusion)
    (equation : firePar? state left right conclusion = some next) :
    next.tokenAt? vertex = state.tokenAt? vertex := by
  rcases firePar?_success_observation equation with
    ⟨outputToken, _forwardEquation, observation⟩
  have parentsEquation : next.parents = state.parents := by
    rw [← observation.parents]
    rfl
  have representativeEquation (token : Nat) :
      next.representative token = state.representative token := by
    unfold UnificationState.representative
    rw [parentsEquation]
  unfold UnificationState.tokenAt?
  rw [← observation.marks]
  simp [UnificationState.markConclusion,
    different.symm, representativeEquation]

/-- A successful par firing changes no raw mark except its conclusion slot. -/
private theorem firePar?_success_mark_of_ne
    {state next : UnificationState}
    {left right conclusion vertex : Vertex}
    (different : vertex ≠ conclusion)
    (equation : firePar? state left right conclusion = some next) :
    next.marks[vertex]? = state.marks[vertex]? := by
  rcases firePar?_success_observation equation with
    ⟨outputToken, _forwardEquation, observation⟩
  rw [← observation.marks]
  simp [UnificationState.markConclusion, different.symm]

/-- Par firing is monotone on the domain of marked occurrences: it marks its
conclusion and leaves every other raw mark unchanged. -/
private theorem firePar?_success_preserves_assigned
    {certificate : Certificate} {state next : UnificationState}
    (abstractable : state.Abstractable certificate)
    {left right conclusion vertex : Vertex}
    (conclusionBound : conclusion < certificate.formulas.size)
    (marked : state.assignedToken? vertex ≠ none)
    (equation : firePar? state left right conclusion = some next) :
    next.assignedToken? vertex ≠ none := by
  by_cases same : vertex = conclusion
  · subst vertex
    exact firePar?_success_conclusion_marked
      abstractable conclusionBound equation
  · cases oldLookup : state.assignedToken? vertex with
    | none =>
        exact False.elim (marked oldLookup)
    | some token =>
        have oldRaw :
            state.marks[vertex]? = some (some token) :=
          UnificationState.assignedToken?_some_raw oldLookup
        have nextRaw :
            next.marks[vertex]? = some (some token) := by
          rw [firePar?_success_mark_of_ne same equation]
          exact oldRaw
        unfold UnificationState.assignedToken?
        rw [nextRaw]
        simp

/-- A successful par firing exposes its new conclusion at the same root token
shared by both premises. -/
private theorem firePar?_success_conclusion_tokenAt?
    {certificate : Certificate} {state next : UnificationState}
    (abstractable : state.Abstractable certificate)
    {left right conclusion : Vertex}
    {outputToken : Nat}
    (forwardEquation :
      state.forwardToken? left right conclusion = some outputToken)
    (equation : firePar? state left right conclusion = some next) :
    next.tokenAt? conclusion = some outputToken := by
  rcases firePar?_success_observation equation with
    ⟨observedToken, observedForward, observation⟩
  rw [forwardEquation] at observedForward
  injection observedForward with tokenEquation
  subst observedToken
  have guards := state.forwardToken?_success forwardEquation
  have tokenRoot : state.representative outputToken = outputToken :=
    abstractable.tokenAt?_root guards.2.1
  have conclusionBound : conclusion < state.marks.size :=
    (Array.getElem?_eq_some_iff.mp guards.1).1
  have parentsEquation : next.parents = state.parents := by
    rw [← observation.parents]
    rfl
  have representativeEquation (token : Nat) :
      next.representative token = state.representative token := by
    unfold UnificationState.representative
    rw [parentsEquation]
  unfold UnificationState.tokenAt?
  rw [← observation.marks]
  simp [UnificationState.markConclusion, conclusionBound,
    representativeEquation, tokenRoot]

/-- A successful par firing preserves every differently named frontier
occurrence.  Occurrences in the fired component survive both exact picks;
occurrences in all other components are untouched. -/
private theorem firePar?_success_frontier_of_ne
    {certificate : Certificate} {state next : UnificationState}
    (abstractable : state.Abstractable certificate)
    {left right conclusion vertex token : Vertex}
    {component : UnificationComponent}
    (vertexToken : state.tokenAt? vertex = some token)
    (componentLookup : state.componentAt? token = some component)
    (vertexMembership : vertex ∈ component.frontier)
    (notLeft : vertex ≠ left) (notRight : vertex ≠ right)
    (equation : firePar? state left right conclusion = some next) :
    ∃ nextComponent,
      next.componentAt? token = some nextComponent ∧
        vertex ∈ nextComponent.frontier := by
  rcases firePar?_success_observation equation with
    ⟨outputToken, forwardEquation, _observation⟩
  have guards := state.forwardToken?_success forwardEquation
  have outputRoot : state.representative outputToken = outputToken :=
    abstractable.tokenAt?_root guards.2.1
  have tokenRoot : state.representative token = token :=
    abstractable.tokenAt?_root vertexToken
  unfold firePar? at equation
  rw [forwardEquation] at equation
  cases firedLookup :
      state.componentAt? outputToken with
  | none =>
      simp [firedLookup] at equation
  | some firedComponent =>
      simp only [firedLookup] at equation
      cases leftPick :
          pickVertex? firedComponent.frontier left with
      | none =>
          simp [leftPick] at equation
      | some leftResult =>
          rcases leftResult with ⟨leftIndex, afterLeft⟩
          simp only [leftPick] at equation
          cases rightPick :
              pickVertex? afterLeft right with
          | none =>
              simp [rightPick] at equation
          | some rightResult =>
              rcases rightResult with ⟨rightIndex, context⟩
              simp only [rightPick] at equation
              injection equation with nextEquation
              have nextOutputRoot :
                  next.representative outputToken = outputToken := by
                rw [_observation.representative_eq outputToken]
                simpa [UnificationState.representative,
                  UnificationState.markConclusion] using outputRoot
              have nextTokenRoot :
                  next.representative token = token := by
                rw [_observation.representative_eq token]
                simpa [UnificationState.representative,
                  UnificationState.markConclusion] using tokenRoot
              subst next
              let replacement : UnificationComponent :=
                { tree :=
                    .par leftIndex rightIndex firedComponent.tree
                  frontier := context ++ [conclusion] }
              have firedRaw :
                  state.components[outputToken]? =
                    some (some firedComponent) := by
                have rawAtRepresentative :=
                  UnificationState.componentAt?_some_raw firedLookup
                simpa [outputRoot] using rawAtRepresentative
              have outputBound :
                  outputToken < state.components.size :=
                (Array.getElem?_eq_some_iff.mp firedRaw).1
              by_cases same : token = outputToken
              · subst token
                have componentEquation :
                    component = firedComponent := by
                  rw [firedLookup] at componentLookup
                  injection componentLookup with equality
                  exact equality.symm
                subst component
                have afterLeftMembership : vertex ∈ afterLeft :=
                  pickVertex?_mem_remaining_of_ne
                    leftPick notLeft vertexMembership
                have contextMembership : vertex ∈ context :=
                  pickVertex?_mem_remaining_of_ne
                    rightPick notRight afterLeftMembership
                refine ⟨replacement, ?_, ?_⟩
                · unfold UnificationState.componentAt?
                  rw [nextOutputRoot]
                  simp [replacement, outputBound]
                · simp [replacement, contextMembership]
              · have different : outputToken ≠ token := Ne.symm same
                have componentRaw :
                    state.components[token]? =
                      some (some component) := by
                  have rawAtRepresentative :=
                    UnificationState.componentAt?_some_raw componentLookup
                  simpa [tokenRoot] using rawAtRepresentative
                refine ⟨component, ?_, vertexMembership⟩
                unfold UnificationState.componentAt?
                rw [nextTokenRoot]
                simp [different, componentRaw]

/-- The conclusion created by a successful par firing is exposed on the
frontier of the replacement live component. -/
private theorem firePar?_success_conclusion_frontier
    {certificate : Certificate} {state next : UnificationState}
    (abstractable : state.Abstractable certificate)
    {left right conclusion : Vertex}
    (equation : firePar? state left right conclusion = some next) :
    ∃ outputToken nextComponent,
      next.tokenAt? conclusion = some outputToken ∧
        next.componentAt? outputToken = some nextComponent ∧
          conclusion ∈ nextComponent.frontier := by
  rcases firePar?_success_observation equation with
    ⟨outputToken, forwardEquation, observation⟩
  have guards := state.forwardToken?_success forwardEquation
  have outputRoot : state.representative outputToken = outputToken :=
    abstractable.tokenAt?_root guards.2.1
  have conclusionToken :
      next.tokenAt? conclusion = some outputToken :=
    firePar?_success_conclusion_tokenAt?
      abstractable forwardEquation equation
  unfold firePar? at equation
  rw [forwardEquation] at equation
  cases componentLookup :
      state.componentAt? outputToken with
  | none =>
      simp [componentLookup] at equation
  | some component =>
      simp only [componentLookup] at equation
      cases leftPick : pickVertex? component.frontier left with
      | none =>
          simp [leftPick] at equation
      | some leftResult =>
          rcases leftResult with ⟨leftIndex, afterLeft⟩
          simp only [leftPick] at equation
          cases rightPick : pickVertex? afterLeft right with
          | none =>
              simp [rightPick] at equation
          | some rightResult =>
              rcases rightResult with ⟨rightIndex, context⟩
              simp only [rightPick] at equation
              injection equation with nextEquation
              have nextOutputRoot :
                  next.representative outputToken = outputToken := by
                rw [observation.representative_eq outputToken]
                simpa [UnificationState.representative,
                  UnificationState.markConclusion] using outputRoot
              have componentRaw :
                  state.components[outputToken]? =
                    some (some component) := by
                have rawAtRepresentative :=
                  UnificationState.componentAt?_some_raw
                    componentLookup
                simpa [outputRoot] using rawAtRepresentative
              have outputBound :
                  outputToken < state.components.size :=
                (Array.getElem?_eq_some_iff.mp componentRaw).1
              subst next
              let replacement : UnificationComponent :=
                { tree := .par leftIndex rightIndex component.tree
                  frontier := context ++ [conclusion] }
              refine
                ⟨outputToken, replacement, conclusionToken, ?_, ?_⟩
              · unfold UnificationState.componentAt?
                rw [nextOutputRoot]
                simp [replacement, outputBound]
              · simp [replacement]

/-- Firing one par link preserves exact frontier coverage for every still
pending connective.  The fired conclusion becomes a fresh frontier
occurrence, while structural resource ownership prevents either consumed
premise from belonging to any different pending link. -/
private theorem firePar?_success_pendingPremisesCovered
    {certificate : Certificate} {state next : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (abstractable : state.Abstractable certificate)
    (covered : state.PendingPremisesCovered certificate)
    {left right conclusion : Vertex}
    (firedMembership :
      Link.par left right conclusion ∈ certificate.links)
    (equation : firePar? state left right conclusion = some next) :
    next.PendingPremisesCovered certificate := by
  have firedWellFormed :
      certificate.LinkWellFormed (.par left right conclusion) :=
    structural.2.2.2.2.1 _ firedMembership
  have conclusionBound : conclusion < certificate.formulas.size :=
    firedWellFormed.2.2.2.2.2.1
  have firedMarked : next.assignedToken? conclusion ≠ none :=
    firePar?_success_conclusion_marked
      abstractable conclusionBound equation
  unfold UnificationState.PendingPremisesCovered
  intro link linkMembership
  cases link with
  | «axiom» candidateLeft candidateRight =>
      trivial
  | «par» candidateLeft candidateRight candidateConclusion =>
      intro nextReady premise token premiseMembership nextPremiseToken
      have candidateConclusionDifferent :
          candidateConclusion ≠ conclusion := by
        intro same
        subst candidateConclusion
        apply firedMarked
        unfold UnificationState.assignedToken?
        simp [nextReady]
      have oldReady :
          state.marks[candidateConclusion]? = some none := by
        have unchanged :=
          firePar?_success_mark_of_ne
            candidateConclusionDifferent equation
        rw [unchanged] at nextReady
        exact nextReady
      have candidateNeFired :
          Link.par candidateLeft candidateRight candidateConclusion ≠
            Link.par left right conclusion := by
        intro same
        cases same
        exact candidateConclusionDifferent rfl
      by_cases created : premise = conclusion
      · subst premise
        rcases firePar?_success_conclusion_frontier
            abstractable equation with
          ⟨outputToken, nextComponent, conclusionToken,
            componentLookup, conclusionMembership⟩
        rw [conclusionToken] at nextPremiseToken
        injection nextPremiseToken with tokenEquation
        subst token
        exact
          ⟨nextComponent, componentLookup, conclusionMembership⟩
      · have oldPremiseToken :
            state.tokenAt? premise = some token := by
          have unchanged :=
            firePar?_success_tokenAt?_of_ne created equation
          rw [unchanged] at nextPremiseToken
          exact nextPremiseToken
        rcases covered linkMembership oldReady premiseMembership
            oldPremiseToken with
          ⟨component, componentLookup, frontierMembership⟩
        have candidatePremise :
            premise ∈
              (Link.par candidateLeft candidateRight
                candidateConclusion).premises := by
          simpa [Link.premises] using premiseMembership
        have notLeft : premise ≠ left := by
          intro same
          subst premise
          have sameLink :=
            UnificationState.StructurallyWellFormed.parentLink_unique
              structural linkMembership candidatePremise
                firedMembership (by simp [Link.premises])
          exact candidateNeFired sameLink
        have notRight : premise ≠ right := by
          intro same
          subst premise
          have sameLink :=
            UnificationState.StructurallyWellFormed.parentLink_unique
              structural linkMembership candidatePremise
                firedMembership (by simp [Link.premises])
          exact candidateNeFired sameLink
        exact firePar?_success_frontier_of_ne
          abstractable oldPremiseToken componentLookup
            frontierMembership notLeft notRight equation
  | tensor candidateLeft candidateRight candidateConclusion =>
      intro nextReady premise token premiseMembership nextPremiseToken
      have candidateConclusionDifferent :
          candidateConclusion ≠ conclusion := by
        intro same
        subst candidateConclusion
        apply firedMarked
        unfold UnificationState.assignedToken?
        simp [nextReady]
      have oldReady :
          state.marks[candidateConclusion]? = some none := by
        have unchanged :=
          firePar?_success_mark_of_ne
            candidateConclusionDifferent equation
        rw [unchanged] at nextReady
        exact nextReady
      have candidateNeFired :
          Link.tensor candidateLeft candidateRight candidateConclusion ≠
            Link.par left right conclusion := by
        intro same
        contradiction
      by_cases created : premise = conclusion
      · subst premise
        rcases firePar?_success_conclusion_frontier
            abstractable equation with
          ⟨outputToken, nextComponent, conclusionToken,
            componentLookup, conclusionMembership⟩
        rw [conclusionToken] at nextPremiseToken
        injection nextPremiseToken with tokenEquation
        subst token
        exact
          ⟨nextComponent, componentLookup, conclusionMembership⟩
      · have oldPremiseToken :
            state.tokenAt? premise = some token := by
          have unchanged :=
            firePar?_success_tokenAt?_of_ne created equation
          rw [unchanged] at nextPremiseToken
          exact nextPremiseToken
        rcases covered linkMembership oldReady premiseMembership
            oldPremiseToken with
          ⟨component, componentLookup, frontierMembership⟩
        have candidatePremise :
            premise ∈
              (Link.tensor candidateLeft candidateRight
                candidateConclusion).premises := by
          simpa [Link.premises] using premiseMembership
        have notLeft : premise ≠ left := by
          intro same
          subst premise
          have sameLink :=
            UnificationState.StructurallyWellFormed.parentLink_unique
              structural linkMembership candidatePremise
                firedMembership (by simp [Link.premises])
          exact candidateNeFired sameLink
        have notRight : premise ≠ right := by
          intro same
          subst premise
          have sameLink :=
            UnificationState.StructurallyWellFormed.parentLink_unique
              structural linkMembership candidatePremise
                firedMembership (by simp [Link.premises])
          exact candidateNeFired sameLink
        exact firePar?_success_frontier_of_ne
          abstractable oldPremiseToken componentLookup
            frontierMembership notLeft notRight equation

/-- A successful well-typed par firing replaces one live component with the
formula-consistent par derivation built from its selected frontier
occurrences. -/
private theorem firePar?_success_componentsFormulaConsistent
    {certificate : Certificate} {state next : UnificationState}
    (consistent :
      state.ComponentsFormulaConsistent certificate)
    {left right conclusion : Vertex}
    (wellFormed :
      certificate.LinkWellFormed (.par left right conclusion))
    (equation : firePar? state left right conclusion = some next) :
    next.ComponentsFormulaConsistent certificate := by
  unfold firePar? at equation
  split at equation
  · contradiction
  · rename_i _ outputToken forwardEquation
    split at equation
    · contradiction
    · rename_i _ component componentEquation
      split at equation
      · contradiction
      · rename_i _ leftFocus afterLeft leftPick
        split at equation
        · contradiction
        · rename_i _ rightFocus context rightPick
          injection equation with stateEquation
          subst next
          have componentLookup :
              state.components[state.representative outputToken]? =
                some (some component) := by
            unfold UnificationState.componentAt? at componentEquation
            cases lookup :
                state.components[state.representative outputToken]? with
            | none =>
                simp [lookup] at componentEquation
            | some assigned =>
                cases assigned with
                | none =>
                    simp [lookup] at componentEquation
                | some stored =>
                    simp [lookup] at componentEquation
                    subst stored
                    rfl
          have componentConsistent :
              component.FormulaConsistent certificate :=
            consistent componentLookup
          rcases wellFormed.par_formulaData with
            ⟨leftFormula, rightFormula, leftFormulaAt,
              rightFormulaAt, conclusionFormula⟩
          have nextComponentConsistent :
              ({ tree :=
                   .par leftFocus rightFocus component.tree
                 frontier := context ++ [conclusion] } :
                UnificationComponent).FormulaConsistent certificate :=
            UnificationComponent.FormulaConsistent.par
              componentConsistent leftPick rightPick
                leftFormulaAt rightFormulaAt conclusionFormula
          change
            ({ state with
              components :=
                state.components.setIfInBounds outputToken
                  (some
                    { tree :=
                        .par leftFocus rightFocus component.tree
                      frontier := context ++ [conclusion] }) } :
              UnificationState).ComponentsFormulaConsistent certificate
          exact consistent.set (index := outputToken)
            nextComponentConsistent

/-- Every successful concrete par firing leaves the ordered parent forest
unchanged. -/
private theorem firePar?_success_ordered
    {state next : UnificationState}
    (ordered : state.OrderedParents)
    {left right conclusion : Vertex}
    (equation : firePar? state left right conclusion = some next) :
    next.OrderedParents := by
  rcases firePar?_success_observation equation with
    ⟨outputToken, forwardEquation, observation⟩
  have markedOrdered :
      (state.markConclusion conclusion outputToken).OrderedParents :=
    UnificationState.OrderedParents.markConclusion
      ordered conclusion outputToken
  have nextOrdered : next.OrderedParents :=
    UnificationState.ObservationEquivalent.orderedParents
      observation markedOrdered
  intro token parent lookup
  exact nextOrdered lookup

/-- Every successful concrete par firing, including component construction,
refines one independent Figure-5 forward step. -/
private theorem firePar?_refines_forward
    (certificate : Certificate)
    {state next : UnificationState}
    (abstractable : state.Abstractable certificate)
    {left right conclusion : Vertex}
    (linkMembership :
      Link.par left right conclusion ∈ certificate.links)
    (equation : firePar? state left right conclusion = some next) :
    ∃ nextAbstractable : next.Abstractable certificate,
      UnificationStep certificate
        (state.toMarking certificate abstractable)
        (next.toMarking certificate nextAbstractable) := by
  rcases firePar?_success_observation equation with
    ⟨outputToken, forwardEquation, observation⟩
  rcases state.forwardToken?_refines abstractable linkMembership
      forwardEquation with
    ⟨markedAbstractable, markedStep⟩
  let nextAbstractable :=
    observation.abstractable markedAbstractable
  refine ⟨nextAbstractable, ?_⟩
  rw [observation.toMarking_eq markedAbstractable]
  exact markedStep

/-- Fire a Guerrini binary/`tensor` rule when its premises yield distinct
tokens, merge their components, and point the larger representative at the
smaller one. -/
private def fireTensor? (state : UnificationState)
    (left right conclusion : Vertex) :
    Option UnificationState :=
  match state.unifyTokens? left right conclusion with
  | none => none
  | some (leftToken, rightToken) =>
      match state.componentAt? leftToken with
      | none => none
      | some leftComponent =>
          match state.componentAt? rightToken with
          | none => none
          | some rightComponent =>
              match pickVertex? leftComponent.frontier left with
              | none => none
              | some (leftFocus, leftContext) =>
                  match pickVertex? rightComponent.frontier right with
                  | none => none
                  | some (rightFocus, rightContext) =>
                      let representative := min leftToken rightToken
                      let retired := max leftToken rightToken
                      let nextComponent : UnificationComponent :=
                        { tree :=
                            .tensor leftFocus rightFocus
                              leftComponent.tree rightComponent.tree
                          frontier :=
                            conclusion :: (leftContext ++ rightContext) }
                      let merged :=
                        state.mergeConclusion conclusion
                          representative retired
                      some {
                        merged with
                        components :=
                          (state.components.setIfInBounds representative
                            (some nextComponent))
                            |>.setIfInBounds retired none
                      }

/-- Frontier coverage makes a guard-ready tensor firing operationally total.
The two distinct current representatives expose the two concrete premise
occurrences in their respective live components. -/
private theorem fireTensor?_exists_of_ready
    {certificate : Certificate} {state : UnificationState}
    (covered : state.PendingPremisesCovered certificate)
    {left right conclusion leftToken rightToken : Nat}
    (linkMembership :
      Link.tensor left right conclusion ∈ certificate.links)
    (conclusionReady : state.marks[conclusion]? = some none)
    (leftReady : state.tokenAt? left = some leftToken)
    (rightReady : state.tokenAt? right = some rightToken)
    (different : leftToken ≠ rightToken) :
    ∃ next,
      fireTensor? state left right conclusion = some next := by
  have unifyReady :
      state.unifyTokens? left right conclusion =
        some (leftToken, rightToken) := by
    simp [UnificationState.unifyTokens?, conclusionReady,
      leftReady, rightReady, different]
  have pendingCoverage :
      ∀ {premise token : Nat}, premise ∈ [left, right] →
        state.tokenAt? premise = some token →
          ∃ component,
            state.componentAt? token = some component ∧
              premise ∈ component.frontier :=
    covered linkMembership conclusionReady
  rcases pendingCoverage (premise := left) (token := leftToken)
      (by simp) leftReady with
    ⟨leftComponent, leftComponentLookup, leftMembership⟩
  rcases pendingCoverage (premise := right) (token := rightToken)
      (by simp) rightReady with
    ⟨rightComponent, rightComponentLookup, rightMembership⟩
  rcases pickVertex?_exists_of_mem leftMembership with
    ⟨leftIndex, leftContext, leftPicked⟩
  rcases pickVertex?_exists_of_mem rightMembership with
    ⟨rightIndex, rightContext, rightPicked⟩
  simp [fireTensor?, unifyReady, leftComponentLookup,
    rightComponentLookup, leftPicked, rightPicked]

/-- Successful tensor component construction changes the observable state
exactly by the token-semantic mark-and-parent update selected by the two
distinct representatives. -/
private theorem fireTensor?_success_observation
    {state next : UnificationState}
    {left right conclusion : Vertex}
    (equation : fireTensor? state left right conclusion = some next) :
    ∃ leftToken rightToken,
      state.unifyTokens? left right conclusion =
          some (leftToken, rightToken) ∧
        UnificationState.ObservationEquivalent
          (state.mergeConclusion conclusion
            (min leftToken rightToken) (max leftToken rightToken))
          next := by
  unfold fireTensor? at equation
  split at equation
  · contradiction
  · rename_i _ leftToken rightToken unifyEquation
    refine ⟨leftToken, rightToken, unifyEquation, ?_⟩
    split at equation
    · contradiction
    · split at equation
      · contradiction
      · split at equation
        · contradiction
        · split at equation
          · contradiction
          · cases equation
            exact ⟨rfl, rfl⟩

/-- Every successful in-domain tensor firing visibly marks its conclusion. -/
private theorem fireTensor?_success_conclusion_marked
    {certificate : Certificate} {state next : UnificationState}
    (abstractable : state.Abstractable certificate)
    {left right conclusion : Vertex}
    (conclusionBound : conclusion < certificate.formulas.size)
    (equation : fireTensor? state left right conclusion = some next) :
    next.assignedToken? conclusion ≠ none := by
  rcases fireTensor?_success_observation equation with
    ⟨leftToken, rightToken, _unifyEquation, observation⟩
  unfold UnificationState.assignedToken?
  rw [← observation.marks]
  simp [UnificationState.mergeConclusion,
    UnificationState.setParent, UnificationState.markConclusion,
    conclusionBound, abstractable.markArraySize]

/-- A successful tensor firing changes no raw mark except its conclusion
slot; the union operation changes only parent representatives. -/
private theorem fireTensor?_success_mark_of_ne
    {state next : UnificationState}
    {left right conclusion vertex : Vertex}
    (different : vertex ≠ conclusion)
    (equation : fireTensor? state left right conclusion = some next) :
    next.marks[vertex]? = state.marks[vertex]? := by
  rcases fireTensor?_success_observation equation with
    ⟨leftToken, rightToken, _unifyEquation, observation⟩
  rw [← observation.marks]
  simp [UnificationState.mergeConclusion,
    UnificationState.setParent, UnificationState.markConclusion,
    different.symm]

/-- Tensor firing is also monotone on marked occurrences.  The root union may
rename their current representatives, but it never removes a raw mark. -/
private theorem fireTensor?_success_preserves_assigned
    {certificate : Certificate} {state next : UnificationState}
    (abstractable : state.Abstractable certificate)
    {left right conclusion vertex : Vertex}
    (conclusionBound : conclusion < certificate.formulas.size)
    (marked : state.assignedToken? vertex ≠ none)
    (equation : fireTensor? state left right conclusion = some next) :
    next.assignedToken? vertex ≠ none := by
  by_cases same : vertex = conclusion
  · subst vertex
    exact fireTensor?_success_conclusion_marked
      abstractable conclusionBound equation
  · cases oldLookup : state.assignedToken? vertex with
    | none =>
        exact False.elim (marked oldLookup)
    | some token =>
        have oldRaw :
            state.marks[vertex]? = some (some token) :=
          UnificationState.assignedToken?_some_raw oldLookup
        have nextRaw :
            next.marks[vertex]? = some (some token) := by
          rw [fireTensor?_success_mark_of_ne same equation]
          exact oldRaw
        unfold UnificationState.assignedToken?
        rw [nextRaw]
        simp

/-- Any non-conclusion occurrence marked after a tensor firing was already
marked before the firing, although its current representative may have
changed through the root union. -/
private theorem fireTensor?_success_old_tokenAt?_of_ne
    {state next : UnificationState}
    {left right conclusion vertex nextToken : Vertex}
    (different : vertex ≠ conclusion)
    (nextMarked : next.tokenAt? vertex = some nextToken)
    (equation : fireTensor? state left right conclusion = some next) :
    ∃ oldToken, state.tokenAt? vertex = some oldToken := by
  rcases next.tokenAt?_some_witness nextMarked with
    ⟨rawToken, nextRawMarked, _nextRepresentative⟩
  have nextRawLookup :
      next.marks[vertex]? = some (some rawToken) :=
    UnificationState.assignedToken?_some_raw nextRawMarked
  have unchanged :=
    fireTensor?_success_mark_of_ne different equation
  rw [unchanged] at nextRawLookup
  refine ⟨state.representative rawToken, ?_⟩
  unfold UnificationState.tokenAt?
  rw [nextRawLookup]
  rfl

/-- A non-conclusion occurrence which was unmarked before a successful tensor
firing remains unmarked afterwards.  This is the contrapositive form needed
to transport an idle scheduler classification across a root union. -/
private theorem fireTensor?_success_tokenAt?_none_of_ne
    {state next : UnificationState}
    {left right conclusion vertex : Vertex}
    (different : vertex ≠ conclusion)
    (unmarked : state.tokenAt? vertex = none)
    (equation : fireTensor? state left right conclusion = some next) :
    next.tokenAt? vertex = none := by
  cases nextLookup : next.tokenAt? vertex with
  | none =>
      rfl
  | some nextToken =>
      rcases fireTensor?_success_old_tokenAt?_of_ne
          different nextLookup equation with
        ⟨oldToken, oldLookup⟩
      rw [unmarked] at oldLookup
      contradiction

/-- A successful tensor union cannot split an already shared token class.
For two old non-conclusion occurrences which yielded the same representative,
their new representative may be renamed by the union, but remains shared. -/
private theorem fireTensor?_success_same_tokenAt?_of_ne
    {certificate : Certificate} {state next : UnificationState}
    (abstractable : state.Abstractable certificate)
    (ordered : state.OrderedParents)
    {left right conclusion first second token : Vertex}
    (firstDifferent : first ≠ conclusion)
    (secondDifferent : second ≠ conclusion)
    (firstLookup : state.tokenAt? first = some token)
    (secondLookup : state.tokenAt? second = some token)
    (equation : fireTensor? state left right conclusion = some next) :
    ∃ nextToken,
      next.tokenAt? first = some nextToken ∧
        next.tokenAt? second = some nextToken := by
  rcases state.tokenAt?_some_witness firstLookup with
    ⟨firstRaw, firstMarked, firstRepresentative⟩
  rcases state.tokenAt?_some_witness secondLookup with
    ⟨secondRaw, secondMarked, secondRepresentative⟩
  have firstRawLookup :
      state.marks[first]? = some (some firstRaw) :=
    UnificationState.assignedToken?_some_raw firstMarked
  have secondRawLookup :
      state.marks[second]? = some (some secondRaw) :=
    UnificationState.assignedToken?_some_raw secondMarked
  have firstBound : firstRaw < state.parents.size :=
    abstractable.markedTokenBound firstMarked
  have secondBound : secondRaw < state.parents.size :=
    abstractable.markedTokenBound secondMarked
  rcases fireTensor?_success_observation equation with
    ⟨leftToken, rightToken, unifyEquation, observation⟩
  have guards := state.unifyTokens?_success unifyEquation
  have leftBound : leftToken < state.parents.size :=
    abstractable.tokenAt?_bound guards.2.1
  have rightBound : rightToken < state.parents.size :=
    abstractable.tokenAt?_bound guards.2.2.1
  have leftRoot : state.representative leftToken = leftToken :=
    abstractable.tokenAt?_root guards.2.1
  have rightRoot : state.representative rightToken = rightToken :=
    abstractable.tokenAt?_root guards.2.2.1
  have tokensDifferent : leftToken ≠ rightToken :=
    guards.2.2.2
  let survivor := min leftToken rightToken
  let retired := max leftToken rightToken
  have survivorBound : survivor < state.parents.size := by
    exact Nat.lt_of_le_of_lt
      (Nat.min_le_left leftToken rightToken) leftBound
  have retiredBound : retired < state.parents.size := by
    exact Nat.max_lt.mpr ⟨leftBound, rightBound⟩
  have survivorLt : survivor < retired := by
    rcases Nat.lt_or_gt_of_ne tokensDifferent with
      leftLess | rightLess
    · simpa [survivor, retired,
        Nat.min_eq_left (Nat.le_of_lt leftLess),
        Nat.max_eq_right (Nat.le_of_lt leftLess)] using leftLess
    · simpa [survivor, retired,
        Nat.min_eq_right (Nat.le_of_lt rightLess),
        Nat.max_eq_left (Nat.le_of_lt rightLess)] using rightLess
  have survivorRoot :
      state.representative survivor = survivor := by
    rcases Nat.lt_or_gt_of_ne tokensDifferent with
      leftLess | rightLess
    · simpa [survivor,
        Nat.min_eq_left (Nat.le_of_lt leftLess)] using leftRoot
    · simpa [survivor,
        Nat.min_eq_right (Nat.le_of_lt rightLess)] using rightRoot
  have retiredRoot :
      state.representative retired = retired := by
    rcases Nat.lt_or_gt_of_ne tokensDifferent with
      leftLess | rightLess
    · simpa [retired,
        Nat.max_eq_right (Nat.le_of_lt leftLess)] using rightRoot
    · simpa [retired,
        Nat.max_eq_left (Nat.le_of_lt rightLess)] using leftRoot
  have nextRepresentativesEqual :
      next.representative firstRaw =
        next.representative secondRaw := by
    rw [observation.representative_eq firstRaw,
      observation.representative_eq secondRaw]
    change
      (state.setParent retired survivor).representative firstRaw =
        (state.setParent retired survivor).representative secondRaw
    rw [ordered.setParent_representative
          survivorBound retiredBound survivorLt
          survivorRoot retiredRoot firstBound,
      ordered.setParent_representative
          survivorBound retiredBound survivorLt
          survivorRoot retiredRoot secondBound,
      firstRepresentative, secondRepresentative]
  refine ⟨next.representative firstRaw, ?_, ?_⟩
  · unfold UnificationState.tokenAt?
    rw [fireTensor?_success_mark_of_ne firstDifferent equation,
      firstRawLookup]
    rfl
  · unfold UnificationState.tokenAt?
    rw [fireTensor?_success_mark_of_ne secondDifferent equation,
      secondRawLookup]
    exact congrArg some nextRepresentativesEqual.symm

/-- The conclusion created by a successful tensor firing is exposed on the
frontier of the merged live component at the surviving representative. -/
private theorem fireTensor?_success_conclusion_frontier
    {certificate : Certificate} {state next : UnificationState}
    (abstractable : state.Abstractable certificate)
    (ordered : state.OrderedParents)
    {left right conclusion : Vertex}
    (equation : fireTensor? state left right conclusion = some next) :
    ∃ outputToken nextComponent,
      next.tokenAt? conclusion = some outputToken ∧
        next.componentAt? outputToken = some nextComponent ∧
          conclusion ∈ nextComponent.frontier := by
  rcases fireTensor?_success_observation equation with
    ⟨leftToken, rightToken, unifyEquation, observation⟩
  have guards := state.unifyTokens?_success unifyEquation
  have leftBound : leftToken < state.parents.size :=
    abstractable.tokenAt?_bound guards.2.1
  have rightBound : rightToken < state.parents.size :=
    abstractable.tokenAt?_bound guards.2.2.1
  have leftRoot : state.representative leftToken = leftToken :=
    abstractable.tokenAt?_root guards.2.1
  have rightRoot : state.representative rightToken = rightToken :=
    abstractable.tokenAt?_root guards.2.2.1
  have tokensDifferent : leftToken ≠ rightToken :=
    guards.2.2.2
  let survivor := min leftToken rightToken
  let retired := max leftToken rightToken
  have survivorBound : survivor < state.parents.size := by
    exact Nat.lt_of_le_of_lt
      (Nat.min_le_left leftToken rightToken) leftBound
  have retiredBound : retired < state.parents.size := by
    exact Nat.max_lt.mpr ⟨leftBound, rightBound⟩
  have survivorLt : survivor < retired := by
    rcases Nat.lt_or_gt_of_ne tokensDifferent with
      leftLess | rightLess
    · simpa [survivor, retired,
        Nat.min_eq_left (Nat.le_of_lt leftLess),
        Nat.max_eq_right (Nat.le_of_lt leftLess)] using leftLess
    · simpa [survivor, retired,
        Nat.min_eq_right (Nat.le_of_lt rightLess),
        Nat.max_eq_left (Nat.le_of_lt rightLess)] using rightLess
  have survivorRoot :
      state.representative survivor = survivor := by
    rcases Nat.lt_or_gt_of_ne tokensDifferent with
      leftLess | rightLess
    · simpa [survivor,
        Nat.min_eq_left (Nat.le_of_lt leftLess)] using leftRoot
    · simpa [survivor,
        Nat.min_eq_right (Nat.le_of_lt rightLess)] using rightRoot
  have retiredRoot :
      state.representative retired = retired := by
    rcases Nat.lt_or_gt_of_ne tokensDifferent with
      leftLess | rightLess
    · simpa [retired,
        Nat.max_eq_right (Nat.le_of_lt leftLess)] using rightRoot
    · simpa [retired,
        Nat.max_eq_left (Nat.le_of_lt rightLess)] using leftRoot
  have mergedSurvivorRoot :
      UnificationState.representative
        (state.mergeConclusion conclusion survivor retired)
        survivor = survivor := by
    have updated :=
      ordered.setParent_representative survivorBound retiredBound
        survivorLt survivorRoot retiredRoot survivorBound
    change
      (state.setParent retired survivor).representative survivor =
        survivor
    rw [updated, survivorRoot]
    simp [Nat.ne_of_lt survivorLt]
  have nextSurvivorRoot :
      next.representative survivor = survivor := by
    rw [observation.representative_eq survivor]
    exact mergedSurvivorRoot
  have conclusionIndexBound : conclusion < state.marks.size :=
    (Array.getElem?_eq_some_iff.mp guards.1).1
  have conclusionToken :
      next.tokenAt? conclusion = some survivor := by
    unfold UnificationState.tokenAt?
    rw [← observation.marks]
    simp [UnificationState.mergeConclusion,
      UnificationState.setParent, UnificationState.markConclusion,
      conclusionIndexBound]
    simpa [survivor] using nextSurvivorRoot
  unfold fireTensor? at equation
  rw [unifyEquation] at equation
  cases leftComponentLookup :
      state.componentAt? leftToken with
  | none =>
      simp [leftComponentLookup] at equation
  | some leftComponent =>
      simp only [leftComponentLookup] at equation
      cases rightComponentLookup :
          state.componentAt? rightToken with
      | none =>
          simp [rightComponentLookup] at equation
      | some rightComponent =>
          simp only [rightComponentLookup] at equation
          cases leftPick :
              pickVertex? leftComponent.frontier left with
          | none =>
              simp [leftPick] at equation
          | some leftResult =>
              rcases leftResult with ⟨leftIndex, leftContext⟩
              simp only [leftPick] at equation
              cases rightPick :
                  pickVertex? rightComponent.frontier right with
              | none =>
                  simp [rightPick] at equation
              | some rightResult =>
                  rcases rightResult with
                    ⟨rightIndex, rightContext⟩
                  simp only [rightPick] at equation
                  injection equation with nextEquation
                  subst next
                  let replacement : UnificationComponent :=
                    { tree :=
                        .tensor leftIndex rightIndex
                          leftComponent.tree rightComponent.tree
                      frontier :=
                        conclusion ::
                          (leftContext ++ rightContext) }
                  have leftComponentRaw :
                      state.components[leftToken]? =
                        some (some leftComponent) := by
                    have rawAtRepresentative :=
                      UnificationState.componentAt?_some_raw
                        leftComponentLookup
                    simpa [leftRoot] using rawAtRepresentative
                  have leftComponentBound :
                      leftToken < state.components.size :=
                    (Array.getElem?_eq_some_iff.mp
                      leftComponentRaw).1
                  have minBound :
                      min leftToken rightToken <
                        state.components.size :=
                    Nat.lt_of_le_of_lt
                      (Nat.min_le_left leftToken rightToken)
                      leftComponentBound
                  refine
                    ⟨survivor, replacement, conclusionToken, ?_, ?_⟩
                  · unfold UnificationState.componentAt?
                    rw [nextSurvivorRoot]
                    have survivorNeRetired : survivor ≠ retired :=
                      Nat.ne_of_lt survivorLt
                    simp [replacement, survivor, retired,
                      minBound,
                      Ne.symm survivorNeRetired]
                  · simp [replacement]

/-- A successful tensor firing transports every non-consumed old frontier
occurrence into the merged component or leaves its unrelated component
untouched.  The returned token is the occurrence's representative after the
single root union. -/
private theorem fireTensor?_success_frontier_of_ne
    {certificate : Certificate} {state next : UnificationState}
    (abstractable : state.Abstractable certificate)
    (ordered : state.OrderedParents)
    {left right conclusion vertex token : Vertex}
    {component : UnificationComponent}
    (vertexToken : state.tokenAt? vertex = some token)
    (componentLookup : state.componentAt? token = some component)
    (vertexMembership : vertex ∈ component.frontier)
    (notLeft : vertex ≠ left) (notRight : vertex ≠ right)
    (equation : fireTensor? state left right conclusion = some next) :
    ∃ nextToken nextComponent,
      next.tokenAt? vertex = some nextToken ∧
        next.componentAt? nextToken = some nextComponent ∧
          vertex ∈ nextComponent.frontier := by
  rcases fireTensor?_success_observation equation with
    ⟨leftToken, rightToken, unifyEquation, observation⟩
  have guards := state.unifyTokens?_success unifyEquation
  have leftBound : leftToken < state.parents.size :=
    abstractable.tokenAt?_bound guards.2.1
  have rightBound : rightToken < state.parents.size :=
    abstractable.tokenAt?_bound guards.2.2.1
  have leftRoot : state.representative leftToken = leftToken :=
    abstractable.tokenAt?_root guards.2.1
  have rightRoot : state.representative rightToken = rightToken :=
    abstractable.tokenAt?_root guards.2.2.1
  have tokensDifferent : leftToken ≠ rightToken :=
    guards.2.2.2
  have tokenBound : token < state.parents.size :=
    abstractable.tokenAt?_bound vertexToken
  have tokenRoot : state.representative token = token :=
    abstractable.tokenAt?_root vertexToken
  have vertexDifferentConclusion : vertex ≠ conclusion := by
    intro same
    subst vertex
    unfold UnificationState.tokenAt? at vertexToken
    rw [guards.1] at vertexToken
    contradiction
  let survivor := min leftToken rightToken
  let retired := max leftToken rightToken
  have survivorBound : survivor < state.parents.size := by
    exact Nat.lt_of_le_of_lt
      (Nat.min_le_left leftToken rightToken) leftBound
  have retiredBound : retired < state.parents.size := by
    exact Nat.max_lt.mpr ⟨leftBound, rightBound⟩
  have survivorLt : survivor < retired := by
    rcases Nat.lt_or_gt_of_ne tokensDifferent with
      leftLess | rightLess
    · simpa [survivor, retired,
        Nat.min_eq_left (Nat.le_of_lt leftLess),
        Nat.max_eq_right (Nat.le_of_lt leftLess)] using leftLess
    · simpa [survivor, retired,
        Nat.min_eq_right (Nat.le_of_lt rightLess),
        Nat.max_eq_left (Nat.le_of_lt rightLess)] using rightLess
  have survivorRoot :
      state.representative survivor = survivor := by
    rcases Nat.lt_or_gt_of_ne tokensDifferent with
      leftLess | rightLess
    · simpa [survivor,
        Nat.min_eq_left (Nat.le_of_lt leftLess)] using leftRoot
    · simpa [survivor,
        Nat.min_eq_right (Nat.le_of_lt rightLess)] using rightRoot
  have retiredRoot :
      state.representative retired = retired := by
    rcases Nat.lt_or_gt_of_ne tokensDifferent with
      leftLess | rightLess
    · simpa [retired,
        Nat.max_eq_right (Nat.le_of_lt leftLess)] using rightRoot
    · simpa [retired,
        Nat.max_eq_left (Nat.le_of_lt rightLess)] using leftRoot
  have mergedSurvivorRoot :
      UnificationState.representative
        (state.mergeConclusion conclusion survivor retired)
        survivor = survivor := by
    have updated :=
      ordered.setParent_representative survivorBound retiredBound
        survivorLt survivorRoot retiredRoot survivorBound
    change
      (state.setParent retired survivor).representative survivor =
        survivor
    rw [updated, survivorRoot]
    simp [Nat.ne_of_lt survivorLt]
  have nextSurvivorRoot :
      next.representative survivor = survivor := by
    rw [observation.representative_eq survivor]
    simpa [survivor, retired] using mergedSurvivorRoot
  rcases state.tokenAt?_some_witness vertexToken with
    ⟨rawToken, rawMarked, rawRepresentative⟩
  have rawBound : rawToken < state.parents.size :=
    abstractable.markedTokenBound rawMarked
  have rawLookup :
      state.marks[vertex]? = some (some rawToken) :=
    UnificationState.assignedToken?_some_raw rawMarked
  have mergedRawRepresentative :
      UnificationState.representative
        (state.mergeConclusion conclusion survivor retired)
        rawToken =
          if token = retired then survivor else token := by
    have updated :=
      ordered.setParent_representative survivorBound retiredBound
        survivorLt survivorRoot retiredRoot rawBound
    change
      (state.setParent retired survivor).representative rawToken =
        if token = retired then survivor else token
    rw [updated, rawRepresentative]
  have nextRawRepresentative :
      next.representative rawToken =
        if token = retired then survivor else token := by
    rw [observation.representative_eq rawToken]
    simpa [survivor, retired] using mergedRawRepresentative
  have nextRawLookup :
      next.marks[vertex]? = some (some rawToken) := by
    rw [← observation.marks]
    simpa [UnificationState.mergeConclusion,
      UnificationState.setParent, UnificationState.markConclusion,
      vertexDifferentConclusion.symm] using rawLookup
  have nextVertexToken :
      next.tokenAt? vertex =
        some (if token = retired then survivor else token) := by
    unfold UnificationState.tokenAt?
    rw [nextRawLookup]
    simp [nextRawRepresentative]
  unfold fireTensor? at equation
  rw [unifyEquation] at equation
  cases leftComponentLookup :
      state.componentAt? leftToken with
  | none =>
      simp [leftComponentLookup] at equation
  | some leftComponent =>
      simp only [leftComponentLookup] at equation
      cases rightComponentLookup :
          state.componentAt? rightToken with
      | none =>
          simp [rightComponentLookup] at equation
      | some rightComponent =>
          simp only [rightComponentLookup] at equation
          cases leftPick :
              pickVertex? leftComponent.frontier left with
          | none =>
              simp [leftPick] at equation
          | some leftResult =>
              rcases leftResult with ⟨leftIndex, leftContext⟩
              simp only [leftPick] at equation
              cases rightPick :
                  pickVertex? rightComponent.frontier right with
              | none =>
                  simp [rightPick] at equation
              | some rightResult =>
                  rcases rightResult with
                    ⟨rightIndex, rightContext⟩
                  simp only [rightPick] at equation
                  injection equation with nextEquation
                  subst next
                  let replacement : UnificationComponent :=
                    { tree :=
                        .tensor leftIndex rightIndex
                          leftComponent.tree rightComponent.tree
                      frontier :=
                        conclusion ::
                          (leftContext ++ rightContext) }
                  have leftComponentRaw :
                      state.components[leftToken]? =
                        some (some leftComponent) := by
                    have rawAtRepresentative :=
                      UnificationState.componentAt?_some_raw
                        leftComponentLookup
                    simpa [leftRoot] using rawAtRepresentative
                  have leftComponentBound :
                      leftToken < state.components.size :=
                    (Array.getElem?_eq_some_iff.mp
                      leftComponentRaw).1
                  have minComponentBound :
                      min leftToken rightToken <
                        state.components.size :=
                    Nat.lt_of_le_of_lt
                      (Nat.min_le_left leftToken rightToken)
                      leftComponentBound
                  have replacementLookup :
                      ({ marks :=
                           (state.mergeConclusion conclusion
                             (min leftToken rightToken)
                             (max leftToken rightToken)).marks
                         parents :=
                           (state.mergeConclusion conclusion
                             (min leftToken rightToken)
                             (max leftToken rightToken)).parents
                         components :=
                           (state.components.setIfInBounds
                              (min leftToken rightToken)
                              (some replacement))
                             |>.setIfInBounds
                               (max leftToken rightToken) none
                         startedAxioms :=
                           (state.mergeConclusion conclusion
                             (min leftToken rightToken)
                             (max leftToken rightToken)).startedAxioms
                         firedConnectives :=
                           (state.mergeConclusion conclusion
                             (min leftToken rightToken)
                             (max leftToken rightToken))
                               |>.firedConnectives } :
                        UnificationState).componentAt? survivor =
                          some replacement := by
                    unfold UnificationState.componentAt?
                    rw [nextSurvivorRoot]
                    have retiredNeSurvivor : retired ≠ survivor :=
                      Ne.symm (Nat.ne_of_lt survivorLt)
                    simp [replacement, survivor, retired,
                      minComponentBound, retiredNeSurvivor]
                  by_cases sameLeft : token = leftToken
                  · have componentEquation :
                        component = leftComponent := by
                      rw [sameLeft, leftComponentLookup] at componentLookup
                      injection componentLookup with equality
                      exact equality.symm
                    subst component
                    have leftContextMembership :
                        vertex ∈ leftContext :=
                      pickVertex?_mem_remaining_of_ne
                        leftPick notLeft vertexMembership
                    have leftMerged :
                        (if leftToken = retired then
                            survivor else leftToken) = survivor := by
                      rcases Nat.lt_or_gt_of_ne tokensDifferent with
                        leftLess | rightLess
                      · simp [survivor, retired,
                          Nat.min_eq_left (Nat.le_of_lt leftLess),
                          Nat.max_eq_right (Nat.le_of_lt leftLess),
                          Nat.ne_of_lt leftLess]
                      · simp [survivor, retired,
                          Nat.min_eq_right (Nat.le_of_lt rightLess),
                          Nat.max_eq_left (Nat.le_of_lt rightLess)]
                    rw [sameLeft] at nextVertexToken
                    rw [leftMerged] at nextVertexToken
                    refine
                      ⟨survivor, replacement, nextVertexToken,
                        replacementLookup, ?_⟩
                    simp [replacement, leftContextMembership]
                  · by_cases sameRight : token = rightToken
                    · have componentEquation :
                          component = rightComponent := by
                        rw [sameRight, rightComponentLookup] at componentLookup
                        injection componentLookup with equality
                        exact equality.symm
                      subst component
                      have rightContextMembership :
                          vertex ∈ rightContext :=
                        pickVertex?_mem_remaining_of_ne
                          rightPick notRight vertexMembership
                      have rightMerged :
                          (if rightToken = retired then
                              survivor else rightToken) = survivor := by
                        rcases Nat.lt_or_gt_of_ne tokensDifferent with
                          leftLess | rightLess
                        · simp [survivor, retired,
                            Nat.min_eq_left (Nat.le_of_lt leftLess),
                            Nat.max_eq_right (Nat.le_of_lt leftLess)]
                        · have rightNeLeft : rightToken ≠ leftToken :=
                            Ne.symm tokensDifferent
                          simp [survivor, retired,
                            Nat.min_eq_right (Nat.le_of_lt rightLess),
                            Nat.max_eq_left (Nat.le_of_lt rightLess),
                            rightNeLeft]
                      rw [sameRight] at nextVertexToken
                      rw [rightMerged] at nextVertexToken
                      refine
                        ⟨survivor, replacement, nextVertexToken,
                          replacementLookup, ?_⟩
                      simp [replacement, rightContextMembership]
                    · have tokenNeSurvivor : token ≠ survivor := by
                        rcases Nat.lt_or_gt_of_ne tokensDifferent with
                          leftLess | rightLess
                        · simpa [survivor,
                            Nat.min_eq_left
                              (Nat.le_of_lt leftLess)] using sameLeft
                        · simpa [survivor,
                            Nat.min_eq_right
                              (Nat.le_of_lt rightLess)] using sameRight
                      have tokenNeRetired : token ≠ retired := by
                        rcases Nat.lt_or_gt_of_ne tokensDifferent with
                          leftLess | rightLess
                        · simpa [retired,
                            Nat.max_eq_right
                              (Nat.le_of_lt leftLess)] using sameRight
                        · simpa [retired,
                            Nat.max_eq_left
                              (Nat.le_of_lt rightLess)] using sameLeft
                      have nextTokenSame :
                          (if token = retired then
                              survivor else token) = token := by
                        simp [tokenNeRetired]
                      rw [nextTokenSame] at nextVertexToken
                      have componentRaw :
                          state.components[token]? =
                            some (some component) := by
                        have rawAtRepresentative :=
                          UnificationState.componentAt?_some_raw
                            componentLookup
                        simpa [tokenRoot] using rawAtRepresentative
                      have mergedTokenRoot :
                          UnificationState.representative
                            (state.mergeConclusion conclusion
                              survivor retired) token = token := by
                        have updated :=
                          ordered.setParent_representative
                            survivorBound retiredBound survivorLt
                              survivorRoot retiredRoot tokenBound
                        change
                          UnificationState.representative
                            (state.setParent retired survivor)
                            token = token
                        rw [updated, tokenRoot]
                        simp [tokenNeRetired]
                      have nextTokenRoot :
                          ({ marks :=
                               (state.mergeConclusion conclusion
                                 (min leftToken rightToken)
                                 (max leftToken rightToken)).marks
                             parents :=
                               (state.mergeConclusion conclusion
                                 (min leftToken rightToken)
                                 (max leftToken rightToken)).parents
                             components :=
                               (state.components.setIfInBounds
                                  (min leftToken rightToken)
                                  (some replacement))
                                 |>.setIfInBounds
                                   (max leftToken rightToken) none
                             startedAxioms :=
                               (state.mergeConclusion conclusion
                                 (min leftToken rightToken)
                                 (max leftToken rightToken)).startedAxioms
                             firedConnectives :=
                               (state.mergeConclusion conclusion
                                 (min leftToken rightToken)
                                 (max leftToken rightToken))
                                   |>.firedConnectives } :
                            UnificationState).representative token =
                              token := by
                        rw [observation.representative_eq token]
                        simpa [survivor, retired] using
                          mergedTokenRoot
                      refine
                        ⟨token, component, nextVertexToken, ?_,
                          vertexMembership⟩
                      unfold UnificationState.componentAt?
                      rw [nextTokenRoot]
                      have minNeToken :
                          min leftToken rightToken ≠ token := by
                        intro same
                        apply tokenNeSurvivor
                        simpa [survivor] using same.symm
                      have maxNeToken :
                          max leftToken rightToken ≠ token := by
                        intro same
                        apply tokenNeRetired
                        simpa [retired] using same.symm
                      simp [minNeToken, maxNeToken, componentRaw]

/-- Firing one tensor link preserves exact frontier coverage for every still
pending connective.  Structural resource ownership rules out accidental
consumption by a different link, and the local frontier transport theorem
accounts for the representative change caused by the union. -/
private theorem fireTensor?_success_pendingPremisesCovered
    {certificate : Certificate} {state next : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (abstractable : state.Abstractable certificate)
    (ordered : state.OrderedParents)
    (covered : state.PendingPremisesCovered certificate)
    {left right conclusion : Vertex}
    (firedMembership :
      Link.tensor left right conclusion ∈ certificate.links)
    (equation : fireTensor? state left right conclusion = some next) :
    next.PendingPremisesCovered certificate := by
  have firedWellFormed :
      certificate.LinkWellFormed (.tensor left right conclusion) :=
    structural.2.2.2.2.1 _ firedMembership
  have conclusionBound : conclusion < certificate.formulas.size :=
    firedWellFormed.2.2.2.2.2.1
  have firedMarked : next.assignedToken? conclusion ≠ none :=
    fireTensor?_success_conclusion_marked
      abstractable conclusionBound equation
  unfold UnificationState.PendingPremisesCovered
  intro link linkMembership
  cases link with
  | «axiom» candidateLeft candidateRight =>
      trivial
  | «par» candidateLeft candidateRight candidateConclusion =>
      intro nextReady premise token premiseMembership nextPremiseToken
      have candidateConclusionDifferent :
          candidateConclusion ≠ conclusion := by
        intro same
        subst candidateConclusion
        apply firedMarked
        unfold UnificationState.assignedToken?
        simp [nextReady]
      have oldReady :
          state.marks[candidateConclusion]? = some none := by
        have unchanged :=
          fireTensor?_success_mark_of_ne
            candidateConclusionDifferent equation
        rw [unchanged] at nextReady
        exact nextReady
      have candidateNeFired :
          Link.par candidateLeft candidateRight candidateConclusion ≠
            Link.tensor left right conclusion := by
        intro same
        contradiction
      by_cases created : premise = conclusion
      · subst premise
        rcases fireTensor?_success_conclusion_frontier
            abstractable ordered equation with
          ⟨outputToken, nextComponent, conclusionToken,
            componentLookup, conclusionMembership⟩
        rw [conclusionToken] at nextPremiseToken
        injection nextPremiseToken with tokenEquation
        subst token
        exact
          ⟨nextComponent, componentLookup, conclusionMembership⟩
      · rcases fireTensor?_success_old_tokenAt?_of_ne
            created nextPremiseToken equation with
          ⟨oldToken, oldPremiseToken⟩
        rcases covered linkMembership oldReady premiseMembership
            oldPremiseToken with
          ⟨component, componentLookup, frontierMembership⟩
        have candidatePremise :
            premise ∈
              (Link.par candidateLeft candidateRight
                candidateConclusion).premises := by
          simpa [Link.premises] using premiseMembership
        have notLeft : premise ≠ left := by
          intro same
          subst premise
          have sameLink :=
            UnificationState.StructurallyWellFormed.parentLink_unique
              structural linkMembership candidatePremise
                firedMembership (by simp [Link.premises])
          exact candidateNeFired sameLink
        have notRight : premise ≠ right := by
          intro same
          subst premise
          have sameLink :=
            UnificationState.StructurallyWellFormed.parentLink_unique
              structural linkMembership candidatePremise
                firedMembership (by simp [Link.premises])
          exact candidateNeFired sameLink
        rcases fireTensor?_success_frontier_of_ne
            abstractable ordered oldPremiseToken componentLookup
              frontierMembership notLeft notRight equation with
          ⟨transportedToken, nextComponent, transportedMarked,
            nextComponentLookup, transportedMembership⟩
        rw [transportedMarked] at nextPremiseToken
        injection nextPremiseToken with tokenEquation
        subst token
        exact
          ⟨nextComponent, nextComponentLookup,
            transportedMembership⟩
  | tensor candidateLeft candidateRight candidateConclusion =>
      intro nextReady premise token premiseMembership nextPremiseToken
      have candidateConclusionDifferent :
          candidateConclusion ≠ conclusion := by
        intro same
        subst candidateConclusion
        apply firedMarked
        unfold UnificationState.assignedToken?
        simp [nextReady]
      have oldReady :
          state.marks[candidateConclusion]? = some none := by
        have unchanged :=
          fireTensor?_success_mark_of_ne
            candidateConclusionDifferent equation
        rw [unchanged] at nextReady
        exact nextReady
      have candidateNeFired :
          Link.tensor candidateLeft candidateRight candidateConclusion ≠
            Link.tensor left right conclusion := by
        intro same
        cases same
        exact candidateConclusionDifferent rfl
      by_cases created : premise = conclusion
      · subst premise
        rcases fireTensor?_success_conclusion_frontier
            abstractable ordered equation with
          ⟨outputToken, nextComponent, conclusionToken,
            componentLookup, conclusionMembership⟩
        rw [conclusionToken] at nextPremiseToken
        injection nextPremiseToken with tokenEquation
        subst token
        exact
          ⟨nextComponent, componentLookup, conclusionMembership⟩
      · rcases fireTensor?_success_old_tokenAt?_of_ne
            created nextPremiseToken equation with
          ⟨oldToken, oldPremiseToken⟩
        rcases covered linkMembership oldReady premiseMembership
            oldPremiseToken with
          ⟨component, componentLookup, frontierMembership⟩
        have candidatePremise :
            premise ∈
              (Link.tensor candidateLeft candidateRight
                candidateConclusion).premises := by
          simpa [Link.premises] using premiseMembership
        have notLeft : premise ≠ left := by
          intro same
          subst premise
          have sameLink :=
            UnificationState.StructurallyWellFormed.parentLink_unique
              structural linkMembership candidatePremise
                firedMembership (by simp [Link.premises])
          exact candidateNeFired sameLink
        have notRight : premise ≠ right := by
          intro same
          subst premise
          have sameLink :=
            UnificationState.StructurallyWellFormed.parentLink_unique
              structural linkMembership candidatePremise
                firedMembership (by simp [Link.premises])
          exact candidateNeFired sameLink
        rcases fireTensor?_success_frontier_of_ne
            abstractable ordered oldPremiseToken componentLookup
              frontierMembership notLeft notRight equation with
          ⟨transportedToken, nextComponent, transportedMarked,
            nextComponentLookup, transportedMembership⟩
        rw [transportedMarked] at nextPremiseToken
        injection nextPremiseToken with tokenEquation
        subst token
        exact
          ⟨nextComponent, nextComponentLookup,
            transportedMembership⟩

/-- A successful well-typed tensor firing replaces the surviving component
with the exact combined tensor derivation and clears the retired slot, while
preserving formula consistency of every other live component. -/
private theorem fireTensor?_success_componentsFormulaConsistent
    {certificate : Certificate} {state next : UnificationState}
    (consistent :
      state.ComponentsFormulaConsistent certificate)
    {left right conclusion : Vertex}
    (wellFormed :
      certificate.LinkWellFormed (.tensor left right conclusion))
    (equation : fireTensor? state left right conclusion = some next) :
    next.ComponentsFormulaConsistent certificate := by
  unfold fireTensor? at equation
  split at equation
  · contradiction
  · rename_i _ leftToken rightToken unifyEquation
    split at equation
    · contradiction
    · rename_i _ leftComponent leftComponentEquation
      split at equation
      · contradiction
      · rename_i _ rightComponent rightComponentEquation
        split at equation
        · contradiction
        · rename_i _ leftFocus leftContext leftPick
          split at equation
          · contradiction
          · rename_i _ rightFocus rightContext rightPick
            injection equation with stateEquation
            subst next
            have leftConsistent :
                leftComponent.FormulaConsistent certificate :=
              consistent.componentAt leftComponentEquation
            have rightConsistent :
                rightComponent.FormulaConsistent certificate :=
              consistent.componentAt rightComponentEquation
            rcases wellFormed.tensor_formulaData with
              ⟨leftFormula, rightFormula, leftFormulaAt,
                rightFormulaAt, conclusionFormula⟩
            have nextComponentConsistent :
                ({ tree :=
                     .tensor leftFocus rightFocus
                       leftComponent.tree rightComponent.tree
                   frontier :=
                     conclusion :: (leftContext ++ rightContext) } :
                  UnificationComponent).FormulaConsistent certificate :=
              UnificationComponent.FormulaConsistent.tensor
                leftConsistent rightConsistent leftPick rightPick
                  leftFormulaAt rightFormulaAt conclusionFormula
            change
              ({ state with
                components :=
                  (state.components.setIfInBounds
                    (min leftToken rightToken)
                    (some
                      { tree :=
                          .tensor leftFocus rightFocus
                            leftComponent.tree rightComponent.tree
                        frontier :=
                          conclusion ::
                            (leftContext ++ rightContext) }))
                    |>.setIfInBounds
                      (max leftToken rightToken) none } :
                UnificationState).ComponentsFormulaConsistent certificate
            have survivorConsistent :
                ({ state with
                  components :=
                    state.components.setIfInBounds
                      (min leftToken rightToken)
                      (some
                        { tree :=
                            .tensor leftFocus rightFocus
                              leftComponent.tree rightComponent.tree
                          frontier :=
                            conclusion ::
                              (leftContext ++ rightContext) }) } :
                  UnificationState).ComponentsFormulaConsistent
                    certificate :=
              consistent.set
                (index := min leftToken rightToken)
                nextComponentConsistent
            intro index component lookup
            exact
              UnificationState.ComponentsFormulaConsistent.clear
                survivorConsistent (max leftToken rightToken) lookup

/-- Every successful concrete tensor firing preserves the ordered union-find
forest invariant, independently of component construction. -/
private theorem fireTensor?_success_ordered
    {state next : UnificationState}
    (ordered : state.OrderedParents)
    {left right conclusion : Vertex}
    (equation : fireTensor? state left right conclusion = some next) :
    next.OrderedParents := by
  rcases fireTensor?_success_observation equation with
    ⟨leftToken, rightToken, unifyEquation, observation⟩
  have mergedOrdered :
      (state.mergeConclusion conclusion
        (min leftToken rightToken) (max leftToken rightToken))
        |>.OrderedParents :=
    ordered.mergeConclusion conclusion
      (min leftToken rightToken) (max leftToken rightToken)
      (Nat.le_trans (Nat.min_le_left leftToken rightToken)
        (Nat.le_max_left leftToken rightToken))
  have nextOrdered : next.OrderedParents :=
    UnificationState.ObservationEquivalent.orderedParents
      observation mergedOrdered
  intro token parent lookup
  exact nextOrdered lookup

/-- Every successful concrete tensor firing, including component construction,
refines one independent Figure-5 unify step. -/
private theorem fireTensor?_refines_unify
    (certificate : Certificate)
    {state next : UnificationState}
    (abstractable : state.Abstractable certificate)
    (ordered : state.OrderedParents)
    {left right conclusion : Vertex}
    (linkMembership :
      Link.tensor left right conclusion ∈ certificate.links)
    (equation : fireTensor? state left right conclusion = some next) :
    ∃ nextAbstractable : next.Abstractable certificate,
      UnificationStep certificate
        (state.toMarking certificate abstractable)
        (next.toMarking certificate nextAbstractable) := by
  rcases fireTensor?_success_observation equation with
    ⟨leftToken, rightToken, unifyEquation, observation⟩
  rcases state.unifyTokens?_refines abstractable ordered
      linkMembership unifyEquation with
    ⟨mergedAbstractable, mergedStep⟩
  let nextAbstractable :=
    observation.abstractable mergedAbstractable
  refine ⟨nextAbstractable, ?_⟩
  rw [observation.toMarking_eq mergedAbstractable]
  exact mergedStep

/-- Try one connective. `none` means that the link is currently idle, waiting,
already fired, or a binary deadlock; it is not an exception. -/
private def fireConnective? (state : UnificationState) :
    Link → Option UnificationState
  | .axiom _ _ => none
  | .par left right conclusion =>
      firePar? state left right conclusion
  | .tensor left right conclusion =>
      fireTensor? state left right conclusion

/-- Every successful connective firing preserves the ordered parent forest. -/
private theorem fireConnective?_success_ordered
    {state next : UnificationState}
    (ordered : state.OrderedParents)
    {link : Link}
    (equation : fireConnective? state link = some next) :
    next.OrderedParents := by
  cases link with
  | «axiom» left right =>
      simp [fireConnective?] at equation
  | «par» left right conclusion =>
      exact firePar?_success_ordered ordered equation
  | «tensor» left right conclusion =>
      exact fireTensor?_success_ordered ordered equation

/-- Every successful well-typed connective firing preserves the partial
derivation formula invariant. -/
private theorem fireConnective?_success_componentsFormulaConsistent
    {certificate : Certificate} {state next : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (consistent :
      state.ComponentsFormulaConsistent certificate)
    {link : Link}
    (linkMembership : link ∈ certificate.links)
    (equation : fireConnective? state link = some next) :
    next.ComponentsFormulaConsistent certificate := by
  have wellFormed : certificate.LinkWellFormed link :=
    structural.2.2.2.2.1 link linkMembership
  cases link with
  | «axiom» left right =>
      simp [fireConnective?] at equation
  | «par» left right conclusion =>
      intro index component lookup
      exact firePar?_success_componentsFormulaConsistent
        consistent wellFormed equation lookup
  | «tensor» left right conclusion =>
      intro index component lookup
      exact fireTensor?_success_componentsFormulaConsistent
        consistent wellFormed equation lookup

/-- Any successful real connective firing preserves abstraction and refines
the corresponding independent Figure-5 transition. -/
private theorem fireConnective?_refines
    (certificate : Certificate)
    {state next : UnificationState}
    (abstractable : state.Abstractable certificate)
    (ordered : state.OrderedParents)
    {link : Link}
    (linkMembership : link ∈ certificate.links)
    (equation : fireConnective? state link = some next) :
    ∃ nextAbstractable : next.Abstractable certificate,
      UnificationStep certificate
        (state.toMarking certificate abstractable)
        (next.toMarking certificate nextAbstractable) := by
  cases link with
  | «axiom» left right =>
      simp [fireConnective?] at equation
  | «par» left right conclusion =>
      exact firePar?_refines_forward certificate abstractable
        linkMembership equation
  | «tensor» left right conclusion =>
      exact fireTensor?_refines_unify certificate abstractable ordered
        linkMembership equation

/-- One fold update for a deterministic connective pass. -/
private def unificationFoldStep
    (current : UnificationState × Nat) (link : Link) :
    UnificationState × Nat :=
  match fireConnective? current.1 link with
  | none => current
  | some next => (next, current.2 + 1)

/-- One deterministic left-to-right pass over all connective links. -/
private def unificationPass (links : List Link)
    (initial : UnificationState) : UnificationState × Nat :=
  links.foldl unificationFoldStep (initial, 0)

/-- The ordered parent forest is invariant under a whole eager connective
pass, for any incoming progress counter. -/
private theorem unificationFold_ordered
    (links : List Link) {state : UnificationState} (progress : Nat)
    (ordered : state.OrderedParents) :
    ((links.foldl unificationFoldStep
      (state, progress)).1).OrderedParents := by
  induction links generalizing state progress with
  | nil =>
      exact ordered
  | cons link links induction =>
      simp only [List.foldl_cons]
      cases fireEquation : fireConnective? state link with
      | none =>
          have stepEquation :
              unificationFoldStep (state, progress) link =
                (state, progress) := by
            simp [unificationFoldStep, fireEquation]
          rw [stepEquation]
          have result :
              ((links.foldl unificationFoldStep
                (state, progress)).1).OrderedParents :=
            induction progress ordered
          intro token parent lookup
          exact result lookup
      | some fired =>
          have stepEquation :
              unificationFoldStep (state, progress) link =
                (fired, progress + 1) := by
            simp [unificationFoldStep, fireEquation]
          rw [stepEquation]
          have firedOrdered : fired.OrderedParents :=
            fireConnective?_success_ordered ordered fireEquation
          have result :
              ((links.foldl unificationFoldStep
                (fired, progress + 1)).1).OrderedParents :=
            induction (progress + 1) firedOrdered
          intro token parent lookup
          exact result lookup

/-- A left-to-right executable fold preserves formula consistency of all live
partial derivation components. -/
private theorem unificationFold_componentsFormulaConsistent
    (certificate : Certificate)
    (structural : certificate.StructurallyWellFormed)
    (links : List Link)
    {state : UnificationState}
    (progress : Nat)
    (consistent :
      state.ComponentsFormulaConsistent certificate)
    (submitted :
      ∀ link, link ∈ links → link ∈ certificate.links) :
    ((links.foldl unificationFoldStep
      (state, progress)).1).ComponentsFormulaConsistent certificate := by
  induction links generalizing state progress with
  | nil =>
      exact consistent
  | cons link links induction =>
      have linkSubmitted : link ∈ certificate.links :=
        submitted link (by simp)
      have tailSubmitted :
          ∀ candidate, candidate ∈ links →
            candidate ∈ certificate.links := by
        intro candidate membership
        exact submitted candidate (by simp [membership])
      simp only [List.foldl_cons]
      cases fireEquation : fireConnective? state link with
      | none =>
          have stepEquation :
              unificationFoldStep (state, progress) link =
                (state, progress) := by
            simp [unificationFoldStep, fireEquation]
          rw [stepEquation]
          intro index component lookup
          exact induction progress consistent tailSubmitted lookup
      | some fired =>
          have stepEquation :
              unificationFoldStep (state, progress) link =
                (fired, progress + 1) := by
            simp [unificationFoldStep, fireEquation]
          rw [stepEquation]
          have firedConsistent :
              fired.ComponentsFormulaConsistent certificate :=
            fireConnective?_success_componentsFormulaConsistent
              structural consistent linkSubmitted fireEquation
          intro index component lookup
          exact induction (progress + 1) firedConsistent
            tailSubmitted lookup

/-- A left-to-right executable fold preserves abstraction and is simulated by
a finite execution of the independent Figure-5 semantics. Idle links
contribute reflexive steps; every successful firing contributes exactly one
semantic transition. -/
private theorem unificationFold_refines
    (certificate : Certificate)
    (links : List Link)
    {state : UnificationState}
    (progress : Nat)
    (abstractable : state.Abstractable certificate)
    (ordered : state.OrderedParents)
    (submitted :
      ∀ link, link ∈ links → link ∈ certificate.links) :
    ∃ finalAbstractable :
        ((links.foldl unificationFoldStep
          (state, progress)).1).Abstractable certificate,
      UnificationExecution certificate
        (state.toMarking certificate abstractable)
        (((links.foldl unificationFoldStep
          (state, progress)).1).toMarking
            certificate finalAbstractable) := by
  induction links generalizing state progress with
  | nil =>
      exact ⟨abstractable, .refl _⟩
  | cons link links induction =>
      have linkSubmitted : link ∈ certificate.links :=
        submitted link (by simp)
      have tailSubmitted :
          ∀ candidate, candidate ∈ links →
            candidate ∈ certificate.links := by
        intro candidate membership
        exact submitted candidate (by simp [membership])
      simp only [List.foldl_cons]
      cases fireEquation : fireConnective? state link with
      | none =>
          have stepEquation :
              unificationFoldStep (state, progress) link =
                (state, progress) := by
            simp [unificationFoldStep, fireEquation]
          have result :=
            induction progress abstractable ordered tailSubmitted
          simpa only [stepEquation] using result
      | some fired =>
          have stepEquation :
              unificationFoldStep (state, progress) link =
                (fired, progress + 1) := by
            simp [unificationFoldStep, fireEquation]
          rcases fireConnective?_refines certificate abstractable ordered
              linkSubmitted fireEquation with
            ⟨firedAbstractable, transition⟩
          have firedOrdered : fired.OrderedParents :=
            fireConnective?_success_ordered ordered fireEquation
          rcases induction (progress + 1) firedAbstractable
              firedOrdered tailSubmitted with
            ⟨finalAbstractable, rest⟩
          have result :
              ∃ completedAbstractable :
                  ((links.foldl unificationFoldStep
                    (fired, progress + 1)).1).Abstractable certificate,
                UnificationExecution certificate
                  (state.toMarking certificate abstractable)
                  (((links.foldl unificationFoldStep
                    (fired, progress + 1)).1).toMarking
                      certificate completedAbstractable) :=
            ⟨finalAbstractable,
              UnificationExecution.step transition rest⟩
          simpa only [stepEquation] using result

/-- A deterministic eager pass preserves the ordered parent forest. -/
private theorem unificationPass_ordered
    (links : List Link) {state : UnificationState}
    (ordered : state.OrderedParents) :
    (unificationPass links state).1.OrderedParents := by
  exact unificationFold_ordered links 0 ordered

/-- One complete eager pass over submitted links preserves every live partial
derivation's formula frontier. -/
private theorem unificationPass_componentsFormulaConsistent
    (certificate : Certificate)
    (structural : certificate.StructurallyWellFormed)
    {state : UnificationState}
    (consistent :
      state.ComponentsFormulaConsistent certificate) :
    (unificationPass certificate.links state).1
      |>.ComponentsFormulaConsistent certificate := by
  exact unificationFold_componentsFormulaConsistent certificate structural
    certificate.links 0 consistent (fun _ membership => membership)

/-- One complete eager pass over the submitted certificate links is simulated
by a finite independent Figure-5 execution. -/
private theorem unificationPass_refines
    (certificate : Certificate)
    {state : UnificationState}
    (abstractable : state.Abstractable certificate)
    (ordered : state.OrderedParents) :
    ∃ finalAbstractable :
        (unificationPass certificate.links state).1.Abstractable certificate,
      UnificationExecution certificate
        (state.toMarking certificate abstractable)
        ((unificationPass certificate.links state).1.toMarking
          certificate finalAbstractable) := by
  exact unificationFold_refines certificate certificate.links 0
    abstractable ordered (fun _ membership => membership)

private structure UnificationSaturationResult where
  state : UnificationState
  stats : UnificationScanStats

/-- Repeat deterministic passes until saturation. Every successful firing marks
a fresh connective conclusion, so `links.length` passes are sufficient. -/
private def saturateUnification (links : List Link) :
    Nat → UnificationState → UnificationSaturationResult
  | 0, state =>
      { state
        stats :=
          { passes := 0
            linkVisits := 0
            successfulFirings := 0 } }
  | fuel + 1, state =>
      let (next, progress) := unificationPass links state
      if progress == 0 then
        { state := next
          stats :=
            { passes := 1
              linkVisits := links.length
              successfulFirings := 0 } }
      else
        let saturated := saturateUnification links fuel next
        { state := saturated.state
          stats :=
            { passes := saturated.stats.passes + 1
              linkVisits := saturated.stats.linkVisits + links.length
              successfulFirings :=
                saturated.stats.successfulFirings + progress } }

private theorem saturateUnification_stats (links : List Link)
    (fuel : Nat) (state : UnificationState) :
    let result := saturateUnification links fuel state
    result.stats.passes ≤ fuel ∧
      result.stats.linkVisits = result.stats.passes * links.length := by
  induction fuel generalizing state with
  | zero =>
      simp [saturateUnification]
  | succ fuel induction =>
      simp only [saturateUnification]
      split
      · simp
      · simp only
        have tail := induction (unificationPass links state).1
        constructor
        · omega
        · rw [tail.2]
          simp [Nat.add_mul]

/-- Every eager saturation prefix preserves the ordered parent forest. -/
private theorem saturateUnification_ordered
    (links : List Link) (fuel : Nat)
    {state : UnificationState}
    (ordered : state.OrderedParents) :
    (saturateUnification links fuel state).state.OrderedParents := by
  induction fuel generalizing state with
  | zero =>
      exact ordered
  | succ fuel induction =>
      simp only [saturateUnification]
      have nextOrdered :
          (unificationPass links state).1.OrderedParents :=
        unificationPass_ordered links ordered
      split
      · intro token parent lookup
        exact nextOrdered lookup
      · have saturatedOrdered :
            (saturateUnification links fuel
              (unificationPass links state).1).state.OrderedParents :=
          induction nextOrdered
        intro token parent lookup
        exact saturatedOrdered lookup

/-- Every finite eager-saturation prefix preserves formula consistency of all
live partial derivation components. -/
private theorem saturateUnification_componentsFormulaConsistent
    (certificate : Certificate)
    (structural : certificate.StructurallyWellFormed)
    (fuel : Nat)
    {state : UnificationState}
    (consistent :
      state.ComponentsFormulaConsistent certificate) :
    (saturateUnification certificate.links fuel state).state
      |>.ComponentsFormulaConsistent certificate := by
  induction fuel generalizing state with
  | zero =>
      exact consistent
  | succ fuel induction =>
      simp only [saturateUnification]
      have nextConsistent :
          (unificationPass certificate.links state).1
            |>.ComponentsFormulaConsistent certificate :=
        unificationPass_componentsFormulaConsistent
          certificate structural consistent
      split
      · intro index component lookup
        exact nextConsistent lookup
      · have saturatedConsistent :
            (saturateUnification certificate.links fuel
              (unificationPass certificate.links state).1).state
              |>.ComponentsFormulaConsistent certificate :=
          induction nextConsistent
        intro index component lookup
        exact saturatedConsistent lookup

/-- Every finite eager-saturation prefix preserves abstraction and is
simulated by a finite execution of the independent Figure-5 semantics. -/
private theorem saturateUnification_refines
    (certificate : Certificate)
    (fuel : Nat)
    {state : UnificationState}
    (abstractable : state.Abstractable certificate)
    (ordered : state.OrderedParents) :
    ∃ finalAbstractable :
        (saturateUnification certificate.links fuel state).state
          |>.Abstractable certificate,
      UnificationExecution certificate
        (state.toMarking certificate abstractable)
        ((saturateUnification certificate.links fuel state).state.toMarking
          certificate finalAbstractable) := by
  induction fuel generalizing state with
  | zero =>
      exact ⟨abstractable, .refl _⟩
  | succ fuel induction =>
      simp only [saturateUnification]
      rcases unificationPass_refines certificate abstractable ordered with
        ⟨nextAbstractable, passExecution⟩
      have nextOrdered :
          (unificationPass certificate.links state).1.OrderedParents :=
        unificationPass_ordered certificate.links ordered
      split
      · exact ⟨nextAbstractable, passExecution⟩
      · rcases induction nextAbstractable nextOrdered with
          ⟨finalAbstractable, tailExecution⟩
        exact ⟨finalAbstractable,
          passExecution.trans tailExecution⟩

/-- The complete eager token-semantic run, from the empty initial state through
all axiom starts and the bounded saturation phase, is simulated by one finite
execution of the independent Figure-5 semantics whenever initialization
succeeds. -/
private theorem eagerUnification_refines
    (certificate : Certificate)
    {started : UnificationState}
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    ∃ finalAbstractable :
        (saturateUnification certificate.links certificate.links.length
          started).state.Abstractable certificate,
      UnificationExecution certificate
        (certificate.initialUnificationState.toMarking certificate
          (initialUnificationState_abstractable certificate))
        ((saturateUnification certificate.links certificate.links.length
          started).state.toMarking certificate finalAbstractable) := by
  rcases certificate.startAxioms?_success_refines
      (initialUnificationState_abstractable certificate)
      (initialUnificationState_identityParents certificate)
      (fun _ membership => membership) startEquation with
    ⟨startedAbstractable, startedIdentity, startExecution⟩
  have startedOrdered : started.OrderedParents :=
    startedIdentity.orderedParents
  rcases saturateUnification_refines certificate certificate.links.length
      startedAbstractable startedOrdered with
    ⟨finalAbstractable, saturationExecution⟩
  exact ⟨finalAbstractable,
    startExecution.trans saturationExecution⟩

/-- On structurally well-formed input, the complete successful eager run keeps
every stored live component equal, at the formula level, to the sequent
inferred by its partial cut-free derivation. -/
private theorem eagerUnification_componentsFormulaConsistent
    (certificate : Certificate)
    (structural : certificate.StructurallyWellFormed)
    {started : UnificationState}
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    (saturateUnification certificate.links certificate.links.length
      started).state.ComponentsFormulaConsistent certificate := by
  have startedConsistent :
      started.ComponentsFormulaConsistent certificate :=
    certificate.startAxioms?_success_componentsFormulaConsistent
      structural
      (initialUnificationState_componentsFormulaConsistent certificate)
      (fun _ membership => membership) startEquation
  intro index component lookup
  exact saturateUnification_componentsFormulaConsistent
    certificate structural certificate.links.length startedConsistent lookup

private inductive WorklistEnqueueKind where
  | initial
  | dependency
  | waiting

/-- Cumulative count of all successful concrete queue insertions, separated
by their operational causes in the public statistics record. -/
private def totalWorklistEnqueues
    (stats : UnificationWorklistStats) : Nat :=
  stats.initialEnqueues +
    stats.dependencyEnqueues +
      stats.waitingRequeues

private structure UnificationWorklistState where
  core : UnificationState
  queue : List Nat
  queued : Array Bool
  waiting : List Nat
  waitingFlags : Array Bool
  stats : UnificationWorklistStats

/-- A connective link is fired in a core state exactly when its conclusion
has a raw token. Axioms are started before the worklist and are deliberately
excluded from this scheduler history. -/
private def linkFiredIn (state : UnificationState) : Link → Prop
  | .axiom _ _ => False
  | .par _ _ conclusion
  | .tensor _ _ conclusion =>
      state.assignedToken? conclusion ≠ none

/-- Proof-only event history tying the operational successful-firing counter
to distinct submitted connective links whose conclusions are marked. -/
private def WorklistFiringsAccounted
    (certificate : Certificate)
    (state : UnificationWorklistState) : Prop :=
  ∃ history : List Link,
    history.Nodup ∧
      (∀ link ∈ history, link ∈ certificate.links) ∧
        (∀ link ∈ history, linkFiredIn state.core link) ∧
          history.length = state.stats.successfulFirings

/-- Cumulative dependency insertion and waiting-requeue sources are charged to
successful connective firings. A dependency event costs at most one insertion;
a tensor event can requeue at most the submitted-link carrier. -/
private def WorklistEnqueueSourcesBounded
    (certificate : Certificate)
    (state : UnificationWorklistState) : Prop :=
  state.stats.dependencyEnqueues ≤ state.stats.successfulFirings ∧
    state.stats.waitingRequeues ≤
      certificate.links.length * state.stats.successfulFirings

/-- Scheduler-only changes preserve a firing history when they leave the core
and successful-firing counter unchanged. -/
private theorem WorklistFiringsAccounted.transport
    {certificate : Certificate}
    {before after : UnificationWorklistState}
    (accounted : WorklistFiringsAccounted certificate before)
    (core : after.core = before.core)
    (counter :
      after.stats.successfulFirings =
        before.stats.successfulFirings) :
    WorklistFiringsAccounted certificate after := by
  rcases accounted with
    ⟨history, historyNodup, historySubmitted,
      historyFired, countExact⟩
  exact
    ⟨history, historyNodup, historySubmitted, by
      intro link membership
      simpa [core] using historyFired link membership, by
        simpa [counter] using countExact⟩

/-- Exact cumulative-enqueue/queue conservation between two scheduler
states. -/
private def QueueInsertionBalanced
    (before after : UnificationWorklistState) : Prop :=
  totalWorklistEnqueues after.stats + before.queue.length =
    totalWorklistEnqueues before.stats + after.queue.length

/-- Queue insertion conservation composes transitively. -/
private theorem QueueInsertionBalanced.trans
    {first middle last : UnificationWorklistState}
    (firstMiddle : QueueInsertionBalanced first middle)
    (middleLast : QueueInsertionBalanced middle last) :
    QueueInsertionBalanced first last := by
  unfold QueueInsertionBalanced at firstMiddle middleLast ⊢
  omega

/-- Scheduler-side classification used to state that no connective which is
ready in the current token partition has been silently lost.  The `queued`
case is intentionally operational: membership in the actual queue, rather
than a Boolean summary flag, is what guarantees a future attempt. -/
private inductive ConnectiveSchedulerStatus
    (state : UnificationWorklistState) (index : Nat) : Link → Prop
  | queued {link : Link} (membership : index ∈ state.queue) :
      ConnectiveSchedulerStatus state index link
  | firedPar {left right conclusion : Vertex}
      (marked : state.core.assignedToken? conclusion ≠ none) :
      ConnectiveSchedulerStatus state index (.par left right conclusion)
  | firedTensor {left right conclusion : Vertex}
      (marked : state.core.assignedToken? conclusion ≠ none) :
      ConnectiveSchedulerStatus state index (.tensor left right conclusion)
  | idlePar {left right conclusion : Vertex}
      (idle :
        state.core.tokenAt? left = none ∨
          state.core.tokenAt? right = none) :
      ConnectiveSchedulerStatus state index (.par left right conclusion)
  | idleTensor {left right conclusion : Vertex}
      (idle :
        state.core.tokenAt? left = none ∨
          state.core.tokenAt? right = none) :
      ConnectiveSchedulerStatus state index (.tensor left right conclusion)
  | waitingPar {left right conclusion : Vertex}
      {leftToken rightToken : Nat}
      (leftMarked : state.core.tokenAt? left = some leftToken)
      (rightMarked : state.core.tokenAt? right = some rightToken)
      (different : leftToken ≠ rightToken)
      (registered : index ∈ state.waiting)
      (bound : index < state.queued.size) :
      ConnectiveSchedulerStatus state index (.par left right conclusion)
  | tensorDeadlock {left right conclusion : Vertex} {token : Nat}
      (leftMarked : state.core.tokenAt? left = some token)
      (rightMarked : state.core.tokenAt? right = some token) :
      ConnectiveSchedulerStatus state index (.tensor left right conclusion)

/-- Every submitted connective has an operational or token-semantic reason
for not being missed by the scheduler.  In particular, a ready par or tensor
which is neither fired, idle, waiting, nor a tensor deadlock must occur in the
real work queue. -/
private def SchedulerCoverage (certificate : Certificate)
    (state : UnificationWorklistState) : Prop :=
  ∀ {index : Nat} {link : Link},
    certificate.links[index]? = some link →
      link.isConnective = true →
        ConnectiveSchedulerStatus state index link

/-- Scheduler coverage with one distinguished queue head temporarily exempt.
Popping removes that head's operational `queued` witness before processing;
all other connective classifications must remain available during the atomic
pop-and-process proof. -/
private def SchedulerCoverageExcept (certificate : Certificate)
    (state : UnificationWorklistState) (skipped : Nat) : Prop :=
  ∀ {index : Nat} {link : Link},
    certificate.links[index]? = some link →
      link.isConnective = true →
        index ≠ skipped →
          ConnectiveSchedulerStatus state index link

/-- The exact semantic reasons why an unfired connective can remain after a
covered scheduler becomes quiescent. -/
private def QuiescentConnectiveObstruction
    (state : UnificationWorklistState) (index : Nat) : Link → Prop
  | .axiom _ _ => False
  | .par left right conclusion =>
      state.core.assignedToken? conclusion = none ∧
        ((state.core.tokenAt? left = none ∨
            state.core.tokenAt? right = none) ∨
          ∃ leftToken rightToken,
            state.core.tokenAt? left = some leftToken ∧
              state.core.tokenAt? right = some rightToken ∧
                leftToken ≠ rightToken ∧
                  index ∈ state.waiting)
  | .tensor left right conclusion =>
      state.core.assignedToken? conclusion = none ∧
        ((state.core.tokenAt? left = none ∨
            state.core.tokenAt? right = none) ∨
          ∃ token,
            state.core.tokenAt? left = some token ∧
              state.core.tokenAt? right = some token)

/-- The two genuinely thread-level quiescent obstructions left after choosing
a minimum-complexity unmarked conclusion.  Idle premises have disappeared:
a par is blocked by distinct live threads, while a tensor is blocked by one
shared live thread. -/
private def QuiescentThreadObstruction
    (state : UnificationWorklistState) (index : Nat) : Link → Prop
  | .axiom _ _ => False
  | .par left right conclusion =>
      state.core.assignedToken? conclusion = none ∧
        ∃ leftToken rightToken,
          state.core.tokenAt? left = some leftToken ∧
            state.core.tokenAt? right = some rightToken ∧
              leftToken ≠ rightToken ∧
                index ∈ state.waiting
  | .tensor left right conclusion =>
      state.core.assignedToken? conclusion = none ∧
        ∃ token,
          state.core.tokenAt? left = some token ∧
            state.core.tokenAt? right = some token

/-- Once the concrete queue is empty, scheduler coverage turns every
submitted but unfired connective into an explicit semantic obstruction.
For a par this is either a missing premise or two distinct registered
threads; for a tensor it is either a missing premise or a same-thread
deadlock.  This theorem is deliberately correctness-free: the next layer must
use proof-net correctness to rule these witnesses out. -/
private theorem SchedulerCoverage.quiescent_unfired_obstruction
    {certificate : Certificate} {state : UnificationWorklistState}
    {index : Nat} {link : Link}
    (coverage : SchedulerCoverage certificate state)
    (quiescent : state.queue = [])
    (lookup : certificate.links[index]? = some link)
    (connective : link.isConnective = true)
    (unfired : ¬linkFiredIn state.core link) :
    QuiescentConnectiveObstruction state index link := by
  have status := coverage lookup connective
  cases link with
  | «axiom» left right =>
      simp [Link.isConnective] at connective
  | «par» left right conclusion =>
      have conclusionUnmarked :
          state.core.assignedToken? conclusion = none := by
        simpa [linkFiredIn] using unfired
      refine ⟨conclusionUnmarked, ?_⟩
      cases status with
      | queued membership =>
          simp [quiescent] at membership
      | firedPar marked =>
          exact False.elim (marked conclusionUnmarked)
      | idlePar idle =>
          exact Or.inl idle
      | waitingPar leftMarked rightMarked different registered bound =>
          exact Or.inr
            ⟨_, _, leftMarked, rightMarked, different, registered⟩
  | tensor left right conclusion =>
      have conclusionUnmarked :
          state.core.assignedToken? conclusion = none := by
        simpa [linkFiredIn] using unfired
      refine ⟨conclusionUnmarked, ?_⟩
      cases status with
      | queued membership =>
          simp [quiescent] at membership
      | firedTensor marked =>
          exact False.elim (marked conclusionUnmarked)
      | idleTensor idle =>
          exact Or.inl idle
      | tensorDeadlock leftMarked rightMarked =>
          exact Or.inr ⟨_, leftMarked, rightMarked⟩

/-- A `true` deduplication flag must be backed by membership in the actual
queue.  The reverse direction and queue uniqueness belong to the later fuel
accounting layer; this direction is enough to justify every deduplicated
enqueue as non-lossy. -/
private def QueueFlagSound (state : UnificationWorklistState) : Prop :=
  ∀ {index : Nat}, state.queued[index]? = some true →
    index ∈ state.queue

/-- Every real queue member owns a `true` deduplication flag. Together with
`QueueFlagSound`, this makes the array an exact characteristic function of
the concrete queue. -/
private def QueueFlagComplete (state : UnificationWorklistState) : Prop :=
  ∀ {index : Nat}, index ∈ state.queue →
    state.queued[index]? = some true

/-- The concrete queue has no duplicate link indices. -/
private def QueueNodup (state : UnificationWorklistState) : Prop :=
  state.queue.Nodup

/-- Every real queue member addresses a valid deduplication-flag slot. -/
private def QueueBounded (state : UnificationWorklistState) : Prop :=
  ∀ {index : Nat}, index ∈ state.queue →
    index < state.queued.size

/-- A `true` waiting flag must be backed by membership in the actual
waiting-par registry. -/
private def WaitingFlagSound (state : UnificationWorklistState) : Prop :=
  ∀ {index : Nat}, state.waitingFlags[index]? = some true →
    index ∈ state.waiting

/-- Every registered waiting par owns a `true` waiting flag. -/
private def WaitingFlagComplete (state : UnificationWorklistState) : Prop :=
  ∀ {index : Nat}, index ∈ state.waiting →
    state.waitingFlags[index]? = some true

/-- The waiting-par registry has no duplicate link indices. -/
private def WaitingNodup (state : UnificationWorklistState) : Prop :=
  state.waiting.Nodup

/-- Every waiting-par registry member addresses a valid flag slot. -/
private def WaitingBounded (state : UnificationWorklistState) : Prop :=
  ∀ {index : Nat}, index ∈ state.waiting →
    index < state.waitingFlags.size

/-- A duplicate-free finite registry contained in a finite ambient list
cannot be longer than that ambient carrier. -/
private theorem worklist_length_le_of_nodup_subset
    {α : Type} [BEq α] [LawfulBEq α]
    {values ambient : List α} (nodup : values.Nodup)
    (subset : ∀ value ∈ values, value ∈ ambient) :
    values.length ≤ ambient.length := by
  induction values generalizing ambient with
  | nil =>
      simp
  | cons head tail induction =>
      have headMembership : head ∈ ambient :=
        subset head (by simp)
      have tailSubset :
          ∀ value ∈ tail, value ∈ ambient.erase head := by
        intro value membership
        have valueMembership : value ∈ ambient :=
          subset value (by simp [membership])
        have different : value ≠ head := by
          intro same
          subst value
          exact (List.nodup_cons.mp nodup).1 membership
        exact (List.mem_erase_of_ne different).2 valueMembership
      have tailBound :=
        induction (List.nodup_cons.mp nodup).2 tailSubset
      rw [List.length_erase_of_mem headMembership] at tailBound
      have positive : 0 < ambient.length :=
        List.length_pos_of_mem headMembership
      simp only [List.length_cons]
      omega

/-- An accounted firing history cannot be longer than the submitted-link
carrier. -/
private theorem WorklistFiringsAccounted.successfulFirings_le
    {certificate : Certificate} {state : UnificationWorklistState}
    (accounted : WorklistFiringsAccounted certificate state) :
    state.stats.successfulFirings ≤ certificate.links.length := by
  rcases accounted with
    ⟨history, historyNodup, historySubmitted,
      _historyFired, countExact⟩
  rw [← countExact]
  exact worklist_length_le_of_nodup_subset
    historyNodup historySubmitted

/-- Exact queue flags imply ordinary queue bounds. -/
private theorem QueueFlagComplete.queueBounded
    {state : UnificationWorklistState}
    (complete : QueueFlagComplete state) :
    QueueBounded state := by
  intro index membership
  exact (Array.getElem?_eq_some_iff.mp
    (complete membership)).1

/-- Exact waiting flags imply ordinary waiting-registry bounds. -/
private theorem WaitingFlagComplete.waitingBounded
    {state : UnificationWorklistState}
    (complete : WaitingFlagComplete state) :
    WaitingBounded state := by
  intro index membership
  exact (Array.getElem?_eq_some_iff.mp
    (complete membership)).1

/-- Exact queue flags and uniqueness bound the concrete queue by its flag
carrier. -/
private theorem QueueNodup.length_le_queuedSize
    {state : UnificationWorklistState}
    (nodup : QueueNodup state)
    (complete : QueueFlagComplete state) :
    state.queue.length ≤ state.queued.size := by
  have subset :
      ∀ index ∈ state.queue,
        index ∈ List.range state.queued.size := by
    intro index membership
    exact List.mem_range.mpr (complete.queueBounded membership)
  have bound :=
    worklist_length_le_of_nodup_subset nodup subset
  simpa using bound

/-- Exact waiting flags and uniqueness bound the concrete waiting registry by
its flag carrier. -/
private theorem WaitingNodup.length_le_waitingFlagsSize
    {state : UnificationWorklistState}
    (nodup : WaitingNodup state)
    (complete : WaitingFlagComplete state) :
    state.waiting.length ≤ state.waitingFlags.size := by
  have subset :
      ∀ index ∈ state.waiting,
        index ∈ List.range state.waitingFlags.size := by
    intro index membership
    exact List.mem_range.mpr (complete.waitingBounded membership)
  have bound :=
    worklist_length_le_of_nodup_subset nodup subset
  simpa using bound

/-- A link index denotes one of the submitted binary connectives rather than
an axiom or an out-of-range number. -/
private def SubmittedConnective (certificate : Certificate)
    (index : Nat) : Prop :=
  ∃ link,
    certificate.links[index]? = some link ∧
    link.isConnective = true

/-- Every concrete work-queue entry originates from a submitted connective.
This is deliberately stronger than mere array bounds: it rules out both axiom
indices and fabricated in-range indices. -/
private def QueueConnectiveSound (certificate : Certificate)
    (state : UnificationWorklistState) : Prop :=
  ∀ {index : Nat}, index ∈ state.queue →
    SubmittedConnective certificate index

/-- The waiting registry contains only submitted par links.  Tensor firing
requeues precisely this registry, so retaining the stronger constructor fact
keeps queue provenance compositional. -/
private def WaitingParSound (certificate : Certificate)
    (state : UnificationWorklistState) : Prop :=
  ∀ {index : Nat}, index ∈ state.waiting →
    ∃ left right conclusion,
      certificate.links[index]? =
        some (.par left right conclusion)

private def pushConsumer (consumers : Array (List Nat))
    (vertex linkIndex : Nat) : Array (List Nat) :=
  match consumers[vertex]? with
  | none => consumers
  | some indices =>
      consumers.setIfInBounds vertex (linkIndex :: indices)

/-- Consumer insertion never changes the table carrier. -/
@[simp] private theorem pushConsumer_size
    (consumers : Array (List Nat)) (vertex linkIndex : Nat) :
    (pushConsumer consumers vertex linkIndex).size = consumers.size := by
  unfold pushConsumer
  split <;> simp

/-- Add both premise dependencies of one indexed connective. -/
private def addLinkConsumers (consumers : Array (List Nat))
    (entry : Link × Nat) : Array (List Nat) :=
  match entry with
  | (.axiom _ _, _) => consumers
  | (.par left right _, linkIndex)
  | (.tensor left right _, linkIndex) =>
      let withLeft := pushConsumer consumers left linkIndex
      pushConsumer withLeft right linkIndex

/-- Adding one indexed link preserves the consumer-table carrier. -/
@[simp] private theorem addLinkConsumers_size
    (consumers : Array (List Nat)) (entry : Link × Nat) :
    (addLinkConsumers consumers entry).size = consumers.size := by
  rcases entry with ⟨link, linkIndex⟩
  cases link <;> simp [addLinkConsumers]

/-- Precompute the links that can become newly armed when a formula occurrence
is marked. Structural well-formedness ensures resource-linear use, but this
builder also fails closed on out-of-range vertices. -/
private def worklistConsumers (certificate : Certificate) :
    Array (List Nat) :=
  certificate.links.zipIdx.foldl addLinkConsumers
    (Array.replicate certificate.formulas.size [])

/-- Adding one in-bounds consumer places its index in the addressed bucket. -/
private theorem mem_pushConsumer_self
    {consumers : Array (List Nat)} {vertex linkIndex : Nat}
    (bound : vertex < consumers.size) :
    linkIndex ∈
      ((pushConsumer consumers vertex linkIndex)[vertex]?).getD [] := by
  simp [pushConsumer, bound]

/-- Adding a consumer never removes an existing dependency from any bucket. -/
private theorem mem_pushConsumer_of_mem
    {consumers : Array (List Nat)} {vertex linkIndex : Nat}
    {premise existingIndex : Nat}
    (membership :
      existingIndex ∈ (consumers[premise]?).getD []) :
    existingIndex ∈
      ((pushConsumer consumers vertex linkIndex)[premise]?).getD [] := by
  by_cases vertexBound : vertex < consumers.size
  · by_cases same : vertex = premise
    · subst premise
      have oldMembership :
          existingIndex ∈ consumers[vertex] := by
        rw [Array.getElem?_eq_getElem vertexBound] at membership
        simpa using membership
      simpa [pushConsumer, vertexBound] using
        List.mem_cons_of_mem linkIndex oldMembership
    · simpa [pushConsumer, vertexBound, same] using membership
  · have lookupNone : consumers[vertex]? = none :=
      Array.getElem?_eq_none (Nat.le_of_not_gt vertexBound)
    simpa [pushConsumer, lookupNone] using membership

/-- Every dependency found after one bucket update was either the newly
inserted link index or was already present before the update. -/
private theorem mem_pushConsumer_origin
    {consumers : Array (List Nat)} {vertex linkIndex : Nat}
    {premise candidate : Nat}
    (membership :
      candidate ∈
        ((pushConsumer consumers vertex linkIndex)[premise]?).getD []) :
    (candidate = linkIndex ∧ premise = vertex) ∨
      candidate ∈ (consumers[premise]?).getD [] := by
  by_cases vertexBound : vertex < consumers.size
  · by_cases same : vertex = premise
    · subst premise
      have inserted :
          candidate = linkIndex ∨
            candidate ∈ consumers[vertex] := by
        simpa [pushConsumer, vertexBound] using membership
      rcases inserted with inserted | old
      · exact Or.inl ⟨inserted, rfl⟩
      · apply Or.inr
        rw [Array.getElem?_eq_getElem vertexBound]
        simpa using old
    · apply Or.inr
      simpa [pushConsumer, vertexBound, same] using membership
  · have lookupNone : consumers[vertex]? = none :=
      Array.getElem?_eq_none (Nat.le_of_not_gt vertexBound)
    apply Or.inr
    simpa [pushConsumer, lookupNone] using membership

/-- One indexed connective update preserves every dependency already stored. -/
private theorem mem_addLinkConsumers_of_mem
    {consumers : Array (List Nat)} {entry : Link × Nat}
    {premise existingIndex : Nat}
    (membership :
      existingIndex ∈ (consumers[premise]?).getD []) :
    existingIndex ∈
      ((addLinkConsumers consumers entry)[premise]?).getD [] := by
  rcases entry with ⟨link, linkIndex⟩
  cases link with
  | «axiom» left right =>
      exact membership
  | «par» left right conclusion =>
      exact mem_pushConsumer_of_mem
        (mem_pushConsumer_of_mem membership)
  | «tensor» left right conclusion =>
      exact mem_pushConsumer_of_mem
        (mem_pushConsumer_of_mem membership)

/-- Every dependency introduced by one indexed-link update names that exact
submitted connective; all other dependencies were already present. -/
private theorem mem_addLinkConsumers_origin
    {consumers : Array (List Nat)} {link : Link} {linkIndex : Nat}
    {premise candidate : Nat}
    (membership :
      candidate ∈
        ((addLinkConsumers consumers (link, linkIndex))[premise]?).getD []) :
    (candidate = linkIndex ∧ link.isConnective = true ∧
      premise ∈ link.premises) ∨
      candidate ∈ (consumers[premise]?).getD [] := by
  cases link with
  | «axiom» left right =>
      exact Or.inr membership
  | «par» left right conclusion =>
      have rightOrigin := mem_pushConsumer_origin membership
      rcases rightOrigin with rightInserted | beforeRight
      · exact Or.inl
          ⟨rightInserted.1, rfl, by
            simp [Link.premises, rightInserted.2]⟩
      · have leftOrigin := mem_pushConsumer_origin beforeRight
        rcases leftOrigin with leftInserted | old
        · exact Or.inl
            ⟨leftInserted.1, rfl, by
              simp [Link.premises, leftInserted.2]⟩
        · exact Or.inr old
  | «tensor» left right conclusion =>
      have rightOrigin := mem_pushConsumer_origin membership
      rcases rightOrigin with rightInserted | beforeRight
      · exact Or.inl
          ⟨rightInserted.1, rfl, by
            simp [Link.premises, rightInserted.2]⟩
      · have leftOrigin := mem_pushConsumer_origin beforeRight
        rcases leftOrigin with leftInserted | old
        · exact Or.inl
            ⟨leftInserted.1, rfl, by
              simp [Link.premises, leftInserted.2]⟩
        · exact Or.inr old

/-- Folding further indexed links never removes a previously stored
dependency. -/
private theorem mem_foldl_addLinkConsumers_of_mem
    (entries : List (Link × Nat))
    {consumers : Array (List Nat)} {premise existingIndex : Nat}
    (membership :
      existingIndex ∈ (consumers[premise]?).getD []) :
    existingIndex ∈
      ((entries.foldl addLinkConsumers consumers)[premise]?).getD [] := by
  induction entries generalizing consumers with
  | nil =>
      exact membership
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction (mem_addLinkConsumers_of_mem membership)

/-- Every dependency found after a complete consumer-table fold originates
from a concrete connective entry in that fold or from the initial table. -/
private theorem mem_foldl_addLinkConsumers_origin
    (entries : List (Link × Nat))
    {consumers : Array (List Nat)} {premise candidate : Nat}
    (membership :
      candidate ∈
        ((entries.foldl addLinkConsumers consumers)[premise]?).getD []) :
    (∃ link linkIndex,
      (link, linkIndex) ∈ entries ∧
      candidate = linkIndex ∧
      link.isConnective = true ∧
      premise ∈ link.premises) ∨
      candidate ∈ (consumers[premise]?).getD [] := by
  induction entries generalizing consumers with
  | nil =>
      exact Or.inr membership
  | cons head tail induction =>
      simp only [List.foldl_cons] at membership
      rcases induction membership with introduced | beforeTail
      · rcases introduced with
          ⟨link, linkIndex, entryMembership, candidateIndex,
            connective, premiseMembership⟩
        exact Or.inl
          ⟨link, linkIndex, by simp [entryMembership],
            candidateIndex, connective, premiseMembership⟩
      · rcases head with ⟨link, linkIndex⟩
        rcases mem_addLinkConsumers_origin beforeTail with
          introduced | old
        · exact Or.inl
            ⟨link, linkIndex, by simp, introduced.1,
              introduced.2.1, introduced.2.2⟩
        · exact Or.inr old

/-- Processing one in-bounds indexed connective records its index in the
bucket of each of its premises. -/
private theorem mem_addLinkConsumers_of_premise
    {consumers : Array (List Nat)} {link : Link} {linkIndex premise : Nat}
    (bound : premise < consumers.size)
    (premiseMembership : premise ∈ link.premises) :
    linkIndex ∈
      ((addLinkConsumers consumers (link, linkIndex))[premise]?).getD [] := by
  cases link with
  | «axiom» left right =>
      simp [Link.premises] at premiseMembership
  | «par» left right conclusion =>
      simp [Link.premises] at premiseMembership
      rcases premiseMembership with same | same
      · subst premise
        exact mem_pushConsumer_of_mem
          (mem_pushConsumer_self bound)
      · subst premise
        apply mem_pushConsumer_self
        simpa using bound
  | «tensor» left right conclusion =>
      simp [Link.premises] at premiseMembership
      rcases premiseMembership with same | same
      · subst premise
        exact mem_pushConsumer_of_mem
          (mem_pushConsumer_self bound)
      · subst premise
        apply mem_pushConsumer_self
        simpa using bound

/-- Every in-bounds premise dependency present in an indexed entry list is
recorded by the completed consumer fold. -/
private theorem mem_foldl_addLinkConsumers_of_entry
    (entries : List (Link × Nat)) (consumers : Array (List Nat))
    {link : Link} {linkIndex premise : Nat}
    (entryMembership : (link, linkIndex) ∈ entries)
    (bound : premise < consumers.size)
    (premiseMembership : premise ∈ link.premises) :
    linkIndex ∈
      ((entries.foldl addLinkConsumers consumers)[premise]?).getD [] := by
  induction entries generalizing consumers with
  | nil =>
      simp at entryMembership
  | cons head tail induction =>
      simp only [List.mem_cons] at entryMembership
      rcases entryMembership with same | inTail
      · subst head
        simp only [List.foldl_cons]
        apply mem_foldl_addLinkConsumers_of_mem
        exact mem_addLinkConsumers_of_premise bound premiseMembership
      · simp only [List.foldl_cons]
        apply induction
        · exact inTail
        · simpa using bound

/-- The precomputed consumer table covers every concrete in-bounds premise of
every certificate link.  This is the exact no-missed-dependency direction used
when a newly marked conclusion fans out into the work queue. -/
private theorem mem_worklistConsumers_of_premise
    {certificate : Certificate} {link : Link}
    {linkIndex premise : Nat}
    (lookup : certificate.links[linkIndex]? = some link)
    (bound : premise < certificate.formulas.size)
    (premiseMembership : premise ∈ link.premises) :
    linkIndex ∈
      ((worklistConsumers certificate)[premise]?).getD [] := by
  apply mem_foldl_addLinkConsumers_of_entry
  · exact List.mk_mem_zipIdx_iff_getElem?.2 lookup
  · simpa using bound
  · exact premiseMembership

/-- Every stored dependency has exact submitted-link and premise provenance. -/
private theorem mem_worklistConsumers_origin
    {certificate : Certificate} {premise candidate : Nat}
    (membership :
      candidate ∈
        ((worklistConsumers certificate)[premise]?).getD []) :
    ∃ link,
      certificate.links[candidate]? = some link ∧
      link.isConnective = true ∧
      premise ∈ link.premises := by
  have foldedMembership :
      candidate ∈
        (((certificate.links.zipIdx.foldl addLinkConsumers
          (Array.replicate certificate.formulas.size []))[
            premise]?).getD []) := by
    simpa [worklistConsumers] using membership
  rcases
      mem_foldl_addLinkConsumers_origin
        certificate.links.zipIdx foldedMembership with
    introduced | initial
  · rcases introduced with
      ⟨link, linkIndex, entryMembership, candidateIndex,
        connective, premiseMembership⟩
    subst candidate
    exact
      ⟨link,
        List.mk_mem_zipIdx_iff_getElem?.1 entryMembership,
        connective, premiseMembership⟩
  · by_cases premiseBound :
        premise < certificate.formulas.size
    · have initialLookup :
          (Array.replicate certificate.formulas.size
            ([] : List Nat))[premise]? = some [] := by
        simp [premiseBound]
      rw [initialLookup] at initial
      simp at initial
    · have initialLookup :
          (Array.replicate certificate.formulas.size
            ([] : List Nat))[premise]? = none :=
        Array.getElem?_eq_none (by
          simpa using Nat.le_of_not_gt premiseBound)
      rw [initialLookup] at initial
      simp at initial

/-- Every dependency in the precomputed consumer table is the index of a
submitted connective.  This is the reverse provenance direction needed to
show that dependency fan-out can never inject an axiom or an out-of-range
number into the real work queue. -/
private theorem mem_worklistConsumers_submitted_connective
    {certificate : Certificate} {premise candidate : Nat}
    (membership :
      candidate ∈
        ((worklistConsumers certificate)[premise]?).getD []) :
    ∃ link,
      certificate.links[candidate]? = some link ∧
      link.isConnective = true := by
  rcases mem_worklistConsumers_origin membership with
    ⟨link, lookup, connective, _premiseMembership⟩
  exact ⟨link, lookup, connective⟩

/-- Structural linear ownership makes all indices in one consumer bucket
equal. Queue deduplication can therefore record at most one successful
dependency insertion for each newly marked occurrence. -/
private theorem worklistConsumers_members_eq
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {premise first second : Nat}
    (firstMembership :
      first ∈
        ((worklistConsumers certificate)[premise]?).getD [])
    (secondMembership :
      second ∈
        ((worklistConsumers certificate)[premise]?).getD []) :
    first = second := by
  rcases mem_worklistConsumers_origin firstMembership with
    ⟨firstLink, firstLookup, _firstConnective, firstPremise⟩
  rcases mem_worklistConsumers_origin secondMembership with
    ⟨secondLink, secondLookup, _secondConnective, secondPremise⟩
  have firstBound :
      first < certificate.links.length :=
    (List.getElem?_eq_some_iff.mp firstLookup).1
  have secondBound :
      second < certificate.links.length :=
    (List.getElem?_eq_some_iff.mp secondLookup).1
  have firstLinkMembership :
      firstLink ∈ certificate.links := by
    have membership := List.getElem_mem firstBound
    simpa [(List.getElem?_eq_some_iff.mp firstLookup).2] using membership
  have secondLinkMembership :
      secondLink ∈ certificate.links := by
    have membership := List.getElem_mem secondBound
    simpa [(List.getElem?_eq_some_iff.mp secondLookup).2] using membership
  have sameLink : firstLink = secondLink :=
    UnificationState.StructurallyWellFormed.parentLink_unique structural
      firstLinkMembership
      firstPremise
      secondLinkMembership
      secondPremise
  apply
    (List.getElem?_inj firstBound structural.links_nodup).mp
  rw [firstLookup, secondLookup, sameLink]

private def enqueueWorklist (kind : WorklistEnqueueKind)
    (index : Nat) (state : UnificationWorklistState) :
    UnificationWorklistState :=
  if (state.queued[index]?).getD true then
    state
  else
    let nextStats :=
      match kind with
      | .initial =>
          { state.stats with
            initialEnqueues := state.stats.initialEnqueues + 1 }
      | .dependency =>
          { state.stats with
            dependencyEnqueues := state.stats.dependencyEnqueues + 1 }
      | .waiting =>
          { state.stats with
            waitingRequeues := state.stats.waitingRequeues + 1 }
    { state with
      queue := index :: state.queue
      queued := state.queued.setIfInBounds index true
      stats := nextStats }

/-- A single enqueue preserves the exact conservation law between cumulative
successful insertions and concrete queue length. -/
private theorem enqueueWorklist_balance
    (kind : WorklistEnqueueKind) (index : Nat)
    (state : UnificationWorklistState) :
    totalWorklistEnqueues
          (Certificate.enqueueWorklist kind index state).stats +
        state.queue.length =
      totalWorklistEnqueues state.stats +
        (Certificate.enqueueWorklist kind index state).queue.length := by
  unfold Certificate.enqueueWorklist
  split
  · rfl
  · cases kind <;>
      simp [totalWorklistEnqueues] <;>
        omega

/-- Once one index has been armed, immediately arming that same index again is
an exact no-op for every enqueue cause. -/
private theorem enqueueWorklist_idempotent
    (kind : WorklistEnqueueKind) (index : Nat)
    (state : UnificationWorklistState) :
    Certificate.enqueueWorklist kind index
        (Certificate.enqueueWorklist kind index state) =
      Certificate.enqueueWorklist kind index state := by
  unfold Certificate.enqueueWorklist
  split
  · rfl
  · rename_i ready
    have lookupFalse :
        state.queued[index]? = some false := by
      cases lookup : state.queued[index]? with
      | none =>
          simp [lookup] at ready
      | some queued =>
          cases queued with
          | false =>
              rfl
          | true =>
              simp [lookup] at ready
    have indexBound :
        index < state.queued.size :=
      (Array.getElem?_eq_some_iff.mp lookupFalse).1
    simp [indexBound]

/-- A nonempty enqueue batch whose entries are all the same collapses to one
deduplicated enqueue. -/
private theorem foldl_enqueueWorklist_eq_single_of_all_eq
    (kind : WorklistEnqueueKind) (indices : List Nat)
    (anchor : Nat) (state : UnificationWorklistState)
    (nonempty : indices ≠ [])
    (allEqual : ∀ index ∈ indices, index = anchor) :
    indices.foldl
        (fun next index =>
          Certificate.enqueueWorklist kind index next)
        state =
      Certificate.enqueueWorklist kind anchor state := by
  induction indices generalizing state with
  | nil =>
      contradiction
  | cons head tail induction =>
      have headEqual : head = anchor :=
        allEqual head (by simp)
      subst head
      simp only [List.foldl_cons]
      by_cases tailEmpty : tail = []
      · subst tail
        simp
      · rw [induction
          (state :=
            Certificate.enqueueWorklist kind anchor state)
          tailEmpty
          (by
            intro index membership
            exact allEqual index (by simp [membership]))]
        exact enqueueWorklist_idempotent kind anchor state

/-- One dependency enqueue can increase its dedicated counter by at most one. -/
private theorem enqueueWorklist_dependencyEnqueues_le
    (index : Nat) (state : UnificationWorklistState) :
    (Certificate.enqueueWorklist .dependency index state).stats.dependencyEnqueues ≤
      state.stats.dependencyEnqueues + 1 := by
  unfold Certificate.enqueueWorklist
  split <;> simp <;> omega

/-- One waiting enqueue can increase its dedicated counter by at most one. -/
private theorem enqueueWorklist_waitingRequeues_le
    (index : Nat) (state : UnificationWorklistState) :
    (Certificate.enqueueWorklist .waiting index state).stats.waitingRequeues ≤
      state.stats.waitingRequeues + 1 := by
  unfold Certificate.enqueueWorklist
  split <;> simp <;> omega

/-- A waiting-enqueue batch adds no more successful insertions than requested
indices, even before using queue deduplication. -/
private theorem foldl_enqueueWorklist_waitingRequeues_le
    (indices : List Nat) (state : UnificationWorklistState) :
    (indices.foldl
      (fun next index =>
        Certificate.enqueueWorklist .waiting index next)
      state).stats.waitingRequeues ≤
        state.stats.waitingRequeues + indices.length := by
  induction indices generalizing state with
  | nil =>
      simp
  | cons head tail induction =>
      simp only [List.foldl_cons, List.length_cons]
      have first :=
        enqueueWorklist_waitingRequeues_le head state
      have rest :=
        induction
          (state :=
            Certificate.enqueueWorklist .waiting head state)
      omega

/-- Repeated enqueues telescope the same insertion/queue conservation law. -/
private theorem foldl_enqueueWorklist_balance
    (kind : WorklistEnqueueKind) (indices : List Nat)
    (state : UnificationWorklistState) :
    let final :=
      indices.foldl
        (fun next index =>
          Certificate.enqueueWorklist kind index next)
        state
    totalWorklistEnqueues final.stats + state.queue.length =
      totalWorklistEnqueues state.stats + final.queue.length := by
  induction indices generalizing state with
  | nil =>
      rfl
  | cons head tail induction =>
      simp only [List.foldl_cons]
      have first :=
        enqueueWorklist_balance kind head state
      have rest :=
        induction
          (state :=
            Certificate.enqueueWorklist kind head state)
      omega

/-- Enqueueing preserves the deduplication-flag carrier. -/
@[simp] private theorem enqueueWorklist_queued_size
    (kind : WorklistEnqueueKind) (index : Nat)
    (state : UnificationWorklistState) :
    (enqueueWorklist kind index state).queued.size =
      state.queued.size := by
  unfold enqueueWorklist
  split <;> simp

/-- Enqueueing never changes the token-unification core. -/
@[simp] private theorem enqueueWorklist_core
    (kind : WorklistEnqueueKind) (index : Nat)
    (state : UnificationWorklistState) :
    (enqueueWorklist kind index state).core = state.core := by
  unfold enqueueWorklist
  split <;> rfl

/-- Queue insertion does not itself record a connective firing. -/
@[simp] private theorem enqueueWorklist_successfulFirings
    (kind : WorklistEnqueueKind) (index : Nat)
    (state : UnificationWorklistState) :
    (enqueueWorklist kind index state).stats.successfulFirings =
      state.stats.successfulFirings := by
  unfold enqueueWorklist
  split
  · rfl
  · cases kind <;> rfl

/-- A dependency enqueue cannot change the waiting-requeue counter. -/
@[simp] private theorem enqueueWorklist_dependency_waitingRequeues
    (index : Nat) (state : UnificationWorklistState) :
    (enqueueWorklist .dependency index state).stats.waitingRequeues =
      state.stats.waitingRequeues := by
  unfold enqueueWorklist
  split <;> rfl

/-- A waiting enqueue cannot change the dependency counter. -/
@[simp] private theorem enqueueWorklist_waiting_dependencyEnqueues
    (index : Nat) (state : UnificationWorklistState) :
    (enqueueWorklist .waiting index state).stats.dependencyEnqueues =
      state.stats.dependencyEnqueues := by
  unfold enqueueWorklist
  split <;> rfl

/-- Non-initial scheduler enqueues preserve the initialization counter. -/
@[simp] private theorem enqueueWorklist_dependency_initialEnqueues
    (index : Nat) (state : UnificationWorklistState) :
    (enqueueWorklist .dependency index state).stats.initialEnqueues =
      state.stats.initialEnqueues := by
  unfold enqueueWorklist
  split <;> rfl

@[simp] private theorem enqueueWorklist_waiting_initialEnqueues
    (index : Nat) (state : UnificationWorklistState) :
    (enqueueWorklist .waiting index state).stats.initialEnqueues =
      state.stats.initialEnqueues := by
  unfold enqueueWorklist
  split <;> rfl

/-- Queue enqueues do not change the waiting registry. -/
@[simp] private theorem enqueueWorklist_waiting
    (kind : WorklistEnqueueKind) (index : Nat)
    (state : UnificationWorklistState) :
    (enqueueWorklist kind index state).waiting = state.waiting := by
  unfold enqueueWorklist
  split <;> rfl

/-- Queue enqueues do not change waiting deduplication flags. -/
@[simp] private theorem enqueueWorklist_waitingFlags
    (kind : WorklistEnqueueKind) (index : Nat)
    (state : UnificationWorklistState) :
    (enqueueWorklist kind index state).waitingFlags =
      state.waitingFlags := by
  unfold enqueueWorklist
  split <;> rfl

/-- A real queue member remains present after any later enqueue. -/
private theorem mem_enqueueWorklist_of_mem
    {state : UnificationWorklistState} {candidate : Nat}
    (membership : candidate ∈ state.queue)
    (kind : WorklistEnqueueKind) (index : Nat) :
    candidate ∈ (enqueueWorklist kind index state).queue := by
  unfold enqueueWorklist
  split
  · exact membership
  · exact List.mem_cons_of_mem index membership

/-- Deduplication is non-lossy whenever every pre-existing `true` flag denotes
an actual queue member. -/
private theorem QueueFlagSound.enqueueWorklist
    {state : UnificationWorklistState}
    (sound : QueueFlagSound state)
    (kind : WorklistEnqueueKind) (index : Nat) :
    QueueFlagSound (enqueueWorklist kind index state) := by
  intro candidate flagged
  by_cases already : state.queued[index]?.getD true = true
  · simp [Certificate.enqueueWorklist, already] at flagged ⊢
    exact sound flagged
  · simp [Certificate.enqueueWorklist, already] at flagged ⊢
    by_cases same : index = candidate
    · subst candidate
      simp
    · have oldFlag : state.queued[candidate]? = some true := by
        simpa [Array.getElem?_setIfInBounds, same] using flagged
      exact Or.inr (sound oldFlag)

/-- Enqueueing preserves the reverse queue-membership-to-flag direction. -/
private theorem QueueFlagComplete.enqueueWorklist
    {state : UnificationWorklistState}
    (complete : QueueFlagComplete state)
    (kind : WorklistEnqueueKind) (index : Nat) :
    QueueFlagComplete
      (Certificate.enqueueWorklist kind index state) := by
  intro candidate membership
  by_cases already : state.queued[index]?.getD true = true
  · have oldMembership :
        candidate ∈ state.queue := by
      simpa [Certificate.enqueueWorklist, already] using membership
    have oldFlag := complete oldMembership
    simpa [Certificate.enqueueWorklist, already] using oldFlag
  · have lookupFalse :
        state.queued[index]? = some false := by
      cases lookup : state.queued[index]? with
      | none =>
          simp [lookup] at already
      | some flag =>
          cases flag with
          | false =>
              rfl
          | true =>
              simp [lookup] at already
    have indexBound :
        index < state.queued.size :=
      (Array.getElem?_eq_some_iff.mp lookupFalse).1
    simp [Certificate.enqueueWorklist, already] at membership
    rcases membership with same | old
    · subst candidate
      have setLookup :
          (state.queued.setIfInBounds index true)[index]? =
            some true := by
        simp [indexBound]
      simpa [Certificate.enqueueWorklist, already] using setLookup
    · by_cases same : index = candidate
      · subst candidate
        have setLookup :
            (state.queued.setIfInBounds index true)[index]? =
              some true := by
          simp [indexBound]
        simpa [Certificate.enqueueWorklist, already] using setLookup
      · have oldFlag := complete old
        have setLookup :
            (state.queued.setIfInBounds index true)[candidate]? =
              some true := by
          simpa [Array.getElem?_setIfInBounds, same] using oldFlag
        simpa [Certificate.enqueueWorklist, already] using setLookup

/-- Exact flags prevent a successful enqueue from introducing a duplicate
queue entry. -/
private theorem QueueNodup.enqueueWorklist
    {state : UnificationWorklistState}
    (nodup : QueueNodup state)
    (complete : QueueFlagComplete state)
    (kind : WorklistEnqueueKind) (index : Nat) :
    QueueNodup
      (Certificate.enqueueWorklist kind index state) := by
  by_cases already : state.queued[index]?.getD true = true
  · simpa [Certificate.enqueueWorklist, already] using nodup
  · simp [Certificate.enqueueWorklist, already, QueueNodup]
    constructor
    · intro membership
      have flagged := complete membership
      simp [flagged] at already
    · exact nodup

/-- Queue enqueues leave waiting-flag completeness unchanged. -/
private theorem WaitingFlagComplete.enqueueWorklist
    {state : UnificationWorklistState}
    (complete : WaitingFlagComplete state)
    (kind : WorklistEnqueueKind) (index : Nat) :
    WaitingFlagComplete
      (Certificate.enqueueWorklist kind index state) := by
  intro candidate membership
  have oldMembership :
      candidate ∈ state.waiting := by
    simpa using membership
  have oldFlag := complete oldMembership
  simpa using oldFlag

/-- Queue enqueues leave waiting-registry uniqueness unchanged. -/
private theorem WaitingNodup.enqueueWorklist
    {state : UnificationWorklistState}
    (nodup : WaitingNodup state)
    (kind : WorklistEnqueueKind) (index : Nat) :
    WaitingNodup
      (Certificate.enqueueWorklist kind index state) := by
  simpa [WaitingNodup] using nodup

/-- An in-bounds requested index is a real queue member after enqueue.  The
only no-op case is a sound pre-existing `true` flag. -/
private theorem QueueFlagSound.mem_enqueueWorklist
    {state : UnificationWorklistState}
    (sound : QueueFlagSound state)
    (kind : WorklistEnqueueKind) {index : Nat}
    (bound : index < state.queued.size) :
    index ∈
      (Certificate.enqueueWorklist kind index state).queue := by
  cases lookup : state.queued[index]? with
  | none =>
      have outOfBounds := Array.getElem?_eq_none_iff.mp lookup
      omega
  | some flag =>
      cases flag with
      | false =>
          simp [Certificate.enqueueWorklist, lookup]
      | true =>
          simpa [Certificate.enqueueWorklist, lookup] using sound lookup

/-- Enqueueing an in-bounds index preserves bounds for every real queue
member. -/
private theorem QueueBounded.enqueueWorklist
    {state : UnificationWorklistState}
    (bounded : QueueBounded state)
    (kind : WorklistEnqueueKind) {index : Nat}
    (indexBound : index < state.queued.size) :
    QueueBounded
      (Certificate.enqueueWorklist kind index state) := by
  intro candidate membership
  by_cases already : state.queued[index]?.getD true = true
  · simp [Certificate.enqueueWorklist, already] at membership ⊢
    exact bounded membership
  · simp [Certificate.enqueueWorklist, already] at membership ⊢
    rcases membership with same | oldMembership
    · subst candidate
      simpa using indexBound
    · simpa using bounded oldMembership

/-- Enqueueing one submitted connective preserves exact queue provenance. -/
private theorem QueueConnectiveSound.enqueueWorklist
    {certificate : Certificate} {state : UnificationWorklistState}
    (sound : QueueConnectiveSound certificate state)
    (kind : WorklistEnqueueKind) (index : Nat)
    (submitted : SubmittedConnective certificate index) :
    QueueConnectiveSound certificate
      (Certificate.enqueueWorklist kind index state) := by
  intro candidate membership
  by_cases already : state.queued[index]?.getD true = true
  · simp [Certificate.enqueueWorklist, already] at membership
    exact sound membership
  · simp [Certificate.enqueueWorklist, already] at membership
    rcases membership with same | old
    · subst candidate
      exact submitted
    · exact sound old

/-- Queue-only enqueues leave the waiting-par provenance unchanged. -/
private theorem WaitingParSound.enqueueWorklist
    {certificate : Certificate} {state : UnificationWorklistState}
    (sound : WaitingParSound certificate state)
    (kind : WorklistEnqueueKind) (index : Nat) :
    WaitingParSound certificate
      (Certificate.enqueueWorklist kind index state) := by
  intro candidate membership
  apply sound
  simpa using membership

/-- Enqueueing cannot invalidate scheduler coverage: it leaves token and
waiting state unchanged and only adds a real queue member (or is a deduplicated
no-op). -/
private theorem SchedulerCoverage.enqueueWorklist
    {certificate : Certificate} {state : UnificationWorklistState}
    (coverage : SchedulerCoverage certificate state)
    (kind : WorklistEnqueueKind) (index : Nat) :
    SchedulerCoverage certificate
      (enqueueWorklist kind index state) := by
  intro candidateIndex link lookup connective
  have covered := coverage lookup connective
  unfold Certificate.enqueueWorklist
  split
  · exact covered
  · cases covered with
    | queued membership =>
        apply ConnectiveSchedulerStatus.queued
        simp [membership]
    | firedPar marked =>
        exact ConnectiveSchedulerStatus.firedPar marked
    | firedTensor marked =>
        exact ConnectiveSchedulerStatus.firedTensor marked
    | idlePar idle =>
        exact ConnectiveSchedulerStatus.idlePar idle
    | idleTensor idle =>
        exact ConnectiveSchedulerStatus.idleTensor idle
    | waitingPar leftMarked rightMarked different registered bound =>
        apply ConnectiveSchedulerStatus.waitingPar
        · exact leftMarked
        · exact rightMarked
        · exact different
        · exact registered
        · simpa using bound
    | tensorDeadlock leftMarked rightMarked =>
        exact ConnectiveSchedulerStatus.tensorDeadlock
          leftMarked rightMarked

/-- Repeated enqueues preserve scheduler coverage, which is the induction
principle used by dependency fan-out and waiting-par requeues. -/
private theorem SchedulerCoverage.enqueueMany
    {certificate : Certificate}
    (kind : WorklistEnqueueKind) (indices : List Nat)
    {state : UnificationWorklistState}
    (coverage : SchedulerCoverage certificate state) :
    SchedulerCoverage certificate
      (indices.foldl
        (fun next index =>
          Certificate.enqueueWorklist kind index next)
        state) := by
  induction indices generalizing state with
  | nil =>
      exact coverage
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction (coverage.enqueueWorklist kind head)

/-- Repeated enqueues preserve sound queue flags. -/
private theorem QueueFlagSound.enqueueMany
    (kind : WorklistEnqueueKind) (indices : List Nat)
    {state : UnificationWorklistState}
    (sound : QueueFlagSound state) :
    QueueFlagSound
      (indices.foldl
        (fun next index =>
          Certificate.enqueueWorklist kind index next)
        state) := by
  induction indices generalizing state with
  | nil =>
      exact sound
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction (sound.enqueueWorklist kind head)

/-- Repeated queue enqueues preserve membership-to-flag completeness. -/
private theorem QueueFlagComplete.enqueueMany
    (kind : WorklistEnqueueKind) (indices : List Nat)
    {state : UnificationWorklistState}
    (complete : QueueFlagComplete state) :
    QueueFlagComplete
      (indices.foldl
        (fun next index =>
          Certificate.enqueueWorklist kind index next)
        state) := by
  induction indices generalizing state with
  | nil =>
      exact complete
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction (complete.enqueueWorklist kind head)

/-- Repeated queue enqueues preserve uniqueness when the initial flags are
complete. -/
private theorem QueueNodup.enqueueMany
    (kind : WorklistEnqueueKind) (indices : List Nat)
    {state : UnificationWorklistState}
    (nodup : QueueNodup state)
    (complete : QueueFlagComplete state) :
    QueueNodup
      (indices.foldl
        (fun next index =>
          Certificate.enqueueWorklist kind index next)
        state) := by
  induction indices generalizing state with
  | nil =>
      exact nodup
  | cons head tail induction =>
      simp only [List.foldl_cons]
      have nextComplete :
          QueueFlagComplete
            (Certificate.enqueueWorklist kind head state) :=
        QueueFlagComplete.enqueueWorklist complete kind head
      apply induction
      · exact QueueNodup.enqueueWorklist
          nodup complete kind head
      · exact nextComplete

/-- Repeated queue enqueues preserve waiting-flag completeness. -/
private theorem WaitingFlagComplete.enqueueMany
    (kind : WorklistEnqueueKind) (indices : List Nat)
    {state : UnificationWorklistState}
    (complete : WaitingFlagComplete state) :
    WaitingFlagComplete
      (indices.foldl
        (fun next index =>
          Certificate.enqueueWorklist kind index next)
        state) := by
  induction indices generalizing state with
  | nil =>
      exact complete
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction (complete.enqueueWorklist kind head)

/-- Repeated queue enqueues preserve waiting-registry uniqueness. -/
private theorem WaitingNodup.enqueueMany
    (kind : WorklistEnqueueKind) (indices : List Nat)
    {state : UnificationWorklistState}
    (nodup : WaitingNodup state) :
    WaitingNodup
      (indices.foldl
        (fun next index =>
          Certificate.enqueueWorklist kind index next)
        state) := by
  induction indices generalizing state with
  | nil =>
      exact nodup
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction (nodup.enqueueWorklist kind head)

/-- A batch consisting only of submitted connectives preserves exact queue
provenance. -/
private theorem QueueConnectiveSound.enqueueMany
    {certificate : Certificate}
    (kind : WorklistEnqueueKind) (indices : List Nat)
    {state : UnificationWorklistState}
    (sound : QueueConnectiveSound certificate state)
    (submitted :
      ∀ index ∈ indices,
        SubmittedConnective certificate index) :
    QueueConnectiveSound certificate
      (indices.foldl
        (fun next index =>
          Certificate.enqueueWorklist kind index next)
        state) := by
  induction indices generalizing state with
  | nil =>
      exact sound
  | cons head tail induction =>
      simp only [List.foldl_cons]
      apply induction
      · apply sound.enqueueWorklist kind head
        exact submitted head (by simp)
      · intro index membership
        exact submitted index (by simp [membership])

/-- A batch of queue enqueues preserves waiting-par provenance. -/
private theorem WaitingParSound.enqueueMany
    {certificate : Certificate}
    (kind : WorklistEnqueueKind) (indices : List Nat)
    {state : UnificationWorklistState}
    (sound : WaitingParSound certificate state) :
    WaitingParSound certificate
      (indices.foldl
        (fun next index =>
          Certificate.enqueueWorklist kind index next)
        state) := by
  induction indices generalizing state with
  | nil =>
      exact sound
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction (sound.enqueueWorklist kind head)

/-- A batch of in-bounds enqueues preserves bounds for the real queue. -/
private theorem QueueBounded.enqueueMany
    (kind : WorklistEnqueueKind) (indices : List Nat)
    {state : UnificationWorklistState}
    (bounded : QueueBounded state)
    (indicesBounded :
      ∀ index ∈ indices, index < state.queued.size) :
    QueueBounded
      (indices.foldl
        (fun next index =>
          Certificate.enqueueWorklist kind index next)
        state) := by
  induction indices generalizing state with
  | nil =>
      exact bounded
  | cons head tail induction =>
      simp only [List.foldl_cons]
      apply induction
      · apply bounded.enqueueWorklist kind
        exact indicesBounded head (by simp)
      · intro index membership
        have oldBound := indicesBounded index (by simp [membership])
        simpa using oldBound

/-- Later enqueues preserve every real queue member. -/
private theorem mem_foldl_enqueueWorklist_of_mem
    (kind : WorklistEnqueueKind) (indices : List Nat)
    {state : UnificationWorklistState} {candidate : Nat}
    (membership : candidate ∈ state.queue) :
    candidate ∈
      (indices.foldl
        (fun next index =>
          Certificate.enqueueWorklist kind index next)
        state).queue := by
  induction indices generalizing state with
  | nil =>
      exact membership
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction
        (mem_enqueueWorklist_of_mem membership kind head)

/-- A batch of scheduler enqueues never changes the token-unification core. -/
@[simp] private theorem foldl_enqueueWorklist_core
    (kind : WorklistEnqueueKind) (indices : List Nat)
    (state : UnificationWorklistState) :
    (indices.foldl
      (fun next index =>
        Certificate.enqueueWorklist kind index next)
      state).core = state.core := by
  induction indices generalizing state with
  | nil =>
      rfl
  | cons head tail induction =>
      simp only [List.foldl_cons]
      rw [induction]
      simp

/-- A queue-enqueue batch does not itself record connective firings. -/
@[simp] private theorem foldl_enqueueWorklist_successfulFirings
    (kind : WorklistEnqueueKind) (indices : List Nat)
    (state : UnificationWorklistState) :
    (indices.foldl
      (fun next index =>
        Certificate.enqueueWorklist kind index next)
      state).stats.successfulFirings =
        state.stats.successfulFirings := by
  induction indices generalizing state with
  | nil =>
      rfl
  | cons head tail induction =>
      simp only [List.foldl_cons]
      rw [induction]
      simp

/-- A batch of dependency enqueues leaves the waiting-requeue counter
unchanged. -/
@[simp] private theorem foldl_enqueueWorklist_dependency_waitingRequeues
    (indices : List Nat) (state : UnificationWorklistState) :
    (indices.foldl
      (fun next index =>
        Certificate.enqueueWorklist .dependency index next)
      state).stats.waitingRequeues =
        state.stats.waitingRequeues := by
  induction indices generalizing state with
  | nil =>
      rfl
  | cons head tail induction =>
      simp only [List.foldl_cons]
      rw [induction]
      simp

/-- A batch of waiting enqueues leaves the dependency counter unchanged. -/
@[simp] private theorem foldl_enqueueWorklist_waiting_dependencyEnqueues
    (indices : List Nat) (state : UnificationWorklistState) :
    (indices.foldl
      (fun next index =>
        Certificate.enqueueWorklist .waiting index next)
      state).stats.dependencyEnqueues =
        state.stats.dependencyEnqueues := by
  induction indices generalizing state with
  | nil =>
      rfl
  | cons head tail induction =>
      simp only [List.foldl_cons]
      rw [induction]
      simp

/-- Non-initial enqueue batches preserve the initialization counter. -/
@[simp] private theorem foldl_enqueueWorklist_dependency_initialEnqueues
    (indices : List Nat) (state : UnificationWorklistState) :
    (indices.foldl
      (fun next index =>
        Certificate.enqueueWorklist .dependency index next)
      state).stats.initialEnqueues =
        state.stats.initialEnqueues := by
  induction indices generalizing state with
  | nil =>
      rfl
  | cons head tail induction =>
      simp only [List.foldl_cons]
      rw [induction]
      simp

@[simp] private theorem foldl_enqueueWorklist_waiting_initialEnqueues
    (indices : List Nat) (state : UnificationWorklistState) :
    (indices.foldl
      (fun next index =>
        Certificate.enqueueWorklist .waiting index next)
      state).stats.initialEnqueues =
        state.stats.initialEnqueues := by
  induction indices generalizing state with
  | nil =>
      rfl
  | cons head tail induction =>
      simp only [List.foldl_cons]
      rw [induction]
      simp

/-- A queue-enqueue batch leaves the waiting registry unchanged. -/
@[simp] private theorem foldl_enqueueWorklist_waiting
    (kind : WorklistEnqueueKind) (indices : List Nat)
    (state : UnificationWorklistState) :
    (indices.foldl
      (fun next index =>
        Certificate.enqueueWorklist kind index next)
      state).waiting = state.waiting := by
  induction indices generalizing state with
  | nil =>
      rfl
  | cons head tail induction =>
      simp only [List.foldl_cons]
      rw [induction]
      simp

/-- A queue-enqueue batch leaves waiting flags unchanged. -/
@[simp] private theorem foldl_enqueueWorklist_waitingFlags
    (kind : WorklistEnqueueKind) (indices : List Nat)
    (state : UnificationWorklistState) :
    (indices.foldl
      (fun next index =>
        Certificate.enqueueWorklist kind index next)
      state).waitingFlags = state.waitingFlags := by
  induction indices generalizing state with
  | nil =>
      rfl
  | cons head tail induction =>
      simp only [List.foldl_cons]
      rw [induction]
      simp

/-- If an in-bounds index occurs in an enqueue batch, sound deduplication
guarantees that it is present in the final real queue. -/
private theorem QueueFlagSound.mem_enqueueMany
    {state : UnificationWorklistState}
    (sound : QueueFlagSound state)
    (kind : WorklistEnqueueKind) (indices : List Nat)
    {candidate : Nat} (membership : candidate ∈ indices)
    (bound : candidate < state.queued.size) :
    candidate ∈
      (indices.foldl
        (fun next index =>
          Certificate.enqueueWorklist kind index next)
        state).queue := by
  induction indices generalizing state with
  | nil =>
      simp at membership
  | cons head tail induction =>
      simp only [List.mem_cons] at membership
      rcases membership with same | inTail
      · subst candidate
        simp only [List.foldl_cons]
        apply mem_foldl_enqueueWorklist_of_mem
        exact sound.mem_enqueueWorklist kind bound
      · simp only [List.foldl_cons]
        apply induction (state :=
          Certificate.enqueueWorklist kind head state)
        · exact sound.enqueueWorklist kind head
        · exact inTail
        · simpa using bound

private def enqueueConsumers (consumers : Array (List Nat))
    (conclusion : Vertex) (state : UnificationWorklistState) :
    UnificationWorklistState :=
  match consumers[conclusion]? with
  | none => state
  | some indices =>
      indices.foldl
        (fun next index =>
          enqueueWorklist .dependency index next)
        state

/-- Dependency fan-out preserves cumulative-enqueue/queue conservation. -/
private theorem enqueueConsumers_balance
    (consumers : Array (List Nat)) (conclusion : Vertex)
    (state : UnificationWorklistState) :
    totalWorklistEnqueues
          (Certificate.enqueueConsumers consumers conclusion state).stats +
        state.queue.length =
      totalWorklistEnqueues state.stats +
        (Certificate.enqueueConsumers consumers conclusion state).queue.length := by
  unfold Certificate.enqueueConsumers
  split
  · rfl
  · exact foldl_enqueueWorklist_balance .dependency _ state

/-- Structural resource linearity and queue deduplication bound dependency
fan-out from one newly marked occurrence by one successful insertion. -/
private theorem enqueueConsumers_dependencyEnqueues_le
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (conclusion : Vertex) (state : UnificationWorklistState) :
    (Certificate.enqueueConsumers certificate.worklistConsumers
          conclusion state).stats.dependencyEnqueues ≤
      state.stats.dependencyEnqueues + 1 := by
  cases bucketLookup :
      certificate.worklistConsumers[conclusion]? with
  | none =>
      simp [Certificate.enqueueConsumers, bucketLookup]
  | some indices =>
      by_cases indicesEmpty : indices = []
      · subst indices
        simp [Certificate.enqueueConsumers, bucketLookup]
      · have allEqual :
          ∀ index ∈ indices,
            index = indices.head indicesEmpty := by
          intro index membership
          apply worklistConsumers_members_eq
            (premise := conclusion) structural
          · rw [bucketLookup]
            exact membership
          · rw [bucketLookup]
            exact List.head_mem indicesEmpty
        have collapsed :=
          foldl_enqueueWorklist_eq_single_of_all_eq
            .dependency indices (indices.head indicesEmpty) state
            indicesEmpty allEqual
        simp only [Certificate.enqueueConsumers, bucketLookup]
        rw [collapsed]
        exact enqueueWorklist_dependencyEnqueues_le _ state

/-- A dependency-enqueue batch preserves the queue-flag carrier. -/
@[simp] private theorem foldl_enqueueWorklist_queued_size
    (kind : WorklistEnqueueKind) (indices : List Nat)
    (state : UnificationWorklistState) :
    (indices.foldl
      (fun next index =>
        Certificate.enqueueWorklist kind index next)
      state).queued.size = state.queued.size := by
  induction indices generalizing state with
  | nil =>
      rfl
  | cons head tail induction =>
      simp only [List.foldl_cons]
      rw [induction]
      simp

/-- Dependency fan-out changes only scheduler fields. -/
@[simp] private theorem enqueueConsumers_core
    (consumers : Array (List Nat)) (conclusion : Vertex)
    (state : UnificationWorklistState) :
    (enqueueConsumers consumers conclusion state).core = state.core := by
  unfold enqueueConsumers
  split
  · rfl
  · simp

/-- Dependency fan-out does not itself record connective firings. -/
@[simp] private theorem enqueueConsumers_successfulFirings
    (consumers : Array (List Nat)) (conclusion : Vertex)
    (state : UnificationWorklistState) :
    (enqueueConsumers consumers conclusion state).stats.successfulFirings =
      state.stats.successfulFirings := by
  unfold enqueueConsumers
  split
  · rfl
  · simp

/-- Dependency fan-out cannot change the waiting-requeue counter. -/
@[simp] private theorem enqueueConsumers_waitingRequeues
    (consumers : Array (List Nat)) (conclusion : Vertex)
    (state : UnificationWorklistState) :
    (enqueueConsumers consumers conclusion state).stats.waitingRequeues =
      state.stats.waitingRequeues := by
  unfold enqueueConsumers
  split
  · rfl
  · simp

/-- Dependency fan-out preserves the initialization counter. -/
@[simp] private theorem enqueueConsumers_initialEnqueues
    (consumers : Array (List Nat)) (conclusion : Vertex)
    (state : UnificationWorklistState) :
    (enqueueConsumers consumers conclusion state).stats.initialEnqueues =
      state.stats.initialEnqueues := by
  unfold enqueueConsumers
  split
  · rfl
  · simp

/-- Dependency fan-out preserves the queue-flag carrier. -/
@[simp] private theorem enqueueConsumers_queued_size
    (consumers : Array (List Nat)) (conclusion : Vertex)
    (state : UnificationWorklistState) :
    (enqueueConsumers consumers conclusion state).queued.size =
      state.queued.size := by
  unfold enqueueConsumers
  split
  · rfl
  · simp

/-- Dependency fan-out does not change the waiting registry. -/
@[simp] private theorem enqueueConsumers_waiting
    (consumers : Array (List Nat)) (conclusion : Vertex)
    (state : UnificationWorklistState) :
    (enqueueConsumers consumers conclusion state).waiting =
      state.waiting := by
  unfold enqueueConsumers
  split
  · rfl
  · simp

/-- Dependency fan-out through the concrete certificate consumer table can
enqueue only submitted connectives. -/
private theorem QueueConnectiveSound.enqueueConsumersWorklist
    {certificate : Certificate} {state : UnificationWorklistState}
    (sound : QueueConnectiveSound certificate state)
    (conclusion : Vertex) :
    QueueConnectiveSound certificate
      (Certificate.enqueueConsumers
        certificate.worklistConsumers conclusion state) := by
  cases bucketLookup :
      certificate.worklistConsumers[conclusion]? with
  | none =>
      intro index membership
      apply sound
      simpa [Certificate.enqueueConsumers, bucketLookup] using membership
  | some indices =>
      unfold Certificate.enqueueConsumers
      rw [bucketLookup]
      apply sound.enqueueMany .dependency indices
      intro index membership
      unfold SubmittedConnective
      exact mem_worklistConsumers_submitted_connective
        (certificate := certificate) (premise := conclusion)
        (candidate := index)
        (by simpa [bucketLookup] using membership)

/-- Dependency fan-out never changes which submitted pars are waiting. -/
private theorem WaitingParSound.enqueueConsumers
    {certificate : Certificate} {state : UnificationWorklistState}
    (sound : WaitingParSound certificate state)
    (consumers : Array (List Nat)) (conclusion : Vertex) :
    WaitingParSound certificate
      (Certificate.enqueueConsumers consumers conclusion state) := by
  intro index membership
  apply sound
  simpa using membership

/-- Dependency fan-out preserves sound queue flags. -/
private theorem QueueFlagSound.enqueueConsumers
    {state : UnificationWorklistState}
    (sound : QueueFlagSound state)
    (consumers : Array (List Nat)) (conclusion : Vertex) :
    QueueFlagSound
      (Certificate.enqueueConsumers consumers conclusion state) := by
  unfold Certificate.enqueueConsumers
  split
  · exact sound
  · exact sound.enqueueMany .dependency _

/-- A single queue enqueue leaves waiting-flag soundness unchanged. -/
private theorem WaitingFlagSound.enqueueWorklist
    {state : UnificationWorklistState}
    (sound : WaitingFlagSound state)
    (kind : WorklistEnqueueKind) (index : Nat) :
    WaitingFlagSound
      (Certificate.enqueueWorklist kind index state) := by
  intro candidate flagged
  have oldFlag :
      state.waitingFlags[candidate]? = some true := by
    simpa using flagged
  have oldMembership := sound oldFlag
  simpa using oldMembership

/-- Repeated queue enqueues leave waiting-flag soundness unchanged. -/
private theorem WaitingFlagSound.enqueueMany
    (kind : WorklistEnqueueKind) (indices : List Nat)
    {state : UnificationWorklistState}
    (sound : WaitingFlagSound state) :
    WaitingFlagSound
      (indices.foldl
        (fun next index =>
          Certificate.enqueueWorklist kind index next)
        state) := by
  induction indices generalizing state with
  | nil =>
      exact sound
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction (sound.enqueueWorklist kind head)

/-- Dependency fan-out leaves waiting-flag soundness unchanged. -/
private theorem WaitingFlagSound.enqueueConsumers
    {state : UnificationWorklistState}
    (sound : WaitingFlagSound state)
    (consumers : Array (List Nat)) (conclusion : Vertex) :
    WaitingFlagSound
      (Certificate.enqueueConsumers consumers conclusion state) := by
  unfold Certificate.enqueueConsumers
  split
  · exact sound
  · exact sound.enqueueMany .dependency _

/-- Dependency fan-out preserves exact queue flags. -/
private theorem QueueFlagComplete.enqueueConsumers
    {state : UnificationWorklistState}
    (complete : QueueFlagComplete state)
    (consumers : Array (List Nat)) (conclusion : Vertex) :
    QueueFlagComplete
      (Certificate.enqueueConsumers consumers conclusion state) := by
  unfold Certificate.enqueueConsumers
  split
  · exact complete
  · exact complete.enqueueMany .dependency _

/-- Dependency fan-out preserves queue uniqueness. -/
private theorem QueueNodup.enqueueConsumers
    {state : UnificationWorklistState}
    (nodup : QueueNodup state)
    (complete : QueueFlagComplete state)
    (consumers : Array (List Nat)) (conclusion : Vertex) :
    QueueNodup
      (Certificate.enqueueConsumers consumers conclusion state) := by
  unfold Certificate.enqueueConsumers
  split
  · exact nodup
  · exact nodup.enqueueMany .dependency _ complete

/-- Dependency fan-out preserves waiting-flag completeness. -/
private theorem WaitingFlagComplete.enqueueConsumers
    {state : UnificationWorklistState}
    (complete : WaitingFlagComplete state)
    (consumers : Array (List Nat)) (conclusion : Vertex) :
    WaitingFlagComplete
      (Certificate.enqueueConsumers consumers conclusion state) := by
  unfold Certificate.enqueueConsumers
  split
  · exact complete
  · exact complete.enqueueMany .dependency _

/-- Dependency fan-out preserves waiting-registry uniqueness. -/
private theorem WaitingNodup.enqueueConsumers
    {state : UnificationWorklistState}
    (nodup : WaitingNodup state)
    (consumers : Array (List Nat)) (conclusion : Vertex) :
    WaitingNodup
      (Certificate.enqueueConsumers consumers conclusion state) := by
  unfold Certificate.enqueueConsumers
  split
  · exact nodup
  · exact nodup.enqueueMany .dependency _

/-- Dependency fan-out preserves the waiting-flag carrier. -/
@[simp] private theorem enqueueConsumers_waitingFlags_size
    (consumers : Array (List Nat)) (conclusion : Vertex)
    (state : UnificationWorklistState) :
    ((Certificate.enqueueConsumers consumers conclusion state).waitingFlags).size =
      state.waitingFlags.size := by
  unfold Certificate.enqueueConsumers
  split
  · rfl
  · simp

/-- Marking fan-out cannot lose previously covered work, regardless of which
consumer indices are present. Exactness of the consumer table is a separate
obligation used to show that all newly enabled links are added. -/
private theorem SchedulerCoverage.enqueueConsumers
    {certificate : Certificate} (coverage : SchedulerCoverage certificate state)
    (consumers : Array (List Nat)) (conclusion : Vertex) :
    SchedulerCoverage certificate
      (enqueueConsumers consumers conclusion state) := by
  unfold Certificate.enqueueConsumers
  split
  · exact coverage
  · exact coverage.enqueueMany .dependency _

/-- Dependency fan-out preserves every queue member which was already
scheduled before the newly marked conclusion was broadcast. -/
private theorem mem_enqueueConsumers_of_mem
    {consumers : Array (List Nat)} {conclusion candidate : Nat}
    {state : UnificationWorklistState}
    (membership : candidate ∈ state.queue) :
    candidate ∈
      (Certificate.enqueueConsumers consumers conclusion state).queue := by
  unfold Certificate.enqueueConsumers
  split
  · exact membership
  · exact mem_foldl_enqueueWorklist_of_mem
      .dependency _ membership

/-- The concrete consumer table plus sound deduplication guarantees that
marking a premise places every affected certificate link in the real queue. -/
private theorem QueueFlagSound.mem_enqueueConsumers_worklist
    {certificate : Certificate} {state : UnificationWorklistState}
    (sound : QueueFlagSound state)
    (queueSize : state.queued.size = certificate.links.length)
    {link : Link} {linkIndex premise : Nat}
    (lookup : certificate.links[linkIndex]? = some link)
    (premiseBound : premise < certificate.formulas.size)
    (premiseMembership : premise ∈ link.premises) :
    linkIndex ∈
      (Certificate.enqueueConsumers
        (worklistConsumers certificate) premise state).queue := by
  have consumerMembership :=
    mem_worklistConsumers_of_premise lookup premiseBound
      premiseMembership
  have linkBound :
      linkIndex < certificate.links.length :=
    (List.getElem?_eq_some_iff.mp lookup).1
  cases bucketLookup :
      (worklistConsumers certificate)[premise]? with
  | none =>
      simp [bucketLookup] at consumerMembership
  | some indices =>
      unfold Certificate.enqueueConsumers
      rw [bucketLookup]
      apply sound.mem_enqueueMany .dependency indices
      · simpa [bucketLookup] using consumerMembership
      · simpa [queueSize] using linkBound

private def addWaiting (index : Nat)
    (state : UnificationWorklistState) : UnificationWorklistState :=
  if (state.waitingFlags[index]?).getD true then
    state
  else
    { state with
      waiting := index :: state.waiting
      waitingFlags := state.waitingFlags.setIfInBounds index true }

/-- Waiting registration changes neither cumulative queue insertions nor the
concrete queue. -/
private theorem addWaiting_balance
    (index : Nat) (state : UnificationWorklistState) :
    totalWorklistEnqueues
          (Certificate.addWaiting index state).stats +
        state.queue.length =
      totalWorklistEnqueues state.stats +
        (Certificate.addWaiting index state).queue.length := by
  unfold Certificate.addWaiting
  split <;> rfl

/-- Waiting registration changes only scheduler fields. -/
@[simp] private theorem addWaiting_core
    (index : Nat) (state : UnificationWorklistState) :
    (addWaiting index state).core = state.core := by
  unfold addWaiting
  split <;> rfl

/-- Waiting registration does not record a connective firing. -/
@[simp] private theorem addWaiting_successfulFirings
    (index : Nat) (state : UnificationWorklistState) :
    (addWaiting index state).stats.successfulFirings =
      state.stats.successfulFirings := by
  unfold addWaiting
  split <;> rfl

/-- Waiting registration changes no cumulative enqueue counter. -/
@[simp] private theorem addWaiting_stats
    (index : Nat) (state : UnificationWorklistState) :
    (addWaiting index state).stats = state.stats := by
  unfold addWaiting
  split <;> rfl

/-- Waiting registration preserves the waiting-flag carrier. -/
@[simp] private theorem addWaiting_waitingFlags_size
    (index : Nat) (state : UnificationWorklistState) :
    (addWaiting index state).waitingFlags.size =
      state.waitingFlags.size := by
  unfold addWaiting
  split <;> simp

/-- Waiting registration leaves the queue-flag carrier unchanged. -/
@[simp] private theorem addWaiting_queued_size
    (index : Nat) (state : UnificationWorklistState) :
    (addWaiting index state).queued.size =
      state.queued.size := by
  unfold addWaiting
  split <;> rfl

/-- Waiting registration does not change queue flags or the real queue. -/
private theorem QueueFlagSound.addWaiting
    {state : UnificationWorklistState}
    (sound : QueueFlagSound state) (index : Nat) :
    QueueFlagSound (Certificate.addWaiting index state) := by
  intro candidate flagged
  by_cases already : state.waitingFlags[index]?.getD true = true
  · simp [Certificate.addWaiting, already] at flagged ⊢
    exact sound flagged
  · simp [Certificate.addWaiting, already] at flagged ⊢
    exact sound flagged

/-- Waiting registration does not change real-queue bounds. -/
private theorem QueueBounded.addWaiting
    {state : UnificationWorklistState}
    (bounded : QueueBounded state) (index : Nat) :
    QueueBounded (Certificate.addWaiting index state) := by
  intro candidate membership
  by_cases already : state.waitingFlags[index]?.getD true = true
  · simp [Certificate.addWaiting, already] at membership ⊢
    exact bounded membership
  · simp [Certificate.addWaiting, already] at membership ⊢
    exact bounded membership

/-- Waiting registration leaves exact queue flags unchanged. -/
private theorem QueueFlagComplete.addWaiting
    {state : UnificationWorklistState}
    (complete : QueueFlagComplete state) (index : Nat) :
    QueueFlagComplete
      (Certificate.addWaiting index state) := by
  intro candidate membership
  by_cases already : state.waitingFlags[index]?.getD true = true
  · have oldMembership :
        candidate ∈ state.queue := by
      simpa [Certificate.addWaiting, already] using membership
    have oldFlag := complete oldMembership
    simpa [Certificate.addWaiting, already] using oldFlag
  · have oldMembership :
        candidate ∈ state.queue := by
      simpa [Certificate.addWaiting, already] using membership
    have oldFlag := complete oldMembership
    simpa [Certificate.addWaiting, already] using oldFlag

/-- Waiting registration leaves queue uniqueness unchanged. -/
private theorem QueueNodup.addWaiting
    {state : UnificationWorklistState}
    (nodup : QueueNodup state) (index : Nat) :
    QueueNodup
      (Certificate.addWaiting index state) := by
  by_cases already :
      state.waitingFlags[index]?.getD true = true
  · simpa [Certificate.addWaiting, already, QueueNodup] using nodup
  · simpa [Certificate.addWaiting, already, QueueNodup] using nodup

/-- Waiting registration preserves membership-to-flag completeness. -/
private theorem WaitingFlagComplete.addWaiting
    {state : UnificationWorklistState}
    (complete : WaitingFlagComplete state) (index : Nat) :
    WaitingFlagComplete
      (Certificate.addWaiting index state) := by
  intro candidate membership
  by_cases already :
      state.waitingFlags[index]?.getD true = true
  · have oldMembership :
        candidate ∈ state.waiting := by
      simpa [Certificate.addWaiting, already] using membership
    have oldFlag := complete oldMembership
    simpa [Certificate.addWaiting, already] using oldFlag
  · have lookupFalse :
        state.waitingFlags[index]? = some false := by
      cases lookup : state.waitingFlags[index]? with
      | none =>
          simp [lookup] at already
      | some flag =>
          cases flag with
          | false =>
              rfl
          | true =>
              simp [lookup] at already
    have indexBound :
        index < state.waitingFlags.size :=
      (Array.getElem?_eq_some_iff.mp lookupFalse).1
    simp [Certificate.addWaiting, already] at membership
    rcases membership with same | old
    · subst candidate
      have setLookup :
          (state.waitingFlags.setIfInBounds index true)[index]? =
            some true := by
        simp [indexBound]
      simpa [Certificate.addWaiting, already] using setLookup
    · by_cases same : index = candidate
      · subst candidate
        have setLookup :
            (state.waitingFlags.setIfInBounds index true)[index]? =
              some true := by
          simp [indexBound]
        simpa [Certificate.addWaiting, already] using setLookup
      · have oldFlag := complete old
        have setLookup :
            (state.waitingFlags.setIfInBounds index true)[candidate]? =
              some true := by
          simpa [Array.getElem?_setIfInBounds, same] using oldFlag
        simpa [Certificate.addWaiting, already] using setLookup

/-- Exact waiting flags prevent duplicate registry entries. -/
private theorem WaitingNodup.addWaiting
    {state : UnificationWorklistState}
    (nodup : WaitingNodup state)
    (complete : WaitingFlagComplete state) (index : Nat) :
    WaitingNodup
      (Certificate.addWaiting index state) := by
  by_cases already :
      state.waitingFlags[index]?.getD true = true
  · simpa [Certificate.addWaiting, already] using nodup
  · simp [Certificate.addWaiting, already, WaitingNodup]
    constructor
    · intro membership
      have flagged := complete membership
      simp [flagged] at already
    · exact nodup

/-- Waiting registration does not modify exact queue provenance. -/
private theorem QueueConnectiveSound.addWaiting
    {certificate : Certificate} {state : UnificationWorklistState}
    (sound : QueueConnectiveSound certificate state)
    (index : Nat) :
    QueueConnectiveSound certificate
      (Certificate.addWaiting index state) := by
  intro candidate membership
  by_cases already : state.waitingFlags[index]?.getD true = true
  · apply sound
    simpa [Certificate.addWaiting, already] using membership
  · apply sound
    simpa [Certificate.addWaiting, already] using membership

/-- Exact connective provenance plus the submitted-link carrier size implies
ordinary queue bounds. -/
private theorem QueueConnectiveSound.queueBounded
    {certificate : Certificate} {state : UnificationWorklistState}
    (sound : QueueConnectiveSound certificate state)
    (queueSize :
      state.queued.size = certificate.links.length) :
    QueueBounded state := by
  intro index membership
  rcases sound membership with ⟨link, lookup, _connective⟩
  have bound :
      index < certificate.links.length :=
    (List.getElem?_eq_some_iff.mp lookup).1
  simpa [queueSize] using bound

/-- Registering a submitted par preserves the constructor provenance of the
entire waiting registry. -/
private theorem WaitingParSound.addWaiting
    {certificate : Certificate} {state : UnificationWorklistState}
    (sound : WaitingParSound certificate state)
    {index left right conclusion : Nat}
    (lookup :
      certificate.links[index]? =
        some (.par left right conclusion)) :
    WaitingParSound certificate
      (Certificate.addWaiting index state) := by
  intro candidate membership
  by_cases already : state.waitingFlags[index]?.getD true = true
  · simp [Certificate.addWaiting, already] at membership
    exact sound membership
  · simp [Certificate.addWaiting, already] at membership
    rcases membership with same | old
    · subst candidate
      exact ⟨left, right, conclusion, lookup⟩
    · exact sound old

/-- Sound waiting flags make deduplicated registration non-lossy. -/
private theorem WaitingFlagSound.addWaiting
    {state : UnificationWorklistState}
    (sound : WaitingFlagSound state) (index : Nat) :
    WaitingFlagSound (Certificate.addWaiting index state) := by
  intro candidate flagged
  by_cases already : state.waitingFlags[index]?.getD true = true
  · simp [Certificate.addWaiting, already] at flagged ⊢
    exact sound flagged
  · simp [Certificate.addWaiting, already] at flagged ⊢
    by_cases same : index = candidate
    · subst candidate
      simp
    · have oldFlag :
          state.waitingFlags[candidate]? = some true := by
        simpa [Array.getElem?_setIfInBounds, same] using flagged
      exact Or.inr (sound oldFlag)

/-- An in-bounds requested par index is genuinely registered after
`addWaiting`, including the deduplicated case. -/
private theorem WaitingFlagSound.mem_addWaiting
    {state : UnificationWorklistState}
    (sound : WaitingFlagSound state) {index : Nat}
    (bound : index < state.waitingFlags.size) :
    index ∈ (Certificate.addWaiting index state).waiting := by
  cases lookup : state.waitingFlags[index]? with
  | none =>
      have outOfBounds := Array.getElem?_eq_none_iff.mp lookup
      omega
  | some flag =>
      cases flag with
      | false =>
          simp [Certificate.addWaiting, lookup]
      | true =>
          simpa [Certificate.addWaiting, lookup] using sound lookup

/-- Registering an in-bounds par preserves bounds for the waiting registry. -/
private theorem WaitingBounded.addWaiting
    {state : UnificationWorklistState}
    (bounded : WaitingBounded state) {index : Nat}
    (indexBound : index < state.waitingFlags.size) :
    WaitingBounded (Certificate.addWaiting index state) := by
  intro candidate membership
  by_cases already : state.waitingFlags[index]?.getD true = true
  · simp [Certificate.addWaiting, already] at membership ⊢
    exact bounded membership
  · simp [Certificate.addWaiting, already] at membership ⊢
    rcases membership with same | oldMembership
    · subst candidate
      simpa using indexBound
    · simpa using bounded oldMembership

/-- Registering a waiting par preserves all scheduler classifications and
turns the new index into a genuine member of the operational waiting set. -/
private theorem SchedulerCoverage.addWaiting
    {certificate : Certificate} {state : UnificationWorklistState}
    (coverage : SchedulerCoverage certificate state)
    (index : Nat) :
    SchedulerCoverage certificate (addWaiting index state) := by
  intro candidateIndex link lookup connective
  have covered := coverage lookup connective
  unfold Certificate.addWaiting
  split
  · exact covered
  · cases covered with
    | queued membership =>
        exact ConnectiveSchedulerStatus.queued membership
    | firedPar marked =>
        exact ConnectiveSchedulerStatus.firedPar marked
    | firedTensor marked =>
        exact ConnectiveSchedulerStatus.firedTensor marked
    | idlePar idle =>
        exact ConnectiveSchedulerStatus.idlePar idle
    | idleTensor idle =>
        exact ConnectiveSchedulerStatus.idleTensor idle
    | waitingPar leftMarked rightMarked different registered bound =>
        apply ConnectiveSchedulerStatus.waitingPar
        · exact leftMarked
        · exact rightMarked
        · exact different
        · simpa only [List.mem_cons] using
            (show candidateIndex = index ∨
              candidateIndex ∈ state.waiting from Or.inr registered)
        · simpa using bound
    | tensorDeadlock leftMarked rightMarked =>
        exact ConnectiveSchedulerStatus.tensorDeadlock
          leftMarked rightMarked

/-- Waiting registration also preserves coverage when one popped queue head
is temporarily exempt from the scheduler invariant. -/
private theorem SchedulerCoverageExcept.addWaiting
    {certificate : Certificate} {state : UnificationWorklistState}
    {skipped : Nat}
    (coverage : SchedulerCoverageExcept certificate state skipped)
    (index : Nat) :
    SchedulerCoverageExcept certificate
      (addWaiting index state) skipped := by
  intro candidateIndex link lookup connective candidateDifferent
  have covered := coverage lookup connective candidateDifferent
  unfold Certificate.addWaiting
  split
  · exact covered
  · cases covered with
    | queued membership =>
        exact ConnectiveSchedulerStatus.queued membership
    | firedPar marked =>
        exact ConnectiveSchedulerStatus.firedPar marked
    | firedTensor marked =>
        exact ConnectiveSchedulerStatus.firedTensor marked
    | idlePar idle =>
        exact ConnectiveSchedulerStatus.idlePar idle
    | idleTensor idle =>
        exact ConnectiveSchedulerStatus.idleTensor idle
    | waitingPar leftMarked rightMarked different registered bound =>
        apply ConnectiveSchedulerStatus.waitingPar
        · exact leftMarked
        · exact rightMarked
        · exact different
        · simpa only [List.mem_cons] using
            (show candidateIndex = index ∨
              candidateIndex ∈ state.waiting from Or.inr registered)
        · simpa using bound
    | tensorDeadlock leftMarked rightMarked =>
        exact ConnectiveSchedulerStatus.tensorDeadlock
          leftMarked rightMarked

private def requeueWaiting (linkCount : Nat)
    (state : UnificationWorklistState) : UnificationWorklistState :=
  let waiting := state.waiting
  let cleared :=
    { state with
      waiting := []
      waitingFlags := Array.replicate linkCount false }
  waiting.foldl
    (fun next index => enqueueWorklist .waiting index next)
    cleared

/-- Full waiting requeue accounts for every successful reinsertion exactly in
the cumulative enqueue counters. -/
private theorem requeueWaiting_balance
    (linkCount : Nat) (state : UnificationWorklistState) :
    totalWorklistEnqueues
          (Certificate.requeueWaiting linkCount state).stats +
        state.queue.length =
      totalWorklistEnqueues state.stats +
        (Certificate.requeueWaiting linkCount state).queue.length := by
  let cleared : UnificationWorklistState :=
    { state with
      waiting := []
      waitingFlags := Array.replicate linkCount false }
  have folded :=
    foldl_enqueueWorklist_balance
      .waiting state.waiting cleared
  simpa [Certificate.requeueWaiting, cleared] using folded

/-- One full waiting requeue adds at most the old registry length to its
cumulative successful-requeue counter. -/
private theorem requeueWaiting_waitingRequeues_le
    (linkCount : Nat) (state : UnificationWorklistState) :
    (Certificate.requeueWaiting linkCount state).stats.waitingRequeues ≤
      state.stats.waitingRequeues + state.waiting.length := by
  let cleared : UnificationWorklistState :=
    { state with
      waiting := []
      waitingFlags := Array.replicate linkCount false }
  have bound :=
    foldl_enqueueWorklist_waitingRequeues_le state.waiting cleared
  simpa [Certificate.requeueWaiting, cleared] using bound

/-- Waiting requeue cannot change the dependency-insertion counter. -/
@[simp] private theorem requeueWaiting_dependencyEnqueues
    (linkCount : Nat) (state : UnificationWorklistState) :
    (Certificate.requeueWaiting linkCount state).stats.dependencyEnqueues =
      state.stats.dependencyEnqueues := by
  unfold Certificate.requeueWaiting
  simp

/-- Waiting requeue preserves the initialization counter. -/
@[simp] private theorem requeueWaiting_initialEnqueues
    (linkCount : Nat) (state : UnificationWorklistState) :
    (Certificate.requeueWaiting linkCount state).stats.initialEnqueues =
      state.stats.initialEnqueues := by
  unfold Certificate.requeueWaiting
  simp

/-- Requeueing waiting pars changes only scheduler fields. -/
@[simp] private theorem requeueWaiting_core
    (linkCount : Nat) (state : UnificationWorklistState) :
    (requeueWaiting linkCount state).core = state.core := by
  unfold requeueWaiting
  simp

/-- Waiting requeue does not itself record a connective firing. -/
@[simp] private theorem requeueWaiting_successfulFirings
    (linkCount : Nat) (state : UnificationWorklistState) :
    (requeueWaiting linkCount state).stats.successfulFirings =
      state.stats.successfulFirings := by
  unfold requeueWaiting
  simp

/-- Waiting requeue preserves the queue-flag carrier. -/
@[simp] private theorem requeueWaiting_queued_size
    (linkCount : Nat) (state : UnificationWorklistState) :
    (requeueWaiting linkCount state).queued.size =
      state.queued.size := by
  unfold requeueWaiting
  simp

/-- Waiting requeue rebuilds the waiting-flag carrier at the requested link
count. -/
@[simp] private theorem requeueWaiting_waitingFlags_size
    (linkCount : Nat) (state : UnificationWorklistState) :
    ((Certificate.requeueWaiting linkCount state).waitingFlags).size =
      linkCount := by
  unfold Certificate.requeueWaiting
  simp

/-- Clearing the waiting registry and enqueueing all of its former members
preserves sound deduplication flags. -/
private theorem QueueFlagSound.requeueWaiting
    {state : UnificationWorklistState}
    (sound : QueueFlagSound state) (linkCount : Nat) :
    QueueFlagSound
      (Certificate.requeueWaiting linkCount state) := by
  let cleared : UnificationWorklistState :=
    { state with
      waiting := []
      waitingFlags := Array.replicate linkCount false }
  have clearedSound : QueueFlagSound cleared := by
    intro index flagged
    exact sound flagged
  unfold Certificate.requeueWaiting
  change QueueFlagSound
    (state.waiting.foldl
      (fun next index =>
        Certificate.enqueueWorklist .waiting index next)
      cleared)
  exact clearedSound.enqueueMany .waiting state.waiting

/-- Requeueing a bounded waiting registry preserves real-queue bounds when
queue and waiting flag arrays share their submitted-link carrier. -/
private theorem QueueBounded.requeueWaiting
    {state : UnificationWorklistState}
    (queueBounded : QueueBounded state)
    (waitingBounded : WaitingBounded state)
    (sameSize : state.waitingFlags.size = state.queued.size)
    (linkCount : Nat) :
    QueueBounded
      (Certificate.requeueWaiting linkCount state) := by
  let cleared : UnificationWorklistState :=
    { state with
      waiting := []
      waitingFlags := Array.replicate linkCount false }
  have clearedBounded : QueueBounded cleared := by
    intro index membership
    exact queueBounded membership
  unfold Certificate.requeueWaiting
  change QueueBounded
    (state.waiting.foldl
      (fun next index =>
        Certificate.enqueueWorklist .waiting index next)
      cleared)
  apply clearedBounded.enqueueMany .waiting
  intro index membership
  have waitingIndexBound := waitingBounded membership
  simpa [cleared, sameSize] using waitingIndexBound

/-- Requeueing the waiting-par registry preserves exact queue provenance. -/
private theorem QueueConnectiveSound.requeueWaiting
    {certificate : Certificate} {state : UnificationWorklistState}
    (queueSound : QueueConnectiveSound certificate state)
    (waitingSound : WaitingParSound certificate state)
    (linkCount : Nat) :
    QueueConnectiveSound certificate
      (Certificate.requeueWaiting linkCount state) := by
  let cleared : UnificationWorklistState :=
    { state with
      waiting := []
      waitingFlags := Array.replicate linkCount false }
  have clearedSound :
      QueueConnectiveSound certificate cleared := by
    intro index membership
    exact queueSound membership
  unfold Certificate.requeueWaiting
  change QueueConnectiveSound certificate
    (state.waiting.foldl
      (fun next index =>
        Certificate.enqueueWorklist .waiting index next)
      cleared)
  apply clearedSound.enqueueMany .waiting state.waiting
  intro index membership
  rcases waitingSound membership with
    ⟨left, right, conclusion, lookup⟩
  exact
    ⟨.par left right conclusion, lookup, rfl⟩

/-- Requeueing clears the waiting registry, so its par provenance becomes
vacuous. -/
private theorem WaitingParSound.requeueWaiting
    {certificate : Certificate} (state : UnificationWorklistState)
    (linkCount : Nat) :
    WaitingParSound certificate
      (Certificate.requeueWaiting linkCount state) := by
  intro index membership
  simp [Certificate.requeueWaiting] at membership

/-- Waiting requeue preserves exact queue flags. -/
private theorem QueueFlagComplete.requeueWaiting
    {state : UnificationWorklistState}
    (complete : QueueFlagComplete state) (linkCount : Nat) :
    QueueFlagComplete
      (Certificate.requeueWaiting linkCount state) := by
  let cleared : UnificationWorklistState :=
    { state with
      waiting := []
      waitingFlags := Array.replicate linkCount false }
  have clearedComplete : QueueFlagComplete cleared := by
    intro index membership
    apply complete
    exact membership
  unfold Certificate.requeueWaiting
  change QueueFlagComplete
    (state.waiting.foldl
      (fun next index =>
        Certificate.enqueueWorklist .waiting index next)
      cleared)
  exact clearedComplete.enqueueMany .waiting state.waiting

/-- Waiting requeue preserves queue uniqueness. -/
private theorem QueueNodup.requeueWaiting
    {state : UnificationWorklistState}
    (nodup : QueueNodup state)
    (complete : QueueFlagComplete state) (linkCount : Nat) :
    QueueNodup
      (Certificate.requeueWaiting linkCount state) := by
  let cleared : UnificationWorklistState :=
    { state with
      waiting := []
      waitingFlags := Array.replicate linkCount false }
  have clearedNodup : QueueNodup cleared := by
    exact nodup
  have clearedComplete : QueueFlagComplete cleared := by
    intro index membership
    exact complete membership
  unfold Certificate.requeueWaiting
  change QueueNodup
    (state.waiting.foldl
      (fun next index =>
        Certificate.enqueueWorklist .waiting index next)
      cleared)
  exact clearedNodup.enqueueMany .waiting state.waiting
    clearedComplete

/-- Waiting requeue clears the registry, so flag completeness is vacuous. -/
private theorem WaitingFlagComplete.requeueWaiting
    (state : UnificationWorklistState) (linkCount : Nat) :
    WaitingFlagComplete
      (Certificate.requeueWaiting linkCount state) := by
  intro index membership
  simp [Certificate.requeueWaiting] at membership

/-- Waiting requeue clears the registry, so uniqueness is immediate. -/
private theorem WaitingNodup.requeueWaiting
    (state : UnificationWorklistState) (linkCount : Nat) :
    WaitingNodup
      (Certificate.requeueWaiting linkCount state) := by
  simp [Certificate.requeueWaiting, WaitingNodup]

/-- Full waiting requeue resets the waiting flags soundly. -/
private theorem WaitingFlagSound.requeueWaiting
    (state : UnificationWorklistState) (linkCount : Nat) :
    WaitingFlagSound
      (Certificate.requeueWaiting linkCount state) := by
  intro index flagged
  unfold Certificate.requeueWaiting at flagged ⊢
  simp only [foldl_enqueueWorklist_waitingFlags] at flagged
  by_cases bound : index < linkCount
  · have lookup :
        (Array.replicate linkCount false)[index]? = some false := by
      simp [bound]
    rw [lookup] at flagged
    contradiction
  · have lookup :
        (Array.replicate linkCount false)[index]? = none :=
      Array.getElem?_eq_none (by simpa using bound)
    rw [lookup] at flagged
    contradiction

/-- Full waiting requeue empties the waiting registry, hence restores its
boundedness unconditionally. -/
private theorem WaitingBounded.requeueWaiting
    (state : UnificationWorklistState) (linkCount : Nat) :
    WaitingBounded
      (Certificate.requeueWaiting linkCount state) := by
  intro index membership
  unfold Certificate.requeueWaiting at membership
  simp at membership

/-- Requeueing waiting pars preserves every pre-existing real queue member. -/
private theorem mem_requeueWaiting_of_queue_mem
    {state : UnificationWorklistState} {candidate linkCount : Nat}
    (membership : candidate ∈ state.queue) :
    candidate ∈
      (Certificate.requeueWaiting linkCount state).queue := by
  unfold Certificate.requeueWaiting
  exact mem_foldl_enqueueWorklist_of_mem
    .waiting state.waiting membership

/-- A sound, in-bounds waiting registration becomes a real queue member when
the complete waiting registry is requeued. -/
private theorem QueueFlagSound.mem_requeueWaiting_of_waiting
    {state : UnificationWorklistState} {candidate linkCount : Nat}
    (sound : QueueFlagSound state)
    (registered : candidate ∈ state.waiting)
    (bound : candidate < state.queued.size) :
    candidate ∈
      (Certificate.requeueWaiting linkCount state).queue := by
  let cleared : UnificationWorklistState :=
    { state with
      waiting := []
      waitingFlags := Array.replicate linkCount false }
  have clearedSound : QueueFlagSound cleared := by
    intro index flagged
    exact sound flagged
  unfold Certificate.requeueWaiting
  apply clearedSound.mem_enqueueMany .waiting state.waiting
  · exact registered
  · simpa [cleared] using bound

/-- Requeueing the entire waiting-par registry preserves scheduler coverage:
every formerly waiting par becomes a concrete queue member, while queued,
fired, idle, and tensor-deadlock classifications remain valid. -/
private theorem SchedulerCoverage.requeueWaiting
    {certificate : Certificate} {state : UnificationWorklistState}
    (coverage : SchedulerCoverage certificate state)
    (sound : QueueFlagSound state) (linkCount : Nat) :
    SchedulerCoverage certificate
      (Certificate.requeueWaiting linkCount state) := by
  intro candidateIndex link lookup connective
  have covered := coverage lookup connective
  let cleared : UnificationWorklistState :=
    { state with
      waiting := []
      waitingFlags := Array.replicate linkCount false }
  have clearedSound : QueueFlagSound cleared := by
    intro index flagged
    exact sound flagged
  unfold Certificate.requeueWaiting
  cases covered with
  | queued membership =>
      apply ConnectiveSchedulerStatus.queued
      exact mem_foldl_enqueueWorklist_of_mem
        .waiting state.waiting membership
  | firedPar marked =>
      apply ConnectiveSchedulerStatus.firedPar
      simpa using marked
  | firedTensor marked =>
      apply ConnectiveSchedulerStatus.firedTensor
      simpa using marked
  | idlePar idle =>
      apply ConnectiveSchedulerStatus.idlePar
      simpa using idle
  | idleTensor idle =>
      apply ConnectiveSchedulerStatus.idleTensor
      simpa using idle
  | waitingPar leftMarked rightMarked different registered bound =>
      apply ConnectiveSchedulerStatus.queued
      apply clearedSound.mem_enqueueMany .waiting state.waiting
      · exact registered
      · simpa [cleared] using bound
  | tensorDeadlock leftMarked rightMarked =>
      apply ConnectiveSchedulerStatus.tensorDeadlock
      · simpa using leftMarked
      · simpa using rightMarked

private def connectiveIndex? (entry : Link × Nat) : Option Nat :=
  match entry with
  | (.axiom _ _, _) => none
  | (.par _ _ _, index)
  | (.tensor _ _ _, index) => some index

/-- Initial connective indices, in the same reverse certificate order used by
the original enqueue fold.  Defining the queue separately makes its coverage
property available to the proof layer without reasoning through counter and
flag updates at the same time. -/
private def initialWorklistQueue (certificate : Certificate) : List Nat :=
  (certificate.links.zipIdx.filterMap connectiveIndex?).reverse

/-- Every emitted connective index is the second projection of an original
indexed-link entry. -/
private theorem mem_filterMap_connectiveIndex?_map_snd
    {entries : List (Link × Nat)} {index : Nat}
    (membership :
      index ∈ entries.filterMap connectiveIndex?) :
    index ∈ entries.map Prod.snd := by
  simp only [List.mem_filterMap] at membership
  rcases membership with ⟨entry, entryMembership, mapped⟩
  rcases entry with ⟨link, linkIndex⟩
  cases link <;> simp [connectiveIndex?] at mapped
  all_goals
    subst index
    exact List.mem_map.mpr
      ⟨(_, linkIndex), entryMembership, rfl⟩

/-- Filtering indexed links down to connective indices preserves uniqueness
because the original zip indices are unique. -/
private theorem filterMap_connectiveIndex?_nodup
    (entries : List (Link × Nat))
    (indicesNodup : (entries.map Prod.snd).Nodup) :
    (entries.filterMap connectiveIndex?).Nodup := by
  induction entries with
  | nil =>
      simp
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at indicesNodup
      rcases head with ⟨link, linkIndex⟩
      cases link with
      | «axiom» left right =>
          simpa [connectiveIndex?] using
            induction indicesNodup.2
      | «par» left right conclusion =>
          simp only [List.filterMap_cons, connectiveIndex?, List.nodup_cons]
          constructor
          · intro membership
            exact indicesNodup.1
              (mem_filterMap_connectiveIndex?_map_snd membership)
          · exact induction indicesNodup.2
      | «tensor» left right conclusion =>
          simp only [List.filterMap_cons, connectiveIndex?, List.nodup_cons]
          constructor
          · intro membership
            exact indicesNodup.1
              (mem_filterMap_connectiveIndex?_map_snd membership)
          · exact induction indicesNodup.2

/-- The initial queue contains no duplicate connective indices. -/
private theorem initialWorklistQueue_nodup
    (certificate : Certificate) :
    (initialWorklistQueue certificate).Nodup := by
  unfold initialWorklistQueue
  have filtered :
      (certificate.links.zipIdx.filterMap
        connectiveIndex?).Nodup := by
    apply filterMap_connectiveIndex?_nodup
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
      (s := 0) (n := certificate.links.length)
  rw [List.nodup_iff_pairwise_ne] at filtered ⊢
  rw [List.pairwise_reverse]
  exact filtered.imp fun distinct => Ne.symm distinct

/-- Every member of the concrete initial queue is a submitted link index. -/
private theorem mem_initialWorklistQueue_bound
    {certificate : Certificate} {index : Nat}
    (membership : index ∈ initialWorklistQueue certificate) :
    index < certificate.links.length := by
  simp only [initialWorklistQueue, List.mem_reverse,
    List.mem_filterMap] at membership
  rcases membership with ⟨entry, entryMembership, mapped⟩
  rcases entry with ⟨link, linkIndex⟩
  cases link with
  | «axiom» left right =>
      simp [connectiveIndex?] at mapped
  | «par» left right conclusion =>
      simp [connectiveIndex?] at mapped
      subst index
      simpa using List.snd_lt_of_mem_zipIdx entryMembership
  | «tensor» left right conclusion =>
      simp [connectiveIndex?] at mapped
      subst index
      simpa using List.snd_lt_of_mem_zipIdx entryMembership

/-- Every concrete member of the initial work queue is exactly a submitted
connective index. -/
private theorem mem_initialWorklistQueue_submitted_connective
    {certificate : Certificate} {index : Nat}
    (membership : index ∈ initialWorklistQueue certificate) :
    SubmittedConnective certificate index := by
  simp only [initialWorklistQueue, List.mem_reverse,
    List.mem_filterMap] at membership
  rcases membership with ⟨entry, entryMembership, mapped⟩
  rcases entry with ⟨link, linkIndex⟩
  cases link with
  | «axiom» left right =>
      simp [connectiveIndex?] at mapped
  | «par» left right conclusion =>
      simp [connectiveIndex?] at mapped
      subst index
      exact
        ⟨.par left right conclusion,
          List.mk_mem_zipIdx_iff_getElem?.1 entryMembership, rfl⟩
  | «tensor» left right conclusion =>
      simp [connectiveIndex?] at mapped
      subst index
      exact
        ⟨.tensor left right conclusion,
          List.mk_mem_zipIdx_iff_getElem?.1 entryMembership, rfl⟩

/-- Array flags are sound for an allowed queue when every `true` slot names
an element of that queue. -/
private def FlagsSoundFor (flags : Array Bool)
    (allowed : List Nat) : Prop :=
  ∀ {index : Nat}, flags[index]? = some true → index ∈ allowed

/-- A false flag array is sound for every allowed queue. -/
private theorem flagsSoundFor_replicate_false
    (size : Nat) (allowed : List Nat) :
    FlagsSoundFor (Array.replicate size false) allowed := by
  intro index flagged
  by_cases bound : index < size
  · have lookup :
        (Array.replicate size false)[index]? = some false := by
      simp [bound]
    rw [lookup] at flagged
    contradiction
  · have lookup :
        (Array.replicate size false)[index]? = none :=
      Array.getElem?_eq_none (by simpa using bound)
    rw [lookup] at flagged
    contradiction

/-- Setting one allowed flag to true preserves flag soundness. -/
private theorem FlagsSoundFor.setTrue
    {flags : Array Bool} {allowed : List Nat}
    (sound : FlagsSoundFor flags allowed)
    {index : Nat} (allowedMembership : index ∈ allowed) :
    FlagsSoundFor (flags.setIfInBounds index true) allowed := by
  intro candidate flagged
  by_cases same : index = candidate
  · subst candidate
    exact allowedMembership
  · apply sound
    simpa [Array.getElem?_setIfInBounds, same] using flagged

/-- Folding true updates over indices drawn from the allowed queue preserves
flag soundness for that queue. -/
private theorem FlagsSoundFor.foldl_setTrue
    {flags : Array Bool} {allowed indices : List Nat}
    (sound : FlagsSoundFor flags allowed)
    (contained : ∀ index ∈ indices, index ∈ allowed) :
    FlagsSoundFor
      (indices.foldl
        (fun next index => next.setIfInBounds index true)
        flags)
      allowed := by
  induction indices generalizing flags with
  | nil =>
      exact sound
  | cons head tail induction =>
      simp only [List.foldl_cons]
      apply induction
      · apply sound.setTrue
        exact contained head (by simp)
      · intro index membership
        exact contained index (by simp [membership])

/-- Folding bounded flag updates preserves the array carrier. -/
private theorem foldl_setTrue_size
    (indices : List Nat) (flags : Array Bool) :
    (indices.foldl
      (fun next index => next.setIfInBounds index true)
      flags).size = flags.size := by
  induction indices generalizing flags with
  | nil =>
      rfl
  | cons head tail induction =>
      simp only [List.foldl_cons]
      rw [induction]
      simp

/-- Once an in-bounds flag is true, later true updates cannot clear it. -/
private theorem foldl_setTrue_preserves_true
    (indices : List Nat) {flags : Array Bool} {candidate : Nat}
    (lookup : flags[candidate]? = some true) :
    (indices.foldl
      (fun next index => next.setIfInBounds index true)
      flags)[candidate]? = some true := by
  induction indices generalizing flags with
  | nil =>
      exact lookup
  | cons head tail induction =>
      simp only [List.foldl_cons]
      apply induction
      by_cases same : head = candidate
      · subst candidate
        have bound := (Array.getElem?_eq_some_iff.mp lookup).1
        simp [bound]
      · simpa [Array.getElem?_setIfInBounds, same] using lookup

/-- Every in-bounds index explicitly visited by the fold ends with a true
flag. -/
private theorem foldl_setTrue_lookup_of_mem
    (indices : List Nat) (flags : Array Bool)
    {candidate : Nat}
    (membership : candidate ∈ indices)
    (bound : candidate < flags.size) :
    (indices.foldl
      (fun next index => next.setIfInBounds index true)
      flags)[candidate]? = some true := by
  induction indices generalizing flags with
  | nil =>
      simp at membership
  | cons head tail induction =>
      simp only [List.mem_cons] at membership
      simp only [List.foldl_cons]
      rcases membership with rfl | inTail
      · apply foldl_setTrue_preserves_true
        have setLookup :
            (flags.setIfInBounds candidate true)[candidate]? =
              some true := by
          simp [bound]
        exact setLookup
      · apply induction
        · exact inTail
        · simpa using bound

/-- A concrete connective lookup always occurs in the initial queue. -/
private theorem mem_initialWorklistQueue_of_connective
    {certificate : Certificate} {index : Nat} {link : Link}
    (lookup : certificate.links[index]? = some link)
    (connective : link.isConnective = true) :
    index ∈ initialWorklistQueue certificate := by
  cases link with
  | «axiom» left right =>
      simp [Link.isConnective] at connective
  | «par» left right conclusion =>
      simp only [initialWorklistQueue, List.mem_reverse,
        List.mem_filterMap]
      refine ⟨(Link.par left right conclusion, index), ?_, rfl⟩
      exact List.mk_mem_zipIdx_iff_getElem?.2 lookup
  | «tensor» left right conclusion =>
      simp only [initialWorklistQueue, List.mem_reverse,
        List.mem_filterMap]
      refine ⟨(Link.tensor left right conclusion, index), ?_, rfl⟩
      exact List.mk_mem_zipIdx_iff_getElem?.2 lookup

private def initializeWorklist (certificate : Certificate)
    (core : UnificationState) : UnificationWorklistState :=
  let queue := initialWorklistQueue certificate
  let queued :=
    queue.foldl
      (fun flags index => flags.setIfInBounds index true)
      (Array.replicate certificate.links.length false)
  { core
    queue
    queued
    waiting := []
    waitingFlags := Array.replicate certificate.links.length false
    stats :=
      { initialEnqueues := queue.length
        dependencyEnqueues := 0
        waitingRequeues := 0
        linkAttempts := 0
        successfulFirings := 0 } }

/-- Canonical initialization accounts for exactly the concrete queue it
creates. -/
private theorem initializeWorklist_totalEnqueues_eq_queueLength
    (certificate : Certificate) (core : UnificationState) :
    totalWorklistEnqueues
        (initializeWorklist certificate core).stats =
      (initializeWorklist certificate core).queue.length := by
  simp [initializeWorklist, totalWorklistEnqueues]

/-- Canonical initialization starts with an empty connective-firing history
and an exact zero successful-firing counter. -/
private theorem initializeWorklist_firingsAccounted
    (certificate : Certificate) (core : UnificationState) :
    WorklistFiringsAccounted certificate
      (initializeWorklist certificate core) := by
  refine ⟨[], ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp
  · simp [initializeWorklist]

/-- Canonical initialization has no dependency or waiting-requeue source
charges and no successful connective firings. -/
private theorem initializeWorklist_enqueueSourcesBounded
    (certificate : Certificate) (core : UnificationState) :
    WorklistEnqueueSourcesBounded certificate
      (initializeWorklist certificate core) := by
  simp [WorklistEnqueueSourcesBounded, initializeWorklist]

/-- The initial deduplication flags are backed by the concrete initial queue. -/
private theorem initializeWorklist_queueFlagSound
    (certificate : Certificate) (core : UnificationState) :
    QueueFlagSound (initializeWorklist certificate core) := by
  let queue := initialWorklistQueue certificate
  change FlagsSoundFor
    (queue.foldl
      (fun flags index => flags.setIfInBounds index true)
      (Array.replicate certificate.links.length false))
    queue
  apply FlagsSoundFor.foldl_setTrue
  · exact flagsSoundFor_replicate_false _ _
  · intro index membership
    exact membership

/-- Every initial concrete queue member owns its exact true deduplication
flag. -/
private theorem initializeWorklist_queueFlagComplete
    (certificate : Certificate) (core : UnificationState) :
    QueueFlagComplete (initializeWorklist certificate core) := by
  intro index membership
  have queueMembership :
      index ∈ initialWorklistQueue certificate := by
    simpa [initializeWorklist] using membership
  change
    ((initialWorklistQueue certificate).foldl
      (fun flags candidate =>
        flags.setIfInBounds candidate true)
      (Array.replicate certificate.links.length false))[index]? =
        some true
  apply foldl_setTrue_lookup_of_mem
  · exact queueMembership
  · have bound :=
      mem_initialWorklistQueue_bound
        (certificate := certificate) queueMembership
    simpa using bound

/-- The initial concrete queue contains each connective index at most once. -/
private theorem initializeWorklist_queueNodup
    (certificate : Certificate) (core : UnificationState) :
    QueueNodup (initializeWorklist certificate core) := by
  simpa [initializeWorklist, QueueNodup] using
    initialWorklistQueue_nodup certificate

/-- The empty initial waiting registry has sound flags. -/
private theorem initializeWorklist_waitingFlagSound
    (certificate : Certificate) (core : UnificationState) :
    WaitingFlagSound (initializeWorklist certificate core) := by
  change FlagsSoundFor
    (Array.replicate certificate.links.length false) []
  exact flagsSoundFor_replicate_false _ _

/-- Waiting-flag completeness is vacuous for the empty initial registry. -/
private theorem initializeWorklist_waitingFlagComplete
    (certificate : Certificate) (core : UnificationState) :
    WaitingFlagComplete (initializeWorklist certificate core) := by
  intro index membership
  simp [initializeWorklist] at membership

/-- The empty initial waiting registry contains no duplicates. -/
private theorem initializeWorklist_waitingNodup
    (certificate : Certificate) (core : UnificationState) :
    WaitingNodup (initializeWorklist certificate core) := by
  simp [initializeWorklist, WaitingNodup]

/-- The empty initial waiting registry is vacuously bounded. -/
private theorem initializeWorklist_waitingBounded
    (certificate : Certificate) (core : UnificationState) :
    WaitingBounded (initializeWorklist certificate core) := by
  intro index membership
  simp [initializeWorklist] at membership

/-- Every initial real queue member addresses a valid submitted-link flag. -/
private theorem initializeWorklist_queueBounded
    (certificate : Certificate) (core : UnificationState) :
    QueueBounded (initializeWorklist certificate core) := by
  intro index membership
  have linkBound :=
    mem_initialWorklistQueue_bound
      (certificate := certificate) membership
  simpa [initializeWorklist, foldl_setTrue_size] using linkBound

/-- The initial queue contains exactly submitted connective indices. -/
private theorem initializeWorklist_queueConnectiveSound
    (certificate : Certificate) (core : UnificationState) :
    QueueConnectiveSound certificate
      (initializeWorklist certificate core) := by
  intro index membership
  apply mem_initialWorklistQueue_submitted_connective
  simpa [initializeWorklist] using membership

/-- The initial waiting registry is empty and therefore has exact par
provenance. -/
private theorem initializeWorklist_waitingParSound
    (certificate : Certificate) (core : UnificationState) :
    WaitingParSound certificate
      (initializeWorklist certificate core) := by
  intro index membership
  simp [initializeWorklist] at membership

/-- Initial queue flags have exactly one slot per submitted link. -/
private theorem initializeWorklist_queued_size
    (certificate : Certificate) (core : UnificationState) :
    (initializeWorklist certificate core).queued.size =
      certificate.links.length := by
  simp only [initializeWorklist]
  rw [foldl_setTrue_size]
  simp

/-- Initial waiting flags have exactly one slot per submitted link. -/
private theorem initializeWorklist_waitingFlags_size
    (certificate : Certificate) (core : UnificationState) :
    (initializeWorklist certificate core).waitingFlags.size =
      certificate.links.length := by
  simp [initializeWorklist]

/-- Initial arming establishes scheduler coverage for every connective,
independently of token readiness. -/
private theorem initializeWorklist_schedulerCoverage
    (certificate : Certificate) (core : UnificationState) :
    SchedulerCoverage certificate
      (initializeWorklist certificate core) := by
  intro index link lookup connective
  apply ConnectiveSchedulerStatus.queued
  simpa [initializeWorklist] using
    mem_initialWorklistQueue_of_connective lookup connective

private def popWorklist? (state : UnificationWorklistState) :
    Option (Nat × UnificationWorklistState) :=
  match state.queue with
  | [] => none
  | index :: rest =>
      some (index,
        { state with
          queue := rest
          queued := state.queued.setIfInBounds index false })

/-- Popping a bounded, sound real queue yields an in-bounds link index and
preserves both invariants after clearing exactly that head flag. -/
private theorem popWorklist?_some_invariants
    {state popped : UnificationWorklistState} {index : Nat}
    (sound : QueueFlagSound state)
    (bounded : QueueBounded state)
    (equation : popWorklist? state = some (index, popped)) :
    index < state.queued.size ∧
      QueueFlagSound popped ∧
      QueueBounded popped := by
  cases queueEquation : state.queue with
  | nil =>
      simp [popWorklist?, queueEquation] at equation
  | cons head rest =>
      have poppedEquation :
          popped =
            { state with
              queue := rest
              queued := state.queued.setIfInBounds head false } := by
        simp [popWorklist?, queueEquation] at equation
        exact equation.2.symm
      have indexEquation : index = head := by
        simp [popWorklist?, queueEquation] at equation
        exact equation.1.symm
      subst index
      subst popped
      have headBound : head < state.queued.size := by
        apply bounded
        rw [queueEquation]
        simp
      refine ⟨headBound, ?_, ?_⟩
      · intro candidate flagged
        by_cases same : head = candidate
        · subst candidate
          simp [headBound] at flagged
        · have oldFlag :
              state.queued[candidate]? = some true := by
            simpa [Array.getElem?_setIfInBounds, same] using flagged
          have oldMembership := sound oldFlag
          rw [queueEquation] at oldMembership
          simp only [List.mem_cons] at oldMembership
          rcases oldMembership with candidateHead | inRest
          · exact False.elim (same candidateHead.symm)
          · exact inRest
      · intro candidate membership
        have oldMembership : candidate ∈ state.queue := by
          rw [queueEquation]
          exact List.mem_cons_of_mem head membership
        have oldBound := bounded oldMembership
        simpa using oldBound

/-- Popping exact scheduler work exposes a submitted connective and preserves
queue/waiting provenance in the residual state. -/
private theorem popWorklist?_some_provenance
    {certificate : Certificate}
    {state popped : UnificationWorklistState} {index : Nat}
    (queueSound : QueueConnectiveSound certificate state)
    (waitingSound : WaitingParSound certificate state)
    (equation : popWorklist? state = some (index, popped)) :
    SubmittedConnective certificate index ∧
      QueueConnectiveSound certificate popped ∧
      WaitingParSound certificate popped := by
  cases queueEquation : state.queue with
  | nil =>
      simp [popWorklist?, queueEquation] at equation
  | cons head rest =>
      simp [popWorklist?, queueEquation] at equation
      rcases equation with ⟨rfl, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · apply queueSound
        rw [queueEquation]
        simp
      · intro candidate membership
        apply queueSound
        rw [queueEquation]
        exact List.mem_cons_of_mem head membership
      · intro candidate membership
        apply waitingSound
        exact membership

/-- Popping changes neither waiting state nor array carriers, and therefore
preserves waiting-flag soundness exactly. -/
private theorem popWorklist?_success_bookkeeping
    {state popped : UnificationWorklistState} {index : Nat}
    (waitingSound : WaitingFlagSound state)
    (equation : popWorklist? state = some (index, popped)) :
    WaitingFlagSound popped ∧
      popped.queued.size = state.queued.size ∧
      popped.waitingFlags.size = state.waitingFlags.size := by
  cases queueEquation : state.queue with
  | nil =>
      simp [popWorklist?, queueEquation] at equation
  | cons head rest =>
      simp [popWorklist?, queueEquation] at equation
      rcases equation with ⟨rfl, rfl⟩
      refine ⟨?_, by simp, rfl⟩
      intro candidate flagged
      have oldFlag :
          state.waitingFlags[candidate]? = some true := by
        simpa using flagged
      have oldMembership := waitingSound oldFlag
      simpa using oldMembership

/-- Popping one queue head preserves exact queue/waiting flag completeness
and uniqueness. -/
private theorem popWorklist?_success_exactDiscipline
    {state popped : UnificationWorklistState} {index : Nat}
    (queueComplete : QueueFlagComplete state)
    (queueNodup : QueueNodup state)
    (waitingComplete : WaitingFlagComplete state)
    (waitingNodup : WaitingNodup state)
    (equation : popWorklist? state = some (index, popped)) :
    QueueFlagComplete popped ∧
      QueueNodup popped ∧
        WaitingFlagComplete popped ∧
          WaitingNodup popped := by
  cases queueEquation : state.queue with
  | nil =>
      simp [popWorklist?, queueEquation] at equation
  | cons head rest =>
      simp [popWorklist?, queueEquation] at equation
      rcases equation with ⟨rfl, rfl⟩
      have oldQueueNodup :
          (head :: rest).Nodup := by
        simpa [QueueNodup, queueEquation] using queueNodup
      have restNodup := (List.nodup_cons.mp oldQueueNodup).2
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro candidate membership
        have oldMembership :
            candidate ∈ state.queue := by
          rw [queueEquation]
          exact List.mem_cons_of_mem head membership
        have oldFlag := queueComplete oldMembership
        have distinct : head ≠ candidate := by
          intro same
          subst candidate
          exact (List.nodup_cons.mp oldQueueNodup).1 membership
        simpa [Array.getElem?_setIfInBounds, distinct] using oldFlag
      · simpa [QueueNodup] using restNodup
      · intro candidate membership
        have oldFlag := waitingComplete membership
        simpa using oldFlag
      · simpa [WaitingNodup] using waitingNodup

/-- A successful pop consumes exactly one concrete queue entry and changes no
cumulative enqueue counter. -/
private theorem popWorklist?_success_balance
    {state popped : UnificationWorklistState} {index : Nat}
    (equation : popWorklist? state = some (index, popped)) :
    totalWorklistEnqueues popped.stats =
        totalWorklistEnqueues state.stats ∧
      state.queue.length = popped.queue.length + 1 := by
  cases queueEquation : state.queue with
  | nil =>
      simp [popWorklist?, queueEquation] at equation
  | cons head rest =>
      simp [popWorklist?, queueEquation] at equation
      rcases equation with ⟨rfl, rfl⟩
      simp [totalWorklistEnqueues]

/-- Popping one queue head preserves every other connective's scheduler
classification.  The removed index is the unique temporary hole repaired by
`processWorklistLink_processed_status`. -/
private theorem popWorklist?_success_schedulerCoverageExcept
    {certificate : Certificate}
    {state popped : UnificationWorklistState} {index : Nat}
    (coverage : SchedulerCoverage certificate state)
    (equation : popWorklist? state = some (index, popped)) :
    SchedulerCoverageExcept certificate popped index := by
  cases queueEquation : state.queue with
  | nil =>
      simp [popWorklist?, queueEquation] at equation
  | cons head rest =>
      simp [popWorklist?, queueEquation] at equation
      rcases equation with ⟨rfl, rfl⟩
      intro candidateIndex link lookup connective different
      have covered := coverage lookup connective
      cases covered with
      | queued membership =>
          apply ConnectiveSchedulerStatus.queued
          rw [queueEquation] at membership
          simp only [List.mem_cons] at membership
          rcases membership with same | inRest
          · exact False.elim (different same)
          · exact inRest
      | firedPar marked =>
          apply ConnectiveSchedulerStatus.firedPar
          simpa using marked
      | firedTensor marked =>
          apply ConnectiveSchedulerStatus.firedTensor
          simpa using marked
      | idlePar idle =>
          apply ConnectiveSchedulerStatus.idlePar
          simpa using idle
      | idleTensor idle =>
          apply ConnectiveSchedulerStatus.idleTensor
          simpa using idle
      | waitingPar leftMarked rightMarked
          tokensDifferent registered bound =>
          apply ConnectiveSchedulerStatus.waitingPar
          · simpa using leftMarked
          · simpa using rightMarked
          · exact tokensDifferent
          · exact registered
          · simpa using bound
      | tensorDeadlock leftMarked rightMarked =>
          apply ConnectiveSchedulerStatus.tensorDeadlock
          · simpa using leftMarked
          · simpa using rightMarked

private def recordWorklistFiring (state : UnificationWorklistState) :
    UnificationWorklistState :=
  { state with
    stats :=
      { state.stats with
        successfulFirings := state.stats.successfulFirings + 1 } }

/-- Recording a firing changes neither cumulative queue insertions nor the
concrete queue. -/
private theorem recordWorklistFiring_balance
    (state : UnificationWorklistState) :
    totalWorklistEnqueues (recordWorklistFiring state).stats +
        state.queue.length =
      totalWorklistEnqueues state.stats +
        (recordWorklistFiring state).queue.length := by
  simp [recordWorklistFiring, totalWorklistEnqueues]

/-- Replacing only the executable core and recording its successful firing is
neutral for cumulative queue insertion accounting. -/
private theorem coreUpdate_recordWorklistFiring_balance
    (state : UnificationWorklistState) (nextCore : UnificationState) :
    QueueInsertionBalanced state
      (recordWorklistFiring { state with core := nextCore }) := by
  simp [QueueInsertionBalanced, recordWorklistFiring,
    totalWorklistEnqueues]

/-- Recording a successful scheduler event leaves the parser core unchanged. -/
@[simp] private theorem recordWorklistFiring_core
    (state : UnificationWorklistState) :
    (recordWorklistFiring state).core = state.core :=
  rfl

/-- Recording a firing preserves both cumulative enqueue-source counters and
increments the successful-firing counter exactly once. -/
private theorem recordWorklistFiring_sourceCounters
    (state : UnificationWorklistState) :
    (recordWorklistFiring state).stats.dependencyEnqueues =
        state.stats.dependencyEnqueues ∧
      (recordWorklistFiring state).stats.waitingRequeues =
        state.stats.waitingRequeues ∧
      (recordWorklistFiring state).stats.successfulFirings =
        state.stats.successfulFirings + 1 := by
  simp [recordWorklistFiring]

@[simp] private theorem recordWorklistFiring_dependencyEnqueues
    (state : UnificationWorklistState) :
    (recordWorklistFiring state).stats.dependencyEnqueues =
      state.stats.dependencyEnqueues := by
  simp [recordWorklistFiring]

@[simp] private theorem recordWorklistFiring_waitingRequeues
    (state : UnificationWorklistState) :
    (recordWorklistFiring state).stats.waitingRequeues =
      state.stats.waitingRequeues := by
  simp [recordWorklistFiring]

@[simp] private theorem recordWorklistFiring_successfulFirings
    (state : UnificationWorklistState) :
    (recordWorklistFiring state).stats.successfulFirings =
      state.stats.successfulFirings + 1 := by
  simp [recordWorklistFiring]

@[simp] private theorem recordWorklistFiring_initialEnqueues
    (state : UnificationWorklistState) :
    (recordWorklistFiring state).stats.initialEnqueues =
      state.stats.initialEnqueues := by
  simp [recordWorklistFiring]

/-- A successful par event extends the proof-only firing history by one fresh
submitted link. Freshness follows from the executable conclusion-ready guard,
not from the counter itself. -/
private theorem WorklistFiringsAccounted.afterFirePar
    {certificate : Certificate}
    {state : UnificationWorklistState}
    {next : UnificationState}
    {left right conclusion : Vertex}
    (accounted : WorklistFiringsAccounted certificate state)
    (abstractable : state.core.Abstractable certificate)
    (submitted :
      Link.par left right conclusion ∈ certificate.links)
    (conclusionBound : conclusion < certificate.formulas.size)
    (equation :
      firePar? state.core left right conclusion = some next) :
    WorklistFiringsAccounted certificate
      (recordWorklistFiring { state with core := next }) := by
  rcases accounted with
    ⟨history, historyNodup, historySubmitted,
      historyFired, countExact⟩
  rcases firePar?_success_observation equation with
    ⟨outputToken, forwardEquation, _observation⟩
  have conclusionReady :
      state.core.marks[conclusion]? = some none :=
    (state.core.forwardToken?_success forwardEquation).1
  have fresh :
      Link.par left right conclusion ∉ history := by
    intro membership
    have previouslyFired :=
      historyFired
        (.par left right conclusion) membership
    change state.core.marks[conclusion]?.join ≠ none at previouslyFired
    rw [conclusionReady] at previouslyFired
    exact previouslyFired rfl
  exact
    ⟨Link.par left right conclusion :: history,
      List.nodup_cons.mpr ⟨fresh, historyNodup⟩, by
      intro link membership
      rcases List.mem_cons.mp membership with same | old
      · simpa [same] using submitted
      · exact historySubmitted link old, by
      intro link membership
      rcases List.mem_cons.mp membership with same | old
      · subst link
        simpa [linkFiredIn, recordWorklistFiring] using
          firePar?_success_conclusion_marked
            abstractable conclusionBound equation
      · have oldFired := historyFired link old
        cases link with
        | «axiom» axiomLeft axiomRight =>
            exact oldFired
        | «par» oldLeft oldRight oldConclusion =>
            simpa [linkFiredIn, recordWorklistFiring] using
              firePar?_success_preserves_assigned
                abstractable conclusionBound oldFired equation
        | «tensor» oldLeft oldRight oldConclusion =>
            simpa [linkFiredIn, recordWorklistFiring] using
              firePar?_success_preserves_assigned
                abstractable conclusionBound oldFired equation
      , by
        simp [recordWorklistFiring, countExact]⟩

/-- A successful tensor event extends the same distinct submitted-link
history; representative merging never removes an older conclusion mark. -/
private theorem WorklistFiringsAccounted.afterFireTensor
    {certificate : Certificate}
    {state : UnificationWorklistState}
    {next : UnificationState}
    {left right conclusion : Vertex}
    (accounted : WorklistFiringsAccounted certificate state)
    (abstractable : state.core.Abstractable certificate)
    (submitted :
      Link.tensor left right conclusion ∈ certificate.links)
    (conclusionBound : conclusion < certificate.formulas.size)
    (equation :
      fireTensor? state.core left right conclusion = some next) :
    WorklistFiringsAccounted certificate
      (recordWorklistFiring { state with core := next }) := by
  rcases accounted with
    ⟨history, historyNodup, historySubmitted,
      historyFired, countExact⟩
  rcases fireTensor?_success_observation equation with
    ⟨leftToken, rightToken, unifyEquation, _observation⟩
  have conclusionReady :
      state.core.marks[conclusion]? = some none :=
    (state.core.unifyTokens?_success unifyEquation).1
  have fresh :
      Link.tensor left right conclusion ∉ history := by
    intro membership
    have previouslyFired :=
      historyFired
        (.tensor left right conclusion) membership
    change state.core.marks[conclusion]?.join ≠ none at previouslyFired
    rw [conclusionReady] at previouslyFired
    exact previouslyFired rfl
  exact
    ⟨Link.tensor left right conclusion :: history,
      List.nodup_cons.mpr ⟨fresh, historyNodup⟩, by
      intro link membership
      rcases List.mem_cons.mp membership with same | old
      · simpa [same] using submitted
      · exact historySubmitted link old, by
      intro link membership
      rcases List.mem_cons.mp membership with same | old
      · subst link
        simpa [linkFiredIn, recordWorklistFiring] using
          fireTensor?_success_conclusion_marked
            abstractable conclusionBound equation
      · have oldFired := historyFired link old
        cases link with
        | «axiom» axiomLeft axiomRight =>
            exact oldFired
        | «par» oldLeft oldRight oldConclusion =>
            simpa [linkFiredIn, recordWorklistFiring] using
              fireTensor?_success_preserves_assigned
                abstractable conclusionBound oldFired equation
        | «tensor» oldLeft oldRight oldConclusion =>
            simpa [linkFiredIn, recordWorklistFiring] using
              fireTensor?_success_preserves_assigned
                abstractable conclusionBound oldFired equation
      , by
        simp [recordWorklistFiring, countExact]⟩

/-- Broadcasting a successfully fired par conclusion transports scheduler
coverage for every submitted connective.  Existing queue members remain
queued; old fired conclusions remain marked; unaffected idle/waiting/deadlock
statuses are stable because par does not change representatives; and every
status whose premise is the new conclusion becomes a concrete dependency
queue member through the exact consumer table. -/
private theorem SchedulerCoverageExcept.afterFirePar
    {certificate : Certificate} {state : UnificationWorklistState}
    {next : UnificationState}
    {left right conclusion : Vertex} {skipped : Nat}
    (structural : certificate.StructurallyWellFormed)
    (abstractable : state.core.Abstractable certificate)
    (coverage :
      SchedulerCoverageExcept certificate state skipped)
    (queueSound : QueueFlagSound state)
    (queueSize : state.queued.size = certificate.links.length)
    (firedMembership :
      Link.par left right conclusion ∈ certificate.links)
    (equation :
      firePar? state.core left right conclusion = some next) :
    SchedulerCoverageExcept certificate
      (Certificate.enqueueConsumers
        certificate.worklistConsumers conclusion <|
        recordWorklistFiring { state with core := next })
      skipped := by
  have firedWellFormed :
      certificate.LinkWellFormed
        (.par left right conclusion) :=
    structural.2.2.2.2.1 _ firedMembership
  rcases firedWellFormed with
    ⟨_premisesDifferent, _leftConclusionDifferent,
      _rightConclusionDifferent, _leftBound, _rightBound,
      conclusionBound, _typing⟩
  let firedState : UnificationWorklistState :=
    recordWorklistFiring { state with core := next }
  have firedQueueSound : QueueFlagSound firedState := by
    intro index flagged
    apply queueSound
    simpa [firedState, recordWorklistFiring] using flagged
  have firedQueueSize :
      firedState.queued.size = certificate.links.length := by
    simpa [firedState, recordWorklistFiring] using queueSize
  intro candidateIndex link lookup connective candidateDifferent
  have covered := coverage lookup connective candidateDifferent
  have queuedOfPremise
      (premiseMembership : conclusion ∈ link.premises) :
      ConnectiveSchedulerStatus
        (Certificate.enqueueConsumers
          certificate.worklistConsumers conclusion
          firedState)
        candidateIndex link := by
    apply ConnectiveSchedulerStatus.queued
    exact firedQueueSound.mem_enqueueConsumers_worklist
      firedQueueSize lookup conclusionBound premiseMembership
  cases covered with
  | queued membership =>
      apply ConnectiveSchedulerStatus.queued
      apply mem_enqueueConsumers_of_mem
      simpa [firedState, recordWorklistFiring] using membership
  | firedPar marked =>
      apply ConnectiveSchedulerStatus.firedPar
      have nextMarked :=
        firePar?_success_preserves_assigned
          abstractable conclusionBound marked equation
      simpa [firedState] using nextMarked
  | firedTensor marked =>
      apply ConnectiveSchedulerStatus.firedTensor
      have nextMarked :=
        firePar?_success_preserves_assigned
          abstractable conclusionBound marked equation
      simpa [firedState] using nextMarked
  | @idlePar candidateLeft candidateRight
      candidateConclusion idle =>
      rcases idle with leftIdle | rightIdle
      · by_cases affected : candidateLeft = conclusion
        · apply queuedOfPremise
          subst candidateLeft
          simp [Link.premises]
        · apply ConnectiveSchedulerStatus.idlePar
          apply Or.inl
          have nextIdle :
              next.tokenAt? candidateLeft = none := by
            rw [firePar?_success_tokenAt?_of_ne affected equation]
            exact leftIdle
          simpa [firedState] using nextIdle
      · by_cases affected : candidateRight = conclusion
        · apply queuedOfPremise
          subst candidateRight
          simp [Link.premises]
        · apply ConnectiveSchedulerStatus.idlePar
          apply Or.inr
          have nextIdle :
              next.tokenAt? candidateRight = none := by
            rw [firePar?_success_tokenAt?_of_ne affected equation]
            exact rightIdle
          simpa [firedState] using nextIdle
  | @idleTensor candidateLeft candidateRight
      candidateConclusion idle =>
      rcases idle with leftIdle | rightIdle
      · by_cases affected : candidateLeft = conclusion
        · apply queuedOfPremise
          subst candidateLeft
          simp [Link.premises]
        · apply ConnectiveSchedulerStatus.idleTensor
          apply Or.inl
          have nextIdle :
              next.tokenAt? candidateLeft = none := by
            rw [firePar?_success_tokenAt?_of_ne affected equation]
            exact leftIdle
          simpa [firedState] using nextIdle
      · by_cases affected : candidateRight = conclusion
        · apply queuedOfPremise
          subst candidateRight
          simp [Link.premises]
        · apply ConnectiveSchedulerStatus.idleTensor
          apply Or.inr
          have nextIdle :
              next.tokenAt? candidateRight = none := by
            rw [firePar?_success_tokenAt?_of_ne affected equation]
            exact rightIdle
          simpa [firedState] using nextIdle
  | @waitingPar candidateLeft candidateRight
      candidateConclusion leftToken rightToken
      leftMarked rightMarked different registered bound =>
      by_cases leftAffected : candidateLeft = conclusion
      · apply queuedOfPremise
        subst candidateLeft
        simp [Link.premises]
      · by_cases rightAffected : candidateRight = conclusion
        · apply queuedOfPremise
          subst candidateRight
          simp [Link.premises]
        · apply ConnectiveSchedulerStatus.waitingPar
          · have nextLeft :
                next.tokenAt? candidateLeft =
                  some leftToken := by
              rw [firePar?_success_tokenAt?_of_ne
                leftAffected equation]
              exact leftMarked
            simpa [firedState] using nextLeft
          · have nextRight :
                next.tokenAt? candidateRight =
                  some rightToken := by
              rw [firePar?_success_tokenAt?_of_ne
                rightAffected equation]
              exact rightMarked
            simpa [firedState] using nextRight
          · exact different
          · simpa [firedState, recordWorklistFiring] using
              registered
          · simpa [firedState, recordWorklistFiring] using bound
  | @tensorDeadlock candidateLeft candidateRight
      candidateConclusion token leftMarked rightMarked =>
      by_cases leftAffected : candidateLeft = conclusion
      · apply queuedOfPremise
        subst candidateLeft
        simp [Link.premises]
      · by_cases rightAffected : candidateRight = conclusion
        · apply queuedOfPremise
          subst candidateRight
          simp [Link.premises]
        · apply ConnectiveSchedulerStatus.tensorDeadlock
          · have nextLeft :
                next.tokenAt? candidateLeft = some token := by
              rw [firePar?_success_tokenAt?_of_ne
                leftAffected equation]
              exact leftMarked
            simpa [firedState] using nextLeft
          · have nextRight :
                next.tokenAt? candidateRight = some token := by
              rw [firePar?_success_tokenAt?_of_ne
                rightAffected equation]
              exact rightMarked
            simpa [firedState] using nextRight

/-- Broadcasting a successful tensor conclusion also transports complete
scheduler coverage.  Tensor firing first requeues every waiting par, so the
only token-semantic cases that must be transported directly are fired marks,
unaffected idle premises, and an old tensor deadlock.  The ordered union-find
theorem above ensures that the root union cannot split that old deadlock. -/
private theorem SchedulerCoverageExcept.afterFireTensor
    {certificate : Certificate} {state : UnificationWorklistState}
    {next : UnificationState}
    {left right conclusion : Vertex} {skipped : Nat}
    (structural : certificate.StructurallyWellFormed)
    (abstractable : state.core.Abstractable certificate)
    (ordered : state.core.OrderedParents)
    (coverage :
      SchedulerCoverageExcept certificate state skipped)
    (queueSound : QueueFlagSound state)
    (queueSize : state.queued.size = certificate.links.length)
    (firedMembership :
      Link.tensor left right conclusion ∈ certificate.links)
    (equation :
      fireTensor? state.core left right conclusion = some next) :
    SchedulerCoverageExcept certificate
      (Certificate.enqueueConsumers
        certificate.worklistConsumers conclusion <|
          Certificate.requeueWaiting certificate.links.length <|
            recordWorklistFiring { state with core := next })
      skipped := by
  have firedWellFormed :
      certificate.LinkWellFormed
        (.tensor left right conclusion) :=
    structural.2.2.2.2.1 _ firedMembership
  rcases firedWellFormed with
    ⟨_premisesDifferent, _leftConclusionDifferent,
      _rightConclusionDifferent, _leftBound, _rightBound,
      conclusionBound, _typing⟩
  let firedState : UnificationWorklistState :=
    recordWorklistFiring { state with core := next }
  let requeuedState : UnificationWorklistState :=
    Certificate.requeueWaiting certificate.links.length firedState
  have firedQueueSound : QueueFlagSound firedState := by
    intro index flagged
    apply queueSound
    simpa [firedState, recordWorklistFiring] using flagged
  have firedQueueSize :
      firedState.queued.size = certificate.links.length := by
    simpa [firedState, recordWorklistFiring] using queueSize
  have requeuedQueueSound : QueueFlagSound requeuedState := by
    exact firedQueueSound.requeueWaiting certificate.links.length
  have requeuedQueueSize :
      requeuedState.queued.size = certificate.links.length := by
    simpa [requeuedState] using firedQueueSize
  intro candidateIndex link lookup connective candidateDifferent
  have covered := coverage lookup connective candidateDifferent
  have queuedOfPremise
      (premiseMembership : conclusion ∈ link.premises) :
      ConnectiveSchedulerStatus
        (Certificate.enqueueConsumers
          certificate.worklistConsumers conclusion requeuedState)
        candidateIndex link := by
    apply ConnectiveSchedulerStatus.queued
    exact requeuedQueueSound.mem_enqueueConsumers_worklist
      requeuedQueueSize lookup conclusionBound premiseMembership
  cases covered with
  | queued membership =>
      apply ConnectiveSchedulerStatus.queued
      apply mem_enqueueConsumers_of_mem
      apply mem_requeueWaiting_of_queue_mem
      simpa [firedState, recordWorklistFiring] using membership
  | firedPar marked =>
      apply ConnectiveSchedulerStatus.firedPar
      have nextMarked :=
        fireTensor?_success_preserves_assigned
          abstractable conclusionBound marked equation
      simpa [requeuedState, firedState] using nextMarked
  | firedTensor marked =>
      apply ConnectiveSchedulerStatus.firedTensor
      have nextMarked :=
        fireTensor?_success_preserves_assigned
          abstractable conclusionBound marked equation
      simpa [requeuedState, firedState] using nextMarked
  | @idlePar candidateLeft candidateRight
      candidateConclusion idle =>
      rcases idle with leftIdle | rightIdle
      · by_cases affected : candidateLeft = conclusion
        · apply queuedOfPremise
          subst candidateLeft
          simp [Link.premises]
        · apply ConnectiveSchedulerStatus.idlePar
          apply Or.inl
          have nextIdle :
              next.tokenAt? candidateLeft = none :=
            fireTensor?_success_tokenAt?_none_of_ne
              affected leftIdle equation
          simpa [requeuedState, firedState] using nextIdle
      · by_cases affected : candidateRight = conclusion
        · apply queuedOfPremise
          subst candidateRight
          simp [Link.premises]
        · apply ConnectiveSchedulerStatus.idlePar
          apply Or.inr
          have nextIdle :
              next.tokenAt? candidateRight = none :=
            fireTensor?_success_tokenAt?_none_of_ne
              affected rightIdle equation
          simpa [requeuedState, firedState] using nextIdle
  | @idleTensor candidateLeft candidateRight
      candidateConclusion idle =>
      rcases idle with leftIdle | rightIdle
      · by_cases affected : candidateLeft = conclusion
        · apply queuedOfPremise
          subst candidateLeft
          simp [Link.premises]
        · apply ConnectiveSchedulerStatus.idleTensor
          apply Or.inl
          have nextIdle :
              next.tokenAt? candidateLeft = none :=
            fireTensor?_success_tokenAt?_none_of_ne
              affected leftIdle equation
          simpa [requeuedState, firedState] using nextIdle
      · by_cases affected : candidateRight = conclusion
        · apply queuedOfPremise
          subst candidateRight
          simp [Link.premises]
        · apply ConnectiveSchedulerStatus.idleTensor
          apply Or.inr
          have nextIdle :
              next.tokenAt? candidateRight = none :=
            fireTensor?_success_tokenAt?_none_of_ne
              affected rightIdle equation
          simpa [requeuedState, firedState] using nextIdle
  | @waitingPar candidateLeft candidateRight
      candidateConclusion leftToken rightToken
      leftMarked rightMarked different registered bound =>
      apply ConnectiveSchedulerStatus.queued
      apply mem_enqueueConsumers_of_mem
      have firedRegistered :
          candidateIndex ∈ firedState.waiting := by
        simpa [firedState, recordWorklistFiring] using registered
      have firedBound :
          candidateIndex < firedState.queued.size := by
        simpa [firedState, recordWorklistFiring] using bound
      exact firedQueueSound.mem_requeueWaiting_of_waiting
        firedRegistered firedBound
  | @tensorDeadlock candidateLeft candidateRight
      candidateConclusion token leftMarked rightMarked =>
      by_cases leftAffected : candidateLeft = conclusion
      · apply queuedOfPremise
        subst candidateLeft
        simp [Link.premises]
      · by_cases rightAffected : candidateRight = conclusion
        · apply queuedOfPremise
          subst candidateRight
          simp [Link.premises]
        · rcases fireTensor?_success_same_tokenAt?_of_ne
              abstractable ordered leftAffected rightAffected
              leftMarked rightMarked equation with
            ⟨nextToken, nextLeft, nextRight⟩
          apply ConnectiveSchedulerStatus.tensorDeadlock
          · simpa [requeuedState, firedState] using nextLeft
          · simpa [requeuedState, firedState] using nextRight

private def processWorklistLink (certificate : Certificate)
    (consumers : Array (List Nat)) (index : Nat)
    (state : UnificationWorklistState) : UnificationWorklistState :=
  match certificate.links[index]? with
  | none | some (.axiom _ _) => state
  | some (.par left right conclusion) =>
      match state.core.tokenAt? left, state.core.tokenAt? right with
      | some leftToken, some rightToken =>
          if leftToken == rightToken then
            match firePar? state.core left right conclusion with
            | none => state
            | some nextCore =>
                enqueueConsumers consumers conclusion <|
                  recordWorklistFiring { state with core := nextCore }
          else
            addWaiting index state
      | _, _ => state
  | some (.tensor left right conclusion) =>
      match state.core.tokenAt? left, state.core.tokenAt? right with
      | some leftToken, some rightToken =>
          if leftToken == rightToken then
            state
          else
            match fireTensor? state.core left right conclusion with
            | none => state
            | some nextCore =>
                let fired :=
                  recordWorklistFiring { state with core := nextCore }
                let requeued :=
                  requeueWaiting certificate.links.length fired
                enqueueConsumers consumers conclusion requeued
      | _, _ => state

/-- Processing never changes the number of canonical initial queue
insertions. -/
@[simp] private theorem processWorklistLink_initialEnqueues
    (certificate : Certificate) (consumers : Array (List Nat))
    (index : Nat) (state : UnificationWorklistState) :
    (processWorklistLink certificate consumers index
      state).stats.initialEnqueues =
        state.stats.initialEnqueues := by
  cases lookup : certificate.links[index]? with
  | none =>
      simp [processWorklistLink, lookup]
  | some link =>
      cases link with
      | «axiom» left right =>
          simp [processWorklistLink, lookup]
      | «par» left right conclusion =>
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              simp [processWorklistLink, lookup, leftLookup]
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  simp [processWorklistLink, lookup, leftLookup,
                    rightLookup]
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    cases firing :
                        firePar? state.core left right conclusion <;>
                      simp [processWorklistLink, lookup, leftLookup,
                        rightLookup, firing]
                  · simp [processWorklistLink, lookup, leftLookup,
                      rightLookup, same]
      | «tensor» left right conclusion =>
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              simp [processWorklistLink, lookup, leftLookup]
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  simp [processWorklistLink, lookup, leftLookup,
                    rightLookup]
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    simp [processWorklistLink, lookup, leftLookup,
                      rightLookup]
                  · cases firing :
                        fireTensor? state.core left right conclusion <;>
                      simp [processWorklistLink, lookup, leftLookup,
                        rightLookup, same, firing]

/-- Processing one scheduler entry preserves an exact distinct-link firing
history. Successful par/tensor branches extend it once; every other branch is
scheduler-only. -/
private theorem processWorklistLink_firingsAccounted
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (consumers : Array (List Nat)) (index : Nat)
    {state : UnificationWorklistState}
    (abstractable : state.core.Abstractable certificate)
    (accounted : WorklistFiringsAccounted certificate state) :
    WorklistFiringsAccounted certificate
      (processWorklistLink certificate consumers index state) := by
  cases lookup : certificate.links[index]? with
  | none =>
      simpa [processWorklistLink, lookup] using accounted
  | some link =>
      have indexBound :
          index < certificate.links.length :=
        (List.getElem?_eq_some_iff.mp lookup).1
      have linkMembership :
          link ∈ certificate.links := by
        have membership := List.getElem_mem indexBound
        simpa [(List.getElem?_eq_some_iff.mp lookup).2] using membership
      cases link with
      | «axiom» left right =>
          simpa [processWorklistLink, lookup] using accounted
      | «par» left right conclusion =>
          have linkWellFormed :=
            structural.2.2.2.2.1
              (.par left right conclusion) linkMembership
          rcases linkWellFormed with
            ⟨_premisesDifferent, _leftConclusionDifferent,
              _rightConclusionDifferent, _leftBound, _rightBound,
              conclusionBound, _typing⟩
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              simpa [processWorklistLink, lookup, leftLookup] using
                accounted
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  simpa [processWorklistLink, lookup, leftLookup,
                    rightLookup] using accounted
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    cases firing :
                        firePar? state.core left right conclusion with
                    | none =>
                        simpa [processWorklistLink, lookup, leftLookup,
                          rightLookup, firing] using accounted
                    | some nextCore =>
                        have firedAccounted :=
                          accounted.afterFirePar abstractable
                            linkMembership conclusionBound firing
                        let firedState : UnificationWorklistState :=
                          recordWorklistFiring
                            { state with core := nextCore }
                        have enqueuedAccounted :
                            WorklistFiringsAccounted certificate
                              (enqueueConsumers consumers conclusion
                                firedState) :=
                          firedAccounted.transport
                            (by simp [firedState, recordWorklistFiring])
                            (by simp [firedState, recordWorklistFiring])
                        simpa [processWorklistLink, lookup, leftLookup,
                          rightLookup, firing] using enqueuedAccounted
                  · have waitingAccounted :
                        WorklistFiringsAccounted certificate
                          (addWaiting index state) :=
                      accounted.transport
                        (by simp)
                        (by simp)
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, same] using waitingAccounted
      | «tensor» left right conclusion =>
          have linkWellFormed :=
            structural.2.2.2.2.1
              (.tensor left right conclusion) linkMembership
          rcases linkWellFormed with
            ⟨_premisesDifferent, _leftConclusionDifferent,
              _rightConclusionDifferent, _leftBound, _rightBound,
              conclusionBound, _typing⟩
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              simpa [processWorklistLink, lookup, leftLookup] using
                accounted
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  simpa [processWorklistLink, lookup, leftLookup,
                    rightLookup] using accounted
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup] using accounted
                  · cases firing :
                        fireTensor? state.core left right conclusion with
                    | none =>
                        simpa [processWorklistLink, lookup, leftLookup,
                          rightLookup, same, firing] using accounted
                    | some nextCore =>
                        have firedAccounted :=
                          accounted.afterFireTensor abstractable
                            linkMembership conclusionBound firing
                        let firedState : UnificationWorklistState :=
                          recordWorklistFiring
                            { state with core := nextCore }
                        let requeuedState : UnificationWorklistState :=
                          requeueWaiting certificate.links.length
                            firedState
                        have requeuedAccounted :
                            WorklistFiringsAccounted certificate
                              requeuedState :=
                          firedAccounted.transport
                            (by
                              simp [requeuedState, firedState,
                                recordWorklistFiring])
                            (by
                              simp [requeuedState, firedState,
                                recordWorklistFiring])
                        have enqueuedAccounted :
                            WorklistFiringsAccounted certificate
                              (enqueueConsumers consumers conclusion
                                requeuedState) :=
                          requeuedAccounted.transport
                            (by simp)
                            (by simp)
                        simpa [processWorklistLink, lookup, leftLookup,
                          rightLookup, same, firing] using enqueuedAccounted

/-- One canonical worklist processing event preserves cumulative source
charges: at most one dependency insertion per successful firing and at most
one submitted-link carrier of waiting requeues per successful firing. -/
private theorem processWorklistLink_enqueueSourcesBounded
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (index : Nat) {state : UnificationWorklistState}
    (waitingBound :
      state.waiting.length ≤ certificate.links.length)
    (bounded : WorklistEnqueueSourcesBounded certificate state) :
    WorklistEnqueueSourcesBounded certificate
      (processWorklistLink certificate certificate.worklistConsumers
        index state) := by
  rcases bounded with ⟨dependencyBound, waitingSourceBound⟩
  cases lookup : certificate.links[index]? with
  | none =>
      simpa [processWorklistLink, lookup,
        WorklistEnqueueSourcesBounded] using
        And.intro dependencyBound waitingSourceBound
  | some link =>
      cases link with
      | «axiom» left right =>
          simpa [processWorklistLink, lookup,
            WorklistEnqueueSourcesBounded] using
            And.intro dependencyBound waitingSourceBound
      | «par» left right conclusion =>
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              simpa [processWorklistLink, lookup, leftLookup,
                WorklistEnqueueSourcesBounded] using
                And.intro dependencyBound waitingSourceBound
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  simpa [processWorklistLink, lookup, leftLookup,
                    rightLookup, WorklistEnqueueSourcesBounded] using
                    And.intro dependencyBound waitingSourceBound
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    cases firing :
                        firePar? state.core left right conclusion with
                    | none =>
                        simpa [processWorklistLink, lookup, leftLookup,
                          rightLookup, firing,
                          WorklistEnqueueSourcesBounded] using
                          And.intro dependencyBound waitingSourceBound
                    | some nextCore =>
                        let firedState : UnificationWorklistState :=
                          recordWorklistFiring
                            { state with core := nextCore }
                        have dependencyStep :=
                          enqueueConsumers_dependencyEnqueues_le
                            structural conclusion firedState
                        have waitingExact :
                            (enqueueConsumers
                              certificate.worklistConsumers conclusion
                              firedState).stats.waitingRequeues =
                                state.stats.waitingRequeues := by
                          simp [firedState, recordWorklistFiring]
                        have firingExact :
                            (enqueueConsumers
                              certificate.worklistConsumers conclusion
                              firedState).stats.successfulFirings =
                                state.stats.successfulFirings + 1 := by
                          simp [firedState, recordWorklistFiring]
                        have firedDependencyExact :
                            firedState.stats.dependencyEnqueues =
                              state.stats.dependencyEnqueues := by
                          simp [firedState]
                        have dependencyResult :
                            (enqueueConsumers
                              certificate.worklistConsumers conclusion
                              firedState).stats.dependencyEnqueues ≤
                                state.stats.successfulFirings + 1 := by
                          calc
                            (enqueueConsumers
                              certificate.worklistConsumers conclusion
                              firedState).stats.dependencyEnqueues ≤
                                firedState.stats.dependencyEnqueues + 1 :=
                              dependencyStep
                            _ = state.stats.dependencyEnqueues + 1 := by
                              rw [firedDependencyExact]
                            _ ≤ state.stats.successfulFirings + 1 :=
                              Nat.add_le_add_right dependencyBound 1
                        constructor
                        · simpa [processWorklistLink, lookup, leftLookup,
                            rightLookup, firing, firedState,
                            WorklistEnqueueSourcesBounded] using
                            dependencyResult
                        · have resultBound :
                              state.stats.waitingRequeues ≤
                                certificate.links.length *
                                  (state.stats.successfulFirings + 1) :=
                            Nat.le_trans waitingSourceBound
                              (Nat.mul_le_mul_left _
                                (Nat.le_add_right
                                  state.stats.successfulFirings 1))
                          simpa [processWorklistLink, lookup, leftLookup,
                            rightLookup, firing, firedState,
                            recordWorklistFiring] using resultBound
                  · simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, same, WorklistEnqueueSourcesBounded]
                      using And.intro dependencyBound waitingSourceBound
      | «tensor» left right conclusion =>
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              simpa [processWorklistLink, lookup, leftLookup,
                WorklistEnqueueSourcesBounded] using
                And.intro dependencyBound waitingSourceBound
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  simpa [processWorklistLink, lookup, leftLookup,
                    rightLookup, WorklistEnqueueSourcesBounded] using
                    And.intro dependencyBound waitingSourceBound
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, WorklistEnqueueSourcesBounded] using
                      And.intro dependencyBound waitingSourceBound
                  · cases firing :
                        fireTensor? state.core left right conclusion with
                    | none =>
                        simpa [processWorklistLink, lookup, leftLookup,
                          rightLookup, same, firing,
                          WorklistEnqueueSourcesBounded] using
                          And.intro dependencyBound waitingSourceBound
                    | some nextCore =>
                        let firedState : UnificationWorklistState :=
                          recordWorklistFiring
                            { state with core := nextCore }
                        let requeuedState : UnificationWorklistState :=
                          requeueWaiting certificate.links.length firedState
                        have dependencyStep :=
                          enqueueConsumers_dependencyEnqueues_le
                            structural conclusion requeuedState
                        have waitingStep :=
                          requeueWaiting_waitingRequeues_le
                            certificate.links.length firedState
                        have dependencyExact :
                            requeuedState.stats.dependencyEnqueues =
                              state.stats.dependencyEnqueues := by
                          simp [requeuedState, firedState,
                            recordWorklistFiring]
                        have waitingFinalExact :
                            (enqueueConsumers
                              certificate.worklistConsumers conclusion
                              requeuedState).stats.waitingRequeues =
                                requeuedState.stats.waitingRequeues := by
                          simp
                        have firingExact :
                            (enqueueConsumers
                              certificate.worklistConsumers conclusion
                              requeuedState).stats.successfulFirings =
                                state.stats.successfulFirings + 1 := by
                          simp [requeuedState, firedState]
                        have dependencyResult :
                            (enqueueConsumers
                              certificate.worklistConsumers conclusion
                              requeuedState).stats.dependencyEnqueues ≤
                                state.stats.successfulFirings + 1 := by
                          calc
                            (enqueueConsumers
                              certificate.worklistConsumers conclusion
                              requeuedState).stats.dependencyEnqueues ≤
                                requeuedState.stats.dependencyEnqueues + 1 :=
                              dependencyStep
                            _ = state.stats.dependencyEnqueues + 1 := by
                              rw [dependencyExact]
                            _ ≤ state.stats.successfulFirings + 1 :=
                              Nat.add_le_add_right dependencyBound 1
                        have firedWaitingLength :
                            firedState.waiting.length =
                              state.waiting.length := by
                          rfl
                        have waitingResult :
                            requeuedState.stats.waitingRequeues ≤
                              certificate.links.length *
                                (state.stats.successfulFirings + 1) := by
                          rw [firedWaitingLength] at waitingStep
                          calc
                            requeuedState.stats.waitingRequeues ≤
                                state.stats.waitingRequeues +
                                  state.waiting.length := waitingStep
                            _ ≤ certificate.links.length *
                                  state.stats.successfulFirings +
                                    certificate.links.length :=
                              Nat.add_le_add waitingSourceBound waitingBound
                            _ = certificate.links.length *
                                  (state.stats.successfulFirings + 1) := by
                              simp [Nat.mul_add]
                        constructor
                        · simpa [processWorklistLink, lookup, leftLookup,
                            rightLookup, same, firing, firedState,
                            requeuedState] using dependencyResult
                        · simpa [processWorklistLink, lookup, leftLookup,
                            rightLookup, same, firing, firedState,
                            requeuedState] using
                            (show
                              (enqueueConsumers
                                certificate.worklistConsumers conclusion
                                requeuedState).stats.waitingRequeues ≤
                                  certificate.links.length *
                                    (state.stats.successfulFirings + 1) by
                              rw [waitingFinalExact]
                              exact waitingResult)

/-- Processing one proven submitted queue head preserves exact provenance for
both the remaining queue and the waiting-par registry.  Dependency fan-out
uses the reverse consumer-table theorem; tensor requeue uses waiting-par
constructor provenance. -/
private theorem processWorklistLink_provenance
    {certificate : Certificate} {index : Nat} {link : Link}
    {state : UnificationWorklistState}
    (lookup : certificate.links[index]? = some link)
    (connective : link.isConnective = true)
    (queueSound : QueueConnectiveSound certificate state)
    (waitingSound : WaitingParSound certificate state) :
    QueueConnectiveSound certificate
        (processWorklistLink certificate
          certificate.worklistConsumers index state) ∧
      WaitingParSound certificate
        (processWorklistLink certificate
          certificate.worklistConsumers index state) := by
  have unchanged :
      QueueConnectiveSound certificate state ∧
        WaitingParSound certificate state :=
    ⟨queueSound, waitingSound⟩
  cases link with
  | «axiom» left right =>
      simp [Link.isConnective] at connective
  | «par» left right conclusion =>
      cases leftLookup : state.core.tokenAt? left with
      | none =>
          simpa [processWorklistLink, lookup, leftLookup] using
            unchanged
      | some leftToken =>
          cases rightLookup : state.core.tokenAt? right with
          | none =>
              simpa [processWorklistLink, lookup, leftLookup,
                rightLookup] using unchanged
          | some rightToken =>
              by_cases same : leftToken = rightToken
              · subst rightToken
                cases firing :
                    firePar? state.core left right conclusion with
                | none =>
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, firing] using
                        unchanged
                | some nextCore =>
                    let fired : UnificationWorklistState :=
                      recordWorklistFiring
                        { state with core := nextCore }
                    have firedQueue :
                        QueueConnectiveSound certificate fired := by
                      intro candidate membership
                      apply queueSound
                      simpa [fired, recordWorklistFiring] using membership
                    have firedWaiting :
                        WaitingParSound certificate fired := by
                      intro candidate membership
                      apply waitingSound
                      simpa [fired, recordWorklistFiring] using membership
                    have nextQueue :
                        QueueConnectiveSound certificate
                          (Certificate.enqueueConsumers
                            certificate.worklistConsumers conclusion
                            fired) :=
                      QueueConnectiveSound.enqueueConsumersWorklist
                        (certificate := certificate) (state := fired)
                        firedQueue conclusion
                    have nextWaiting :
                        WaitingParSound certificate
                          (Certificate.enqueueConsumers
                            certificate.worklistConsumers conclusion
                            fired) :=
                      WaitingParSound.enqueueConsumers
                        (certificate := certificate) (state := fired)
                        firedWaiting certificate.worklistConsumers
                          conclusion
                    have nextProvenance :
                        QueueConnectiveSound certificate
                            (Certificate.enqueueConsumers
                              certificate.worklistConsumers conclusion
                              fired) ∧
                          WaitingParSound certificate
                            (Certificate.enqueueConsumers
                              certificate.worklistConsumers conclusion
                              fired) :=
                      ⟨nextQueue, nextWaiting⟩
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, firing, fired] using
                        nextProvenance
              · have nextQueue :
                    QueueConnectiveSound certificate
                      (Certificate.addWaiting index state) :=
                  QueueConnectiveSound.addWaiting
                    (certificate := certificate) (state := state)
                    queueSound index
                have nextWaiting :
                    WaitingParSound certificate
                      (Certificate.addWaiting index state) :=
                  WaitingParSound.addWaiting
                    (certificate := certificate) (state := state)
                    waitingSound lookup
                have nextProvenance :
                    QueueConnectiveSound certificate
                        (Certificate.addWaiting index state) ∧
                      WaitingParSound certificate
                        (Certificate.addWaiting index state) :=
                  ⟨nextQueue, nextWaiting⟩
                simpa [processWorklistLink, lookup, leftLookup,
                  rightLookup, same] using
                    nextProvenance
  | «tensor» left right conclusion =>
      cases leftLookup : state.core.tokenAt? left with
      | none =>
          simpa [processWorklistLink, lookup, leftLookup] using
            unchanged
      | some leftToken =>
          cases rightLookup : state.core.tokenAt? right with
          | none =>
              simpa [processWorklistLink, lookup, leftLookup,
                rightLookup] using unchanged
          | some rightToken =>
              by_cases same : leftToken = rightToken
              · subst rightToken
                simpa [processWorklistLink, lookup, leftLookup,
                  rightLookup] using unchanged
              · cases firing :
                    fireTensor? state.core left right conclusion with
                | none =>
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, same, firing] using
                        unchanged
                | some nextCore =>
                    let fired : UnificationWorklistState :=
                      recordWorklistFiring
                        { state with core := nextCore }
                    have firedQueue :
                        QueueConnectiveSound certificate fired := by
                      intro candidate membership
                      apply queueSound
                      simpa [fired, recordWorklistFiring] using membership
                    have firedWaiting :
                        WaitingParSound certificate fired := by
                      intro candidate membership
                      apply waitingSound
                      simpa [fired, recordWorklistFiring] using membership
                    let requeued : UnificationWorklistState :=
                      Certificate.requeueWaiting
                        certificate.links.length fired
                    have requeuedQueue :
                        QueueConnectiveSound certificate requeued := by
                      exact firedQueue.requeueWaiting firedWaiting
                        certificate.links.length
                    have requeuedWaiting :
                        WaitingParSound certificate requeued := by
                      exact WaitingParSound.requeueWaiting
                        (certificate := certificate) fired
                          certificate.links.length
                    have nextQueue :
                        QueueConnectiveSound certificate
                          (Certificate.enqueueConsumers
                            certificate.worklistConsumers conclusion
                            requeued) :=
                      QueueConnectiveSound.enqueueConsumersWorklist
                        (certificate := certificate) (state := requeued)
                        requeuedQueue conclusion
                    have nextWaiting :
                        WaitingParSound certificate
                          (Certificate.enqueueConsumers
                            certificate.worklistConsumers conclusion
                            requeued) :=
                      WaitingParSound.enqueueConsumers
                        (certificate := certificate) (state := requeued)
                        requeuedWaiting certificate.worklistConsumers
                          conclusion
                    have nextProvenance :
                        QueueConnectiveSound certificate
                            (Certificate.enqueueConsumers
                              certificate.worklistConsumers conclusion
                              requeued) ∧
                          WaitingParSound certificate
                            (Certificate.enqueueConsumers
                              certificate.worklistConsumers conclusion
                              requeued) :=
                      ⟨nextQueue, nextWaiting⟩
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, same, firing, fired, requeued] using
                        nextProvenance

/-- Processing one submitted queue head preserves exact queue/waiting flag
completeness and uniqueness through dependency fan-out, waiting registration,
and full waiting requeue. -/
private theorem processWorklistLink_exactDiscipline
    {certificate : Certificate} {index : Nat} {link : Link}
    {state : UnificationWorklistState}
    (lookup : certificate.links[index]? = some link)
    (connective : link.isConnective = true)
    (queueComplete : QueueFlagComplete state)
    (queueNodup : QueueNodup state)
    (waitingComplete : WaitingFlagComplete state)
    (waitingNodup : WaitingNodup state) :
    let next :=
      processWorklistLink certificate
        certificate.worklistConsumers index state
    QueueFlagComplete next ∧
      QueueNodup next ∧
        WaitingFlagComplete next ∧
          WaitingNodup next := by
  have unchanged :
      QueueFlagComplete state ∧
        QueueNodup state ∧
          WaitingFlagComplete state ∧
            WaitingNodup state :=
    ⟨queueComplete, queueNodup, waitingComplete, waitingNodup⟩
  cases link with
  | «axiom» left right =>
      simp [Link.isConnective] at connective
  | «par» left right conclusion =>
      cases leftLookup : state.core.tokenAt? left with
      | none =>
          simpa [processWorklistLink, lookup, leftLookup] using
            unchanged
      | some leftToken =>
          cases rightLookup : state.core.tokenAt? right with
          | none =>
              simpa [processWorklistLink, lookup, leftLookup,
                rightLookup] using unchanged
          | some rightToken =>
              by_cases same : leftToken = rightToken
              · subst rightToken
                cases firing :
                    firePar? state.core left right conclusion with
                | none =>
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, firing] using unchanged
                | some nextCore =>
                    let fired : UnificationWorklistState :=
                      recordWorklistFiring
                        { state with core := nextCore }
                    have firedQueueComplete :
                        QueueFlagComplete fired := by
                      intro candidate membership
                      apply queueComplete
                      simpa [fired, recordWorklistFiring] using membership
                    have firedQueueNodup :
                        QueueNodup fired := by
                      simpa [fired, recordWorklistFiring, QueueNodup] using
                        queueNodup
                    have firedWaitingComplete :
                        WaitingFlagComplete fired := by
                      intro candidate membership
                      apply waitingComplete
                      simpa [fired, recordWorklistFiring] using membership
                    have firedWaitingNodup :
                        WaitingNodup fired := by
                      simpa [fired, recordWorklistFiring, WaitingNodup] using
                        waitingNodup
                    have nextQueueComplete :
                        QueueFlagComplete
                          (Certificate.enqueueConsumers
                            certificate.worklistConsumers conclusion
                            fired) :=
                      firedQueueComplete.enqueueConsumers
                        certificate.worklistConsumers conclusion
                    have nextQueueNodup :
                        QueueNodup
                          (Certificate.enqueueConsumers
                            certificate.worklistConsumers conclusion
                            fired) :=
                      firedQueueNodup.enqueueConsumers
                        firedQueueComplete
                          certificate.worklistConsumers conclusion
                    have nextWaitingComplete :
                        WaitingFlagComplete
                          (Certificate.enqueueConsumers
                            certificate.worklistConsumers conclusion
                            fired) :=
                      firedWaitingComplete.enqueueConsumers
                        certificate.worklistConsumers conclusion
                    have nextWaitingNodup :
                        WaitingNodup
                          (Certificate.enqueueConsumers
                            certificate.worklistConsumers conclusion
                            fired) :=
                      firedWaitingNodup.enqueueConsumers
                        certificate.worklistConsumers conclusion
                    have nextExact :
                        QueueFlagComplete
                            (Certificate.enqueueConsumers
                              certificate.worklistConsumers conclusion
                              fired) ∧
                          QueueNodup
                            (Certificate.enqueueConsumers
                              certificate.worklistConsumers conclusion
                              fired) ∧
                            WaitingFlagComplete
                              (Certificate.enqueueConsumers
                                certificate.worklistConsumers conclusion
                                fired) ∧
                              WaitingNodup
                                (Certificate.enqueueConsumers
                                  certificate.worklistConsumers conclusion
                                  fired) :=
                      ⟨nextQueueComplete, nextQueueNodup,
                        nextWaitingComplete, nextWaitingNodup⟩
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, firing, fired] using nextExact
              · have nextExact :
                    QueueFlagComplete
                        (Certificate.addWaiting index state) ∧
                      QueueNodup
                          (Certificate.addWaiting index state) ∧
                        WaitingFlagComplete
                            (Certificate.addWaiting index state) ∧
                          WaitingNodup
                            (Certificate.addWaiting index state) :=
                  ⟨queueComplete.addWaiting index,
                    queueNodup.addWaiting index,
                    waitingComplete.addWaiting index,
                    waitingNodup.addWaiting waitingComplete index⟩
                simpa [processWorklistLink, lookup, leftLookup,
                  rightLookup, same] using nextExact
  | «tensor» left right conclusion =>
      cases leftLookup : state.core.tokenAt? left with
      | none =>
          simpa [processWorklistLink, lookup, leftLookup] using
            unchanged
      | some leftToken =>
          cases rightLookup : state.core.tokenAt? right with
          | none =>
              simpa [processWorklistLink, lookup, leftLookup,
                rightLookup] using unchanged
          | some rightToken =>
              by_cases same : leftToken = rightToken
              · subst rightToken
                simpa [processWorklistLink, lookup, leftLookup,
                  rightLookup] using unchanged
              · cases firing :
                    fireTensor? state.core left right conclusion with
                | none =>
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, same, firing] using unchanged
                | some nextCore =>
                    let fired : UnificationWorklistState :=
                      recordWorklistFiring
                        { state with core := nextCore }
                    have firedQueueComplete :
                        QueueFlagComplete fired := by
                      intro candidate membership
                      apply queueComplete
                      simpa [fired, recordWorklistFiring] using membership
                    have firedQueueNodup :
                        QueueNodup fired := by
                      simpa [fired, recordWorklistFiring, QueueNodup] using
                        queueNodup
                    have firedWaitingComplete :
                        WaitingFlagComplete fired := by
                      intro candidate membership
                      apply waitingComplete
                      simpa [fired, recordWorklistFiring] using membership
                    have firedWaitingNodup :
                        WaitingNodup fired := by
                      simpa [fired, recordWorklistFiring, WaitingNodup] using
                        waitingNodup
                    let requeued : UnificationWorklistState :=
                      Certificate.requeueWaiting
                        certificate.links.length fired
                    have requeuedQueueComplete :
                        QueueFlagComplete requeued := by
                      exact firedQueueComplete.requeueWaiting
                        certificate.links.length
                    have requeuedQueueNodup :
                        QueueNodup requeued := by
                      exact firedQueueNodup.requeueWaiting
                        firedQueueComplete certificate.links.length
                    have requeuedWaitingComplete :
                        WaitingFlagComplete requeued := by
                      exact WaitingFlagComplete.requeueWaiting
                        fired certificate.links.length
                    have requeuedWaitingNodup :
                        WaitingNodup requeued := by
                      exact WaitingNodup.requeueWaiting
                        fired certificate.links.length
                    have nextQueueComplete :
                        QueueFlagComplete
                          (Certificate.enqueueConsumers
                            certificate.worklistConsumers conclusion
                            requeued) :=
                      requeuedQueueComplete.enqueueConsumers
                        certificate.worklistConsumers conclusion
                    have nextQueueNodup :
                        QueueNodup
                          (Certificate.enqueueConsumers
                            certificate.worklistConsumers conclusion
                            requeued) :=
                      requeuedQueueNodup.enqueueConsumers
                        requeuedQueueComplete
                          certificate.worklistConsumers conclusion
                    have nextWaitingComplete :
                        WaitingFlagComplete
                          (Certificate.enqueueConsumers
                            certificate.worklistConsumers conclusion
                            requeued) :=
                      requeuedWaitingComplete.enqueueConsumers
                        certificate.worklistConsumers conclusion
                    have nextWaitingNodup :
                        WaitingNodup
                          (Certificate.enqueueConsumers
                            certificate.worklistConsumers conclusion
                            requeued) :=
                      requeuedWaitingNodup.enqueueConsumers
                        certificate.worklistConsumers conclusion
                    have nextExact :
                        QueueFlagComplete
                            (Certificate.enqueueConsumers
                              certificate.worklistConsumers conclusion
                              requeued) ∧
                          QueueNodup
                            (Certificate.enqueueConsumers
                              certificate.worklistConsumers conclusion
                              requeued) ∧
                            WaitingFlagComplete
                              (Certificate.enqueueConsumers
                                certificate.worklistConsumers conclusion
                                requeued) ∧
                              WaitingNodup
                                (Certificate.enqueueConsumers
                                  certificate.worklistConsumers conclusion
                                  requeued) :=
                      ⟨nextQueueComplete, nextQueueNodup,
                        nextWaitingComplete, nextWaitingNodup⟩
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, same, firing, fired, requeued] using
                        nextExact

/-- Processing one popped link accounts exactly for every successful queue
insertion. No-op attempts and waiting registration add no insertion credit;
par firing composes one dependency batch, while tensor firing composes a
waiting requeue and one dependency batch. -/
private theorem processWorklistLink_balance
    {certificate : Certificate} {index : Nat} {link : Link}
    {state : UnificationWorklistState}
    (consumers : Array (List Nat))
    (lookup : certificate.links[index]? = some link) :
    QueueInsertionBalanced state
      (processWorklistLink certificate
        consumers index state) := by
  cases link with
  | «axiom» left right =>
      simp [processWorklistLink, lookup, QueueInsertionBalanced]
  | «par» left right conclusion =>
      cases leftLookup : state.core.tokenAt? left with
      | none =>
          simp [processWorklistLink, lookup, leftLookup,
            QueueInsertionBalanced]
      | some leftToken =>
          cases rightLookup : state.core.tokenAt? right with
          | none =>
              simp [processWorklistLink, lookup, leftLookup,
                rightLookup, QueueInsertionBalanced]
          | some rightToken =>
              by_cases same : leftToken = rightToken
              · subst rightToken
                cases firing :
                    firePar? state.core left right conclusion with
                | none =>
                    simp [processWorklistLink, lookup, leftLookup,
                      rightLookup, firing, QueueInsertionBalanced]
                | some nextCore =>
                    let fired : UnificationWorklistState :=
                      recordWorklistFiring
                        { state with core := nextCore }
                    have toFired :
                        QueueInsertionBalanced state fired := by
                      simpa [fired] using
                        coreUpdate_recordWorklistFiring_balance
                          state nextCore
                    have toNext :
                        QueueInsertionBalanced fired
                          (Certificate.enqueueConsumers
                            consumers conclusion
                            fired) := by
                      exact enqueueConsumers_balance
                        consumers conclusion fired
                    have composed := toFired.trans toNext
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, firing, fired] using composed
              · have registered :
                    QueueInsertionBalanced state
                      (Certificate.addWaiting index state) :=
                  addWaiting_balance index state
                simpa [processWorklistLink, lookup, leftLookup,
                  rightLookup, same] using registered
  | «tensor» left right conclusion =>
      cases leftLookup : state.core.tokenAt? left with
      | none =>
          simp [processWorklistLink, lookup, leftLookup,
            QueueInsertionBalanced]
      | some leftToken =>
          cases rightLookup : state.core.tokenAt? right with
          | none =>
              simp [processWorklistLink, lookup, leftLookup,
                rightLookup, QueueInsertionBalanced]
          | some rightToken =>
              by_cases same : leftToken = rightToken
              · subst rightToken
                simp [processWorklistLink, lookup, leftLookup,
                  rightLookup, QueueInsertionBalanced]
              · cases firing :
                    fireTensor? state.core left right conclusion with
                | none =>
                    simp [processWorklistLink, lookup, leftLookup,
                      rightLookup, same, firing, QueueInsertionBalanced]
                | some nextCore =>
                    let fired : UnificationWorklistState :=
                      recordWorklistFiring
                        { state with core := nextCore }
                    let requeued : UnificationWorklistState :=
                      Certificate.requeueWaiting
                        certificate.links.length fired
                    have toFired :
                        QueueInsertionBalanced state fired := by
                      simpa [fired] using
                        coreUpdate_recordWorklistFiring_balance
                          state nextCore
                    have toRequeued :
                        QueueInsertionBalanced fired requeued := by
                      simpa [requeued, QueueInsertionBalanced] using
                        requeueWaiting_balance
                          certificate.links.length fired
                    have toNext :
                        QueueInsertionBalanced requeued
                          (Certificate.enqueueConsumers
                            consumers conclusion
                            requeued) := by
                      exact enqueueConsumers_balance
                        consumers conclusion requeued
                    have composed :=
                      (toFired.trans toRequeued).trans toNext
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, same, firing, fired, requeued] using
                        composed

/-- Queue-insertion accounting is total even for an out-of-range popped
number: that branch is an exact no-op. -/
private theorem processWorklistLink_balance_total
    (certificate : Certificate) (consumers : Array (List Nat))
    (index : Nat)
    (state : UnificationWorklistState) :
    QueueInsertionBalanced state
      (processWorklistLink certificate
        consumers index state) := by
  cases lookup : certificate.links[index]? with
  | none =>
      simp [processWorklistLink, lookup, QueueInsertionBalanced]
  | some link =>
      exact processWorklistLink_balance consumers lookup

/-- Processing one submitted queue head preserves sound scheduler flags and
their exact submitted-link carriers. -/
private theorem processWorklistLink_bookkeeping
    {certificate : Certificate} {index : Nat} {link : Link}
    {state : UnificationWorklistState}
    (lookup : certificate.links[index]? = some link)
    (connective : link.isConnective = true)
    (queueSound : QueueFlagSound state)
    (waitingSound : WaitingFlagSound state)
    (queueSize :
      state.queued.size = certificate.links.length)
    (waitingSize :
      state.waitingFlags.size = state.queued.size) :
    let next :=
      processWorklistLink certificate
        certificate.worklistConsumers index state
    QueueFlagSound next ∧
      WaitingFlagSound next ∧
      next.queued.size = certificate.links.length ∧
      next.waitingFlags.size = next.queued.size := by
  dsimp only
  have unchanged :
      QueueFlagSound state ∧
        WaitingFlagSound state ∧
        state.queued.size = certificate.links.length ∧
        state.waitingFlags.size = state.queued.size :=
    ⟨queueSound, waitingSound, queueSize, waitingSize⟩
  cases link with
  | «axiom» left right =>
      simp [Link.isConnective] at connective
  | «par» left right conclusion =>
      cases leftLookup : state.core.tokenAt? left with
      | none =>
          simpa [processWorklistLink, lookup, leftLookup] using unchanged
      | some leftToken =>
          cases rightLookup : state.core.tokenAt? right with
          | none =>
              simpa [processWorklistLink, lookup, leftLookup,
                rightLookup] using unchanged
          | some rightToken =>
              by_cases same : leftToken = rightToken
              · subst rightToken
                cases firing :
                    firePar? state.core left right conclusion with
                | none =>
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, firing] using unchanged
                | some nextCore =>
                    let fired : UnificationWorklistState :=
                      recordWorklistFiring
                        { state with core := nextCore }
                    have firedQueue : QueueFlagSound fired := by
                      intro candidate flagged
                      apply queueSound
                      simpa [fired, recordWorklistFiring] using flagged
                    have firedWaiting : WaitingFlagSound fired := by
                      intro candidate flagged
                      have oldFlag :
                          state.waitingFlags[candidate]? =
                            some true := by
                        simpa [fired, recordWorklistFiring] using flagged
                      have oldMembership := waitingSound oldFlag
                      simpa [fired, recordWorklistFiring] using oldMembership
                    let next :=
                      Certificate.enqueueConsumers
                        certificate.worklistConsumers conclusion fired
                    have nextQueue : QueueFlagSound next :=
                      firedQueue.enqueueConsumers
                        certificate.worklistConsumers conclusion
                    have nextWaiting : WaitingFlagSound next :=
                      firedWaiting.enqueueConsumers
                        certificate.worklistConsumers conclusion
                    have nextQueueSize :
                        next.queued.size =
                          certificate.links.length := by
                      simp [next, fired, recordWorklistFiring, queueSize]
                    have nextWaitingSize :
                        next.waitingFlags.size =
                          next.queued.size := by
                      simp [next, fired, recordWorklistFiring,
                        queueSize, waitingSize]
                    have nextInvariant :
                        QueueFlagSound next ∧
                          WaitingFlagSound next ∧
                          next.queued.size =
                            certificate.links.length ∧
                          next.waitingFlags.size =
                            next.queued.size :=
                      ⟨nextQueue, nextWaiting, nextQueueSize,
                        nextWaitingSize⟩
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, firing, fired, next] using nextInvariant
              · let next :=
                    Certificate.addWaiting index state
                have nextQueue : QueueFlagSound next :=
                  queueSound.addWaiting index
                have nextWaiting : WaitingFlagSound next :=
                  waitingSound.addWaiting index
                have nextQueueSize :
                    next.queued.size =
                      certificate.links.length := by
                  simpa [next] using queueSize
                have nextWaitingSize :
                    next.waitingFlags.size =
                      next.queued.size := by
                  simp [next, queueSize, waitingSize]
                have nextInvariant :
                    QueueFlagSound next ∧
                      WaitingFlagSound next ∧
                      next.queued.size =
                        certificate.links.length ∧
                      next.waitingFlags.size =
                        next.queued.size :=
                  ⟨nextQueue, nextWaiting, nextQueueSize,
                    nextWaitingSize⟩
                simpa [processWorklistLink, lookup, leftLookup,
                  rightLookup, same, next] using nextInvariant
  | «tensor» left right conclusion =>
      cases leftLookup : state.core.tokenAt? left with
      | none =>
          simpa [processWorklistLink, lookup, leftLookup] using unchanged
      | some leftToken =>
          cases rightLookup : state.core.tokenAt? right with
          | none =>
              simpa [processWorklistLink, lookup, leftLookup,
                rightLookup] using unchanged
          | some rightToken =>
              by_cases same : leftToken = rightToken
              · subst rightToken
                simpa [processWorklistLink, lookup, leftLookup,
                  rightLookup] using unchanged
              · cases firing :
                    fireTensor? state.core left right conclusion with
                | none =>
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, same, firing] using unchanged
                | some nextCore =>
                    let fired : UnificationWorklistState :=
                      recordWorklistFiring
                        { state with core := nextCore }
                    have firedQueue : QueueFlagSound fired := by
                      intro candidate flagged
                      apply queueSound
                      simpa [fired, recordWorklistFiring] using flagged
                    have firedWaiting : WaitingFlagSound fired := by
                      intro candidate flagged
                      have oldFlag :
                          state.waitingFlags[candidate]? =
                            some true := by
                        simpa [fired, recordWorklistFiring] using flagged
                      have oldMembership := waitingSound oldFlag
                      simpa [fired, recordWorklistFiring] using oldMembership
                    let requeued :=
                      Certificate.requeueWaiting
                        certificate.links.length fired
                    have requeuedQueue : QueueFlagSound requeued :=
                      firedQueue.requeueWaiting certificate.links.length
                    have requeuedWaiting : WaitingFlagSound requeued :=
                      WaitingFlagSound.requeueWaiting fired
                        certificate.links.length
                    let next :=
                      Certificate.enqueueConsumers
                        certificate.worklistConsumers conclusion requeued
                    have nextQueue : QueueFlagSound next :=
                      requeuedQueue.enqueueConsumers
                        certificate.worklistConsumers conclusion
                    have nextWaiting : WaitingFlagSound next :=
                      requeuedWaiting.enqueueConsumers
                        certificate.worklistConsumers conclusion
                    have nextQueueSize :
                        next.queued.size =
                          certificate.links.length := by
                      simp [next, requeued, fired, recordWorklistFiring,
                        queueSize]
                    have nextWaitingSize :
                        next.waitingFlags.size =
                          next.queued.size := by
                      simp [next, requeued, fired, recordWorklistFiring,
                        queueSize]
                    have nextInvariant :
                        QueueFlagSound next ∧
                          WaitingFlagSound next ∧
                          next.queued.size =
                            certificate.links.length ∧
                          next.waitingFlags.size =
                            next.queued.size :=
                      ⟨nextQueue, nextWaiting, nextQueueSize,
                        nextWaitingSize⟩
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, same, firing, fired, requeued, next] using
                        nextInvariant

/-- Every worklist processing branch preserves the executable abstraction
contract.  Scheduler bookkeeping is invisible to the contract; the only
nontrivial branches are successful par and tensor firings, which already
refine one independent Figure-5 transition. -/
private theorem processWorklistLink_core_abstractable
    {certificate : Certificate} {consumers : Array (List Nat)}
    {index : Nat} {state : UnificationWorklistState}
    (abstractable : state.core.Abstractable certificate)
    (ordered : state.core.OrderedParents) :
    (processWorklistLink certificate consumers index state).core
      |>.Abstractable certificate := by
  cases linkLookup : certificate.links[index]? with
  | none =>
      simpa [processWorklistLink, linkLookup] using abstractable
  | some link =>
      have linkMembership : link ∈ certificate.links :=
        List.mem_of_getElem? linkLookup
      cases link with
      | «axiom» left right =>
          simpa [processWorklistLink, linkLookup] using abstractable
      | «par» left right conclusion =>
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              simpa [processWorklistLink, linkLookup, leftLookup] using
                abstractable
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  simpa [processWorklistLink, linkLookup, leftLookup,
                    rightLookup] using abstractable
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    cases firing :
                        firePar? state.core left right conclusion with
                    | none =>
                        simpa [processWorklistLink, linkLookup, leftLookup,
                          rightLookup, firing] using abstractable
                    | some nextCore =>
                        rcases firePar?_refines_forward certificate
                            abstractable linkMembership firing with
                          ⟨nextAbstractable, _step⟩
                        simpa [processWorklistLink, linkLookup, leftLookup,
                          rightLookup, firing] using nextAbstractable
                  · simpa [processWorklistLink, linkLookup, leftLookup,
                      rightLookup, same] using abstractable
      | «tensor» left right conclusion =>
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              simpa [processWorklistLink, linkLookup, leftLookup] using
                abstractable
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  simpa [processWorklistLink, linkLookup, leftLookup,
                    rightLookup] using abstractable
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    simpa [processWorklistLink, linkLookup, leftLookup,
                      rightLookup] using abstractable
                  · cases firing :
                        fireTensor? state.core left right conclusion with
                    | none =>
                        simpa [processWorklistLink, linkLookup, leftLookup,
                          rightLookup, same, firing] using abstractable
                    | some nextCore =>
                        rcases fireTensor?_refines_unify certificate
                            abstractable ordered linkMembership firing with
                          ⟨nextAbstractable, _step⟩
                        simpa [processWorklistLink, linkLookup, leftLookup,
                          rightLookup, same, firing] using nextAbstractable

/-- Semantic thread connectivity depends on the executable observations, not
on the proof term witnessing the abstraction contract. -/
private theorem UnificationState.threadConnected_of_eq
    {certificate : Certificate} {first second : UnificationState}
    (firstAbstractable : first.Abstractable certificate)
    (secondAbstractable : second.Abstractable certificate)
    (equation : first = second)
    (connected :
      UnificationMarking.ThreadConnected
        (first.toMarking certificate firstAbstractable)) :
    UnificationMarking.ThreadConnected
      (second.toMarking certificate secondAbstractable) := by
  subst second
  have markingEquation :
      first.toMarking certificate secondAbstractable =
        first.toMarking certificate firstAbstractable := by
    rfl
  rw [markingEquation]
  intro firstVertex secondVertex firstToken secondToken
    firstMarked secondMarked synchronized
  exact connected firstMarked secondMarked synchronized

/-- Causal threading depends only on executable marks and representatives,
not on the proof term witnessing the abstraction contract. -/
private theorem UnificationState.causallyThreaded_of_eq
    {certificate : Certificate} {first second : UnificationState}
    (firstAbstractable : first.Abstractable certificate)
    (secondAbstractable : second.Abstractable certificate)
    (equation : first = second)
    (coherent :
      UnificationMarking.CausallyThreaded
        (first.toMarking certificate firstAbstractable)) :
    UnificationMarking.CausallyThreaded
      (second.toMarking certificate secondAbstractable) := by
  subst second
  have markingEquation :
      first.toMarking certificate secondAbstractable =
        first.toMarking certificate firstAbstractable := by
    rfl
  rw [markingEquation]
  exact coherent

/-- One scheduler attempt preserves causal closure and exact threading of all
active retained reference links.  No-op branches transport the old marking;
successful branches use their independent Figure-5 refinement step. -/
private theorem processWorklistLink_causallyThreaded
    {certificate : Certificate} {consumers : Array (List Nat)}
    {index : Nat} {state : UnificationWorklistState}
    (structural : certificate.StructurallyWellFormed)
    (abstractable : state.core.Abstractable certificate)
    (ordered : state.core.OrderedParents)
    (coherent :
      UnificationMarking.CausallyThreaded
        (state.core.toMarking certificate abstractable)) :
    UnificationMarking.CausallyThreaded
      ((processWorklistLink certificate consumers index state).core.toMarking
        certificate
        (processWorklistLink_core_abstractable abstractable ordered)) := by
  have fromCore {core : UnificationState}
      (coreAbstractable : core.Abstractable certificate)
      (coreCoherent :
        UnificationMarking.CausallyThreaded
          (core.toMarking certificate coreAbstractable))
      (equation :
        core =
          (processWorklistLink certificate consumers index state).core) :
      UnificationMarking.CausallyThreaded
        ((processWorklistLink certificate consumers index state).core.toMarking
          certificate
          (processWorklistLink_core_abstractable abstractable ordered)) :=
    UnificationState.causallyThreaded_of_eq
      coreAbstractable _ equation coreCoherent
  cases linkLookup : certificate.links[index]? with
  | none =>
      exact fromCore abstractable coherent
        (by simp [processWorklistLink, linkLookup])
  | some link =>
      have linkMembership : link ∈ certificate.links :=
        List.mem_of_getElem? linkLookup
      cases link with
      | «axiom» left right =>
          exact fromCore abstractable coherent
            (by simp [processWorklistLink, linkLookup])
      | «par» left right conclusion =>
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              exact fromCore abstractable coherent
                (by simp [processWorklistLink, linkLookup, leftLookup])
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  exact fromCore abstractable coherent
                    (by simp [processWorklistLink, linkLookup, leftLookup,
                      rightLookup])
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    cases firing :
                        firePar? state.core left right conclusion with
                    | none =>
                        exact fromCore abstractable coherent
                          (by simp [processWorklistLink, linkLookup,
                            leftLookup, rightLookup, firing])
                    | some nextCore =>
                        rcases firePar?_refines_forward certificate
                            abstractable linkMembership firing with
                          ⟨nextAbstractable, semanticStep⟩
                        exact fromCore nextAbstractable
                          (semanticStep.causallyThreaded structural coherent)
                          (by simp [processWorklistLink, linkLookup,
                            leftLookup, rightLookup, firing])
                  · exact fromCore abstractable coherent
                      (by simp [processWorklistLink, linkLookup,
                        leftLookup, rightLookup, same])
      | «tensor» left right conclusion =>
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              exact fromCore abstractable coherent
                (by simp [processWorklistLink, linkLookup, leftLookup])
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  exact fromCore abstractable coherent
                    (by simp [processWorklistLink, linkLookup, leftLookup,
                      rightLookup])
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    exact fromCore abstractable coherent
                      (by simp [processWorklistLink, linkLookup,
                        leftLookup, rightLookup])
                  · cases firing :
                        fireTensor? state.core left right conclusion with
                    | none =>
                        exact fromCore abstractable coherent
                          (by simp [processWorklistLink, linkLookup,
                            leftLookup, rightLookup, same, firing])
                    | some nextCore =>
                        rcases fireTensor?_refines_unify certificate
                            abstractable ordered linkMembership firing with
                          ⟨nextAbstractable, semanticStep⟩
                        exact fromCore nextAbstractable
                          (semanticStep.causallyThreaded structural coherent)
                          (by simp [processWorklistLink, linkLookup,
                            leftLookup, rightLookup, same, firing])

/-- One scheduler attempt preserves semantic thread connectivity.  No-op
branches leave the executable core unchanged; successful par and tensor
branches are discharged by their independent Figure-5 refinement steps. -/
private theorem processWorklistLink_threadConnected
    {certificate : Certificate} {consumers : Array (List Nat)}
    {index : Nat} {state : UnificationWorklistState}
    (abstractable : state.core.Abstractable certificate)
    (ordered : state.core.OrderedParents)
    (connected :
      UnificationMarking.ThreadConnected
        (state.core.toMarking certificate abstractable)) :
    UnificationMarking.ThreadConnected
      ((processWorklistLink certificate consumers index state).core.toMarking
        certificate
        (processWorklistLink_core_abstractable abstractable ordered)) := by
  have fromCore {core : UnificationState}
      (coreAbstractable : core.Abstractable certificate)
      (coreConnected :
        UnificationMarking.ThreadConnected
          (core.toMarking certificate coreAbstractable))
      (equation :
        core =
          (processWorklistLink certificate consumers index state).core) :
      UnificationMarking.ThreadConnected
        ((processWorklistLink certificate consumers index state).core.toMarking
          certificate
          (processWorklistLink_core_abstractable abstractable ordered)) :=
    UnificationState.threadConnected_of_eq
      coreAbstractable _ equation coreConnected
  unfold UnificationMarking.ThreadConnected
  intro firstVertex secondVertex firstToken secondToken
    firstMarked secondMarked synchronized
  cases linkLookup : certificate.links[index]? with
  | none =>
      have transported : UnificationMarking.ThreadConnected _ :=
        fromCore abstractable connected
        (by simp [processWorklistLink, linkLookup])
      exact transported firstMarked secondMarked synchronized
  | some link =>
      have linkMembership : link ∈ certificate.links :=
        List.mem_of_getElem? linkLookup
      cases link with
      | «axiom» left right =>
          have transported : UnificationMarking.ThreadConnected _ :=
            fromCore abstractable connected
            (by simp [processWorklistLink, linkLookup])
          exact transported firstMarked secondMarked synchronized
      | «par» left right conclusion =>
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              have transported : UnificationMarking.ThreadConnected _ :=
                fromCore abstractable connected
                (by simp [processWorklistLink, linkLookup, leftLookup])
              exact transported firstMarked secondMarked synchronized
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  have transported : UnificationMarking.ThreadConnected _ :=
                    fromCore abstractable connected
                    (by simp [processWorklistLink, linkLookup, leftLookup,
                      rightLookup])
                  exact transported firstMarked secondMarked synchronized
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    cases firing :
                        firePar? state.core left right conclusion with
                    | none =>
                        have transported :
                            UnificationMarking.ThreadConnected _ :=
                          fromCore abstractable connected
                          (by simp [processWorklistLink, linkLookup,
                            leftLookup, rightLookup, firing])
                        exact transported firstMarked secondMarked synchronized
                    | some nextCore =>
                        rcases firePar?_refines_forward certificate
                            abstractable linkMembership firing with
                          ⟨_nextAbstractable, semanticStep⟩
                        have preserved :
                            UnificationMarking.ThreadConnected
                              (nextCore.toMarking certificate
                                _nextAbstractable) :=
                          semanticStep.threadConnected connected
                        have transported :
                            UnificationMarking.ThreadConnected _ :=
                          fromCore _nextAbstractable preserved
                          (by simp [processWorklistLink, linkLookup,
                            leftLookup, rightLookup, firing])
                        exact transported firstMarked secondMarked synchronized
                  · have transported :
                        UnificationMarking.ThreadConnected _ :=
                      fromCore abstractable connected
                      (by simp [processWorklistLink, linkLookup,
                        leftLookup, rightLookup, same])
                    exact transported firstMarked secondMarked synchronized
      | «tensor» left right conclusion =>
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              have transported : UnificationMarking.ThreadConnected _ :=
                fromCore abstractable connected
                (by simp [processWorklistLink, linkLookup, leftLookup])
              exact transported firstMarked secondMarked synchronized
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  have transported : UnificationMarking.ThreadConnected _ :=
                    fromCore abstractable connected
                    (by simp [processWorklistLink, linkLookup, leftLookup,
                      rightLookup])
                  exact transported firstMarked secondMarked synchronized
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    have transported : UnificationMarking.ThreadConnected _ :=
                      fromCore abstractable connected
                      (by simp [processWorklistLink, linkLookup,
                        leftLookup, rightLookup])
                    exact transported firstMarked secondMarked synchronized
                  · cases firing :
                        fireTensor? state.core left right conclusion with
                    | none =>
                        have transported :
                            UnificationMarking.ThreadConnected _ :=
                          fromCore abstractable connected
                          (by simp [processWorklistLink, linkLookup,
                            leftLookup, rightLookup, same, firing])
                        exact transported firstMarked secondMarked synchronized
                    | some nextCore =>
                        rcases fireTensor?_refines_unify certificate
                            abstractable ordered linkMembership firing with
                          ⟨_nextAbstractable, semanticStep⟩
                        have preserved :
                            UnificationMarking.ThreadConnected
                              (nextCore.toMarking certificate
                                _nextAbstractable) :=
                          semanticStep.threadConnected connected
                        have transported :
                            UnificationMarking.ThreadConnected _ :=
                          fromCore _nextAbstractable preserved
                          (by simp [processWorklistLink, linkLookup,
                            leftLookup, rightLookup, same, firing])
                        exact transported firstMarked secondMarked synchronized

/-- Processing one worklist entry never removes an existing raw formula
assignment.  Scheduler-only branches leave the executable core unchanged;
successful connective firings use the conclusion-local monotonicity lemmas. -/
private theorem processWorklistLink_preserves_assigned
    {certificate : Certificate} {consumers : Array (List Nat)}
    {index : Nat} {state : UnificationWorklistState}
    (structural : certificate.StructurallyWellFormed)
    (abstractable : state.core.Abstractable certificate)
    {vertex : Vertex}
    (marked : state.core.assignedToken? vertex ≠ none) :
    ((processWorklistLink certificate consumers index state).core
      |>.assignedToken? vertex) ≠ none := by
  cases linkLookup : certificate.links[index]? with
  | none =>
      simpa [processWorklistLink, linkLookup] using marked
  | some link =>
      have linkMembership : link ∈ certificate.links :=
        List.mem_of_getElem? linkLookup
      cases link with
      | «axiom» left right =>
          simpa [processWorklistLink, linkLookup] using marked
      | «par» left right conclusion =>
          have wellFormed :
              certificate.LinkWellFormed
                (.par left right conclusion) :=
            structural.2.2.2.2.1 _ linkMembership
          rcases wellFormed with
            ⟨_premisesDifferent, _leftConclusionDifferent,
              _rightConclusionDifferent, _leftBound, _rightBound,
              conclusionBound, _typing⟩
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              simpa [processWorklistLink, linkLookup, leftLookup] using
                marked
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  simpa [processWorklistLink, linkLookup, leftLookup,
                    rightLookup] using marked
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    cases firing :
                        firePar? state.core left right conclusion with
                    | none =>
                        simpa [processWorklistLink, linkLookup,
                          leftLookup, rightLookup, firing] using marked
                    | some nextCore =>
                        have nextMarked :
                            nextCore.assignedToken? vertex ≠ none :=
                          firePar?_success_preserves_assigned
                            abstractable conclusionBound marked firing
                        simpa [processWorklistLink, linkLookup,
                          leftLookup, rightLookup, firing] using nextMarked
                  · simpa [processWorklistLink, linkLookup, leftLookup,
                      rightLookup, same] using marked
      | «tensor» left right conclusion =>
          have wellFormed :
              certificate.LinkWellFormed
                (.tensor left right conclusion) :=
            structural.2.2.2.2.1 _ linkMembership
          rcases wellFormed with
            ⟨_premisesDifferent, _leftConclusionDifferent,
              _rightConclusionDifferent, _leftBound, _rightBound,
              conclusionBound, _typing⟩
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              simpa [processWorklistLink, linkLookup, leftLookup] using
                marked
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  simpa [processWorklistLink, linkLookup, leftLookup,
                    rightLookup] using marked
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    simpa [processWorklistLink, linkLookup, leftLookup,
                      rightLookup] using marked
                  · cases firing :
                      fireTensor? state.core left right conclusion with
                    | none =>
                        simpa [processWorklistLink, linkLookup,
                          leftLookup, rightLookup, same, firing] using
                            marked
                    | some nextCore =>
                        have nextMarked :
                            nextCore.assignedToken? vertex ≠ none :=
                          fireTensor?_success_preserves_assigned
                            abstractable conclusionBound marked firing
                        simpa [processWorklistLink, linkLookup,
                          leftLookup, rightLookup, same, firing] using
                            nextMarked

/-- Every worklist processing branch preserves the ordered union-find forest.
This is the concrete no-cycle guarantee needed by all later representative
and scheduler arguments. -/
private theorem processWorklistLink_core_ordered
    {certificate : Certificate} {consumers : Array (List Nat)}
    {index : Nat} {state : UnificationWorklistState}
    (ordered : state.core.OrderedParents) :
    (processWorklistLink certificate consumers index state).core
      |>.OrderedParents := by
  intro token parent parentLookup
  cases linkLookup : certificate.links[index]? with
  | none =>
      apply ordered
      simpa [processWorklistLink, linkLookup] using parentLookup
  | some link =>
      cases link with
      | «axiom» left right =>
          apply ordered
          simpa [processWorklistLink, linkLookup] using parentLookup
      | «par» left right conclusion =>
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              apply ordered
              simpa [processWorklistLink, linkLookup, leftLookup] using
                parentLookup
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  apply ordered
                  simpa [processWorklistLink, linkLookup, leftLookup,
                    rightLookup] using parentLookup
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    cases firing :
                        firePar? state.core left right conclusion with
                    | none =>
                        apply ordered
                        simpa [processWorklistLink, linkLookup, leftLookup,
                          rightLookup, firing] using parentLookup
                    | some nextCore =>
                        have nextOrdered : nextCore.OrderedParents :=
                          firePar?_success_ordered ordered firing
                        apply nextOrdered
                        simpa [processWorklistLink, linkLookup, leftLookup,
                          rightLookup, firing] using parentLookup
                  · apply ordered
                    simpa [processWorklistLink, linkLookup, leftLookup,
                      rightLookup, same] using parentLookup
      | «tensor» left right conclusion =>
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              apply ordered
              simpa [processWorklistLink, linkLookup, leftLookup] using
                parentLookup
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  apply ordered
                  simpa [processWorklistLink, linkLookup, leftLookup,
                    rightLookup] using parentLookup
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    apply ordered
                    simpa [processWorklistLink, linkLookup, leftLookup,
                      rightLookup] using parentLookup
                  · cases firing :
                        fireTensor? state.core left right conclusion with
                    | none =>
                        apply ordered
                        simpa [processWorklistLink, linkLookup, leftLookup,
                          rightLookup, same, firing] using parentLookup
                    | some nextCore =>
                        have nextOrdered : nextCore.OrderedParents :=
                          fireTensor?_success_ordered ordered firing
                        apply nextOrdered
                        simpa [processWorklistLink, linkLookup, leftLookup,
                          rightLookup, same, firing] using parentLookup

/-- Every worklist processing branch preserves formula consistency of all live
partial derivation components.  Thus the event-driven scheduler cannot create
a component whose stored boundary disagrees with its derivation tree. -/
private theorem processWorklistLink_core_componentsFormulaConsistent
    {certificate : Certificate} {consumers : Array (List Nat)}
    {index : Nat} {state : UnificationWorklistState}
    (structural : certificate.StructurallyWellFormed)
    (consistent : state.core.ComponentsFormulaConsistent certificate) :
    (processWorklistLink certificate consumers index state).core
      |>.ComponentsFormulaConsistent certificate := by
  intro componentIndex component componentLookup
  cases linkLookup : certificate.links[index]? with
  | none =>
      apply consistent
      simpa [processWorklistLink, linkLookup] using componentLookup
  | some link =>
      have linkMembership : link ∈ certificate.links :=
        List.mem_of_getElem? linkLookup
      have wellFormed : certificate.LinkWellFormed link :=
        structural.2.2.2.2.1 link linkMembership
      cases link with
      | «axiom» left right =>
          apply consistent
          simpa [processWorklistLink, linkLookup] using componentLookup
      | «par» left right conclusion =>
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              apply consistent
              simpa [processWorklistLink, linkLookup, leftLookup] using
                componentLookup
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  apply consistent
                  simpa [processWorklistLink, linkLookup, leftLookup,
                    rightLookup] using componentLookup
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    cases firing :
                        firePar? state.core left right conclusion with
                    | none =>
                        apply consistent
                        simpa [processWorklistLink, linkLookup, leftLookup,
                          rightLookup, firing] using componentLookup
                    | some nextCore =>
                        have nextConsistent :
                            nextCore.ComponentsFormulaConsistent certificate :=
                          firePar?_success_componentsFormulaConsistent
                            consistent wellFormed firing
                        apply nextConsistent
                        simpa [processWorklistLink, linkLookup, leftLookup,
                          rightLookup, firing] using componentLookup
                  · apply consistent
                    simpa [processWorklistLink, linkLookup, leftLookup,
                      rightLookup, same] using componentLookup
      | «tensor» left right conclusion =>
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              apply consistent
              simpa [processWorklistLink, linkLookup, leftLookup] using
                componentLookup
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  apply consistent
                  simpa [processWorklistLink, linkLookup, leftLookup,
                    rightLookup] using componentLookup
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    apply consistent
                    simpa [processWorklistLink, linkLookup, leftLookup,
                      rightLookup] using componentLookup
                  · cases firing :
                        fireTensor? state.core left right conclusion with
                    | none =>
                        apply consistent
                        simpa [processWorklistLink, linkLookup, leftLookup,
                          rightLookup, same, firing] using componentLookup
                    | some nextCore =>
                        have nextConsistent :
                            nextCore.ComponentsFormulaConsistent certificate :=
                          fireTensor?_success_componentsFormulaConsistent
                            consistent wellFormed firing
                        apply nextConsistent
                        simpa [processWorklistLink, linkLookup, leftLookup,
                          rightLookup, same, firing] using componentLookup

/-- Every worklist processing branch preserves exact frontier coverage for
all still-pending connectives.  The successful firing branches are precisely
the global par/tensor transport theorems above; scheduler-only branches leave
the executable core unchanged. -/
private theorem processWorklistLink_core_pendingPremisesCovered
    {certificate : Certificate} {consumers : Array (List Nat)}
    {index : Nat} {state : UnificationWorklistState}
    (structural : certificate.StructurallyWellFormed)
    (abstractable : state.core.Abstractable certificate)
    (ordered : state.core.OrderedParents)
    (covered :
      state.core.PendingPremisesCovered certificate) :
    (processWorklistLink certificate consumers index state).core
      |>.PendingPremisesCovered certificate := by
  unfold UnificationState.PendingPremisesCovered
  intro candidate candidateMembership
  cases linkLookup : certificate.links[index]? with
  | none =>
      rw [show
        (processWorklistLink certificate consumers index state).core =
          state.core by
        simp [processWorklistLink, linkLookup]]
      exact covered (link := candidate) candidateMembership
  | some link =>
      have linkMembership : link ∈ certificate.links :=
        List.mem_of_getElem? linkLookup
      cases link with
      | «axiom» left right =>
          rw [show
            (processWorklistLink certificate consumers index state).core =
              state.core by
            simp [processWorklistLink, linkLookup]]
          exact covered (link := candidate) candidateMembership
      | «par» left right conclusion =>
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              rw [show
                (processWorklistLink certificate consumers index state).core =
                  state.core by
                simp [processWorklistLink, linkLookup, leftLookup]]
              exact covered (link := candidate) candidateMembership
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  rw [show
                    (processWorklistLink certificate consumers index
                      state).core = state.core by
                    simp [processWorklistLink, linkLookup, leftLookup,
                      rightLookup]]
                  exact covered (link := candidate) candidateMembership
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    cases firing :
                        firePar? state.core left right conclusion with
                    | none =>
                        rw [show
                          (processWorklistLink certificate consumers index
                            state).core = state.core by
                          simp [processWorklistLink, linkLookup,
                            leftLookup, rightLookup, firing]]
                        exact covered (link := candidate)
                          candidateMembership
                    | some nextCore =>
                        have nextCovered :
                            nextCore.PendingPremisesCovered certificate :=
                          firePar?_success_pendingPremisesCovered
                            structural abstractable covered
                              linkMembership firing
                        rw [show
                          (processWorklistLink certificate consumers index
                            state).core = nextCore by
                          simp [processWorklistLink, linkLookup,
                            leftLookup, rightLookup, firing]]
                        exact nextCovered (link := candidate)
                          candidateMembership
                  · rw [show
                      (processWorklistLink certificate consumers index
                        state).core = state.core by
                      simp [processWorklistLink, linkLookup, leftLookup,
                        rightLookup, same]]
                    exact covered (link := candidate) candidateMembership
      | «tensor» left right conclusion =>
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              rw [show
                (processWorklistLink certificate consumers index state).core =
                  state.core by
                simp [processWorklistLink, linkLookup, leftLookup]]
              exact covered (link := candidate) candidateMembership
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  rw [show
                    (processWorklistLink certificate consumers index
                      state).core = state.core by
                    simp [processWorklistLink, linkLookup, leftLookup,
                      rightLookup]]
                  exact covered (link := candidate) candidateMembership
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    rw [show
                      (processWorklistLink certificate consumers index
                        state).core = state.core by
                      simp [processWorklistLink, linkLookup, leftLookup,
                        rightLookup]]
                    exact covered (link := candidate) candidateMembership
                  · cases firing :
                        fireTensor? state.core left right conclusion with
                    | none =>
                        rw [show
                          (processWorklistLink certificate consumers index
                            state).core = state.core by
                          simp [processWorklistLink, linkLookup,
                            leftLookup, rightLookup, same, firing]]
                        exact covered (link := candidate)
                          candidateMembership
                    | some nextCore =>
                        have nextCovered :
                            nextCore.PendingPremisesCovered certificate :=
                          fireTensor?_success_pendingPremisesCovered
                            structural abstractable ordered covered
                              linkMembership firing
                        rw [show
                          (processWorklistLink certificate consumers index
                            state).core = nextCore by
                          simp [processWorklistLink, linkLookup,
                            leftLookup, rightLookup, same, firing]]
                        exact nextCovered (link := candidate)
                          candidateMembership

/-- The four executable-core invariants needed by pure worklist
completeness. -/
private def WorklistCoreInvariant (certificate : Certificate)
    (state : UnificationWorklistState) : Prop :=
  state.core.Abstractable certificate ∧
    state.core.OrderedParents ∧
      state.core.ComponentsFormulaConsistent certificate ∧
        state.core.PendingPremisesCovered certificate

/-- Exact concrete scheduler discipline: both registries are duplicate-free
and their membership is completely reflected by the corresponding true
flags. -/
private def WorklistExactDiscipline
    (state : UnificationWorklistState) : Prop :=
  QueueFlagComplete state ∧
    QueueNodup state ∧
      WaitingFlagComplete state ∧
        WaitingNodup state

/-- The complete production-run invariant: kernel-level partial-derivation
correctness, scheduler coverage, sound deduplication flags, exact carrier
sizes, and constructor-level provenance for all queue and waiting entries. -/
private def WorklistRunInvariant (certificate : Certificate)
    (state : UnificationWorklistState) : Prop :=
  WorklistCoreInvariant certificate state ∧
    SchedulerCoverage certificate state ∧
      QueueFlagSound state ∧
        WaitingFlagSound state ∧
          state.queued.size = certificate.links.length ∧
            state.waitingFlags.size = state.queued.size ∧
              QueueConnectiveSound certificate state ∧
                WaitingParSound certificate state ∧
                  WorklistExactDiscipline state

/-- Every state satisfying the production invariant has at most one queued
and one waiting entry per submitted link slot. -/
private theorem WorklistRunInvariant.registryLengthBounds
    {certificate : Certificate} {state : UnificationWorklistState}
    (invariant : WorklistRunInvariant certificate state) :
    state.queue.length ≤ certificate.links.length ∧
      state.waiting.length ≤ certificate.links.length := by
  rcases invariant with
    ⟨_core, _coverage, _queueSound, _waitingSound,
      queueSize, waitingSize, _queueProvenance,
      _waitingProvenance, queueComplete, queueNodup,
      waitingComplete, waitingNodup⟩
  constructor
  · calc
      state.queue.length ≤ state.queued.size :=
        queueNodup.length_le_queuedSize queueComplete
      _ = certificate.links.length := queueSize
  · calc
      state.waiting.length ≤ state.waitingFlags.size :=
        waitingNodup.length_le_waitingFlagsSize waitingComplete
      _ = state.queued.size := waitingSize
      _ = certificate.links.length := queueSize

/-- Successful canonical axiom initialization inherits semantic thread
connectivity from the empty marking through its finite start execution. -/
private theorem startAxioms?_success_threadConnected
    {certificate : Certificate} {started : UnificationState}
    (equation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    ∃ startedAbstractable : started.Abstractable certificate,
      UnificationMarking.ThreadConnected
        (started.toMarking certificate startedAbstractable) := by
  rcases certificate.startAxioms?_success_refines
      (initialUnificationState_abstractable certificate)
      (initialUnificationState_identityParents certificate)
      (fun _ membership => membership) equation with
    ⟨startedAbstractable, _startedIdentity, execution⟩
  exact
    ⟨startedAbstractable,
      execution.threadConnected
        (initialUnificationState_threadConnected certificate)⟩

/-- Successful canonical axiom initialization is causally closed and threads
every active retained reference edge. -/
private theorem startAxioms?_success_causallyThreaded
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (equation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    ∃ startedAbstractable : started.Abstractable certificate,
      UnificationMarking.CausallyThreaded
        (started.toMarking certificate startedAbstractable) := by
  rcases certificate.startAxioms?_success_refines
      (initialUnificationState_abstractable certificate)
      (initialUnificationState_identityParents certificate)
      (fun _ membership => membership) equation with
    ⟨startedAbstractable, _startedIdentity, execution⟩
  exact
    ⟨startedAbstractable,
      execution.causallyThreaded structural
        (initialUnificationState_causallyThreaded certificate)⟩

/-- Successful eager axiom initialization from the canonical empty state
establishes the complete core invariant bundle required by the event-driven
worklist. -/
private theorem startAxioms?_success_initializeWorklist_coreInvariant
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (equation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    WorklistCoreInvariant certificate
      (initializeWorklist certificate started) := by
  have submitted :
      ∀ link, link ∈ certificate.links →
        link ∈ certificate.links := by
    intro link membership
    exact membership
  rcases certificate.startAxioms?_success_refines
      (initialUnificationState_abstractable certificate)
      (initialUnificationState_identityParents certificate)
      submitted equation with
    ⟨startedAbstractable, startedIdentity, _execution⟩
  have startedConsistent :
      started.ComponentsFormulaConsistent certificate :=
    certificate.startAxioms?_success_componentsFormulaConsistent
      structural
      (initialUnificationState_componentsFormulaConsistent certificate)
      submitted equation
  rcases certificate.startAxioms?_success_identityAlignedCovered
      structural
      (initialUnificationState_identityParents certificate)
      (initialUnificationState_componentsParentsAligned certificate)
      (initialUnificationState_pendingPremisesCovered certificate)
      submitted equation with
    ⟨_identityAgain, _aligned, startedCovered⟩
  have startedOrdered : started.OrderedParents :=
    startedIdentity.orderedParents
  change
    started.Abstractable certificate ∧
      started.OrderedParents ∧
        started.ComponentsFormulaConsistent certificate ∧
          started.PendingPremisesCovered certificate
  exact
    ⟨startedAbstractable, startedOrdered,
      startedConsistent, startedCovered⟩

/-- Successful canonical axiom initialization plus initial connective arming
establishes the complete production-run invariant. -/
private theorem startAxioms?_success_initializeWorklist_runInvariant
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (equation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    WorklistRunInvariant certificate
      (initializeWorklist certificate started) := by
  refine
    ⟨startAxioms?_success_initializeWorklist_coreInvariant
        structural equation,
      initializeWorklist_schedulerCoverage certificate started,
      initializeWorklist_queueFlagSound certificate started,
      initializeWorklist_waitingFlagSound certificate started,
      initializeWorklist_queued_size certificate started,
      ?_,
      initializeWorklist_queueConnectiveSound certificate started,
      initializeWorklist_waitingParSound certificate started,
      initializeWorklist_queueFlagComplete certificate started,
      initializeWorklist_queueNodup certificate started,
      initializeWorklist_waitingFlagComplete certificate started,
      initializeWorklist_waitingNodup certificate started⟩
  rw [initializeWorklist_waitingFlags_size,
    initializeWorklist_queued_size]

/-- One worklist processing attempt preserves the complete core invariant
bundle. -/
private theorem processWorklistLink_coreInvariant
    {certificate : Certificate} {consumers : Array (List Nat)}
    {index : Nat} {state : UnificationWorklistState}
    (structural : certificate.StructurallyWellFormed)
    (invariant : WorklistCoreInvariant certificate state) :
    WorklistCoreInvariant certificate
      (processWorklistLink certificate consumers index state) := by
  rcases invariant with
    ⟨abstractable, ordered, consistent, covered⟩
  exact
    ⟨processWorklistLink_core_abstractable abstractable ordered,
      processWorklistLink_core_ordered ordered,
      processWorklistLink_core_componentsFormulaConsistent
        structural consistent,
      processWorklistLink_core_pendingPremisesCovered
        structural abstractable ordered covered⟩

/-- Processing the popped head transports scheduler coverage for every other
connective.  Successful firings use exact consumer fan-out; a waiting par
uses scheduler-only registration; and every no-op branch preserves the
pre-existing classification definitionally. -/
private theorem processWorklistLink_schedulerCoverageExcept
    {certificate : Certificate} {index : Nat}
    {state : UnificationWorklistState}
    (structural : certificate.StructurallyWellFormed)
    (abstractable : state.core.Abstractable certificate)
    (ordered : state.core.OrderedParents)
    (coverage :
      SchedulerCoverageExcept certificate state index)
    (queueSound : QueueFlagSound state)
    (queueSize :
      state.queued.size = certificate.links.length) :
    SchedulerCoverageExcept certificate
      (processWorklistLink certificate
        certificate.worklistConsumers index state)
      index := by
  intro candidateIndex candidateLink candidateLookup
    candidateConnective candidateDifferent
  cases linkLookup : certificate.links[index]? with
  | none =>
      simpa [processWorklistLink, linkLookup] using
        coverage candidateLookup candidateConnective candidateDifferent
  | some link =>
      have linkMembership : link ∈ certificate.links :=
        List.mem_of_getElem? linkLookup
      cases link with
      | «axiom» left right =>
          simpa [processWorklistLink, linkLookup] using
            coverage candidateLookup candidateConnective
              candidateDifferent
      | «par» left right conclusion =>
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              simpa [processWorklistLink, linkLookup, leftLookup] using
                coverage candidateLookup candidateConnective
                  candidateDifferent
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  simpa [processWorklistLink, linkLookup, leftLookup,
                    rightLookup] using
                      coverage candidateLookup candidateConnective
                        candidateDifferent
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    cases firing :
                        firePar? state.core left right conclusion with
                    | none =>
                        simpa [processWorklistLink, linkLookup,
                          leftLookup, rightLookup, firing] using
                            coverage candidateLookup candidateConnective
                              candidateDifferent
                    | some nextCore =>
                        have transported :=
                          (coverage.afterFirePar
                              structural abstractable queueSound queueSize
                                linkMembership firing)
                            candidateLookup candidateConnective
                              candidateDifferent
                        simpa [processWorklistLink, linkLookup,
                          leftLookup, rightLookup, firing] using
                            transported
                  · have registered :=
                      (coverage.addWaiting index)
                        candidateLookup candidateConnective
                          candidateDifferent
                    simpa [processWorklistLink, linkLookup, leftLookup,
                      rightLookup, same] using
                        registered
      | «tensor» left right conclusion =>
          cases leftLookup : state.core.tokenAt? left with
          | none =>
              simpa [processWorklistLink, linkLookup, leftLookup] using
                coverage candidateLookup candidateConnective
                  candidateDifferent
          | some leftToken =>
              cases rightLookup : state.core.tokenAt? right with
              | none =>
                  simpa [processWorklistLink, linkLookup, leftLookup,
                    rightLookup] using
                      coverage candidateLookup candidateConnective
                        candidateDifferent
              | some rightToken =>
                  by_cases same : leftToken = rightToken
                  · subst rightToken
                    simpa [processWorklistLink, linkLookup, leftLookup,
                      rightLookup] using
                        coverage candidateLookup candidateConnective
                          candidateDifferent
                  · cases firing :
                        fireTensor? state.core left right conclusion with
                    | none =>
                        simpa [processWorklistLink, linkLookup,
                          leftLookup, rightLookup, same, firing] using
                            coverage candidateLookup candidateConnective
                              candidateDifferent
                    | some nextCore =>
                        have transported :=
                          (coverage.afterFireTensor
                              structural abstractable ordered queueSound
                                queueSize linkMembership firing)
                            candidateLookup candidateConnective
                              candidateDifferent
                        simpa [processWorklistLink, linkLookup,
                          leftLookup, rightLookup, same, firing] using
                            transported

/-- Processing a concrete submitted connective always reclassifies that
specific popped link: it fires, stays idle, becomes a registered waiting par,
or exposes a tensor deadlock.  The only operational-totality premise beyond
the token/array invariants is exact coverage of marked premises for pending
links.  Whole-scheduler preservation additionally has to transport every
*other* connective across this core update. -/
private theorem processWorklistLink_processed_status
    {certificate : Certificate} {consumers : Array (List Nat)}
    {index : Nat} {link : Link} {state : UnificationWorklistState}
    (structural : certificate.StructurallyWellFormed)
    (abstractable : state.core.Abstractable certificate)
    (premisesCovered :
      state.core.PendingPremisesCovered certificate)
    (waitingSound : WaitingFlagSound state)
    (queueSize :
      state.queued.size = certificate.links.length)
    (waitingFlagSize :
      state.waitingFlags.size = state.queued.size)
    (lookup : certificate.links[index]? = some link)
    (connective : link.isConnective = true) :
    ConnectiveSchedulerStatus
      (processWorklistLink certificate consumers index state)
      index link := by
  have linkMembership : link ∈ certificate.links :=
    List.mem_of_getElem? lookup
  have linkBound : index < certificate.links.length :=
    (List.getElem?_eq_some_iff.mp lookup).1
  have queueBound : index < state.queued.size := by
    simpa [queueSize] using linkBound
  have waitingBound : index < state.waitingFlags.size := by
    simpa [waitingFlagSize] using queueBound
  cases link with
  | «axiom» left right =>
      simp [Link.isConnective] at connective
  | «par» left right conclusion =>
      have wellFormed :
          certificate.LinkWellFormed
            (.par left right conclusion) :=
        structural.2.2.2.2.1 _ linkMembership
      rcases wellFormed with
        ⟨premisesDifferent, _leftConclusionDifferent,
          _rightConclusionDifferent, _leftBound, _rightBound,
          conclusionBound, _typing⟩
      cases leftLookup :
          state.core.tokenAt? left with
      | none =>
          simpa [processWorklistLink, lookup, leftLookup] using
            (ConnectiveSchedulerStatus.idlePar
              (state := state) (index := index)
              (conclusion := conclusion) (Or.inl leftLookup))
      | some leftToken =>
          cases rightLookup :
              state.core.tokenAt? right with
          | none =>
              simpa [processWorklistLink, lookup, leftLookup,
                rightLookup] using
                (ConnectiveSchedulerStatus.idlePar
                  (state := state) (index := index)
                  (conclusion := conclusion) (Or.inr rightLookup))
          | some rightToken =>
              by_cases same : leftToken = rightToken
              · subst rightToken
                cases firing :
                    firePar? state.core left right conclusion with
                | none =>
                    have conclusionMarked :
                        state.core.assignedToken? conclusion ≠ none := by
                      intro unassigned
                      have conclusionReady :=
                        abstractable.markSlotReady_of_unassigned
                          conclusionBound unassigned
                      rcases firePar?_exists_of_ready
                          premisesCovered linkMembership
                          premisesDifferent conclusionReady
                          leftLookup rightLookup with
                        ⟨next, success⟩
                      rw [firing] at success
                      contradiction
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, firing] using
                      (ConnectiveSchedulerStatus.firedPar
                        (state := state) (index := index)
                        conclusionMarked)
                | some nextCore =>
                    have conclusionMarked :
                        nextCore.assignedToken? conclusion ≠ none :=
                      firePar?_success_conclusion_marked
                        abstractable conclusionBound firing
                    apply ConnectiveSchedulerStatus.firedPar
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, firing] using conclusionMarked
              · have different : leftToken ≠ rightToken := same
                have registered :
                    index ∈
                      (addWaiting index state).waiting :=
                  waitingSound.mem_addWaiting waitingBound
                have status :
                    ConnectiveSchedulerStatus
                      (addWaiting index state) index
                      (.par left right conclusion) := by
                  apply ConnectiveSchedulerStatus.waitingPar
                  · simpa using leftLookup
                  · simpa using rightLookup
                  · exact different
                  · exact registered
                  · simpa using queueBound
                simpa [processWorklistLink, lookup, leftLookup,
                  rightLookup, same] using status
  | «tensor» left right conclusion =>
      have wellFormed :
          certificate.LinkWellFormed
            (.tensor left right conclusion) :=
        structural.2.2.2.2.1 _ linkMembership
      rcases wellFormed with
        ⟨_premisesDifferent, _leftConclusionDifferent,
          _rightConclusionDifferent, _leftBound, _rightBound,
          conclusionBound, _typing⟩
      cases leftLookup :
          state.core.tokenAt? left with
      | none =>
          simpa [processWorklistLink, lookup, leftLookup] using
            (ConnectiveSchedulerStatus.idleTensor
              (state := state) (index := index)
              (conclusion := conclusion) (Or.inl leftLookup))
      | some leftToken =>
          cases rightLookup :
              state.core.tokenAt? right with
          | none =>
              simpa [processWorklistLink, lookup, leftLookup,
                rightLookup] using
                (ConnectiveSchedulerStatus.idleTensor
                  (state := state) (index := index)
                  (conclusion := conclusion) (Or.inr rightLookup))
          | some rightToken =>
              by_cases same : leftToken = rightToken
              · subst rightToken
                simpa [processWorklistLink, lookup, leftLookup,
                  rightLookup] using
                  (ConnectiveSchedulerStatus.tensorDeadlock
                    (state := state) (index := index)
                    leftLookup rightLookup)
              · cases firing :
                    fireTensor? state.core left right conclusion with
                | none =>
                    have conclusionMarked :
                        state.core.assignedToken? conclusion ≠ none := by
                      intro unassigned
                      have conclusionReady :=
                        abstractable.markSlotReady_of_unassigned
                          conclusionBound unassigned
                      rcases fireTensor?_exists_of_ready
                          premisesCovered linkMembership conclusionReady
                          leftLookup rightLookup same with
                        ⟨next, success⟩
                      rw [firing] at success
                      contradiction
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, same, firing] using
                      (ConnectiveSchedulerStatus.firedTensor
                        (state := state) (index := index)
                        conclusionMarked)
                | some nextCore =>
                    have conclusionMarked :
                        nextCore.assignedToken? conclusion ≠ none :=
                      fireTensor?_success_conclusion_marked
                        abstractable conclusionBound firing
                    apply ConnectiveSchedulerStatus.firedTensor
                    simpa [processWorklistLink, lookup, leftLookup,
                      rightLookup, same, firing] using conclusionMarked

/-- Once the popped connective is known to be a submitted connective, one
processing step closes the temporary coverage hole: the dedicated processed
status theorem covers that index and the transport theorem covers every other
index. -/
private theorem processWorklistLink_schedulerCoverage
    {certificate : Certificate} {index : Nat} {link : Link}
    {state : UnificationWorklistState}
    (structural : certificate.StructurallyWellFormed)
    (abstractable : state.core.Abstractable certificate)
    (ordered : state.core.OrderedParents)
    (premisesCovered :
      state.core.PendingPremisesCovered certificate)
    (coverage :
      SchedulerCoverageExcept certificate state index)
    (queueSound : QueueFlagSound state)
    (waitingSound : WaitingFlagSound state)
    (queueSize :
      state.queued.size = certificate.links.length)
    (waitingFlagSize :
      state.waitingFlags.size = state.queued.size)
    (lookup : certificate.links[index]? = some link)
    (connective : link.isConnective = true) :
    SchedulerCoverage certificate
      (processWorklistLink certificate
        certificate.worklistConsumers index state) := by
  intro candidateIndex candidateLink candidateLookup
    candidateConnective
  by_cases same : candidateIndex = index
  · subst candidateIndex
    have linkEquality : candidateLink = link := by
      rw [lookup] at candidateLookup
      injection candidateLookup with equality
      exact equality.symm
    subst candidateLink
    exact processWorklistLink_processed_status
      structural abstractable premisesCovered waitingSound
        queueSize waitingFlagSize lookup connective
  · exact
      (processWorklistLink_schedulerCoverageExcept
          structural abstractable ordered coverage queueSound queueSize)
        candidateLookup candidateConnective same

/-- One atomic pop-and-process transition preserves the complete production
invariant. Queue provenance discharges the formerly external assumption that
the popped number denotes a submitted connective. -/
private theorem popProcessWorklist_runInvariant
    {certificate : Certificate}
    {state popped : UnificationWorklistState} {index : Nat}
    (structural : certificate.StructurallyWellFormed)
    (invariant : WorklistRunInvariant certificate state)
    (popEquation :
      popWorklist? state = some (index, popped)) :
    WorklistRunInvariant certificate
      (processWorklistLink certificate
        certificate.worklistConsumers index popped) := by
  rcases invariant with
    ⟨coreInvariant, coverage, queueFlagSound,
      waitingFlagSound, queueSize, waitingSize,
      queueConnectiveSound, waitingParSound,
      exactDiscipline⟩
  rcases exactDiscipline with
    ⟨queueFlagComplete, queueNodup,
      waitingFlagComplete, waitingNodup⟩
  have queueBounded :
      QueueBounded state :=
    queueConnectiveSound.queueBounded queueSize
  rcases popWorklist?_some_invariants
      queueFlagSound queueBounded popEquation with
    ⟨_headBound, poppedQueueFlagSound, _poppedBounded⟩
  rcases popWorklist?_some_provenance
      queueConnectiveSound waitingParSound popEquation with
    ⟨submitted, poppedQueueConnectiveSound,
      poppedWaitingParSound⟩
  rcases submitted with ⟨link, lookup, connective⟩
  rcases popWorklist?_success_bookkeeping
      waitingFlagSound popEquation with
    ⟨poppedWaitingFlagSound, poppedQueueCarrier,
      poppedWaitingCarrier⟩
  rcases popWorklist?_success_exactDiscipline
      queueFlagComplete queueNodup
        waitingFlagComplete waitingNodup popEquation with
    ⟨poppedQueueFlagComplete, poppedQueueNodup,
      poppedWaitingFlagComplete, poppedWaitingNodup⟩
  have poppedQueueSize :
      popped.queued.size = certificate.links.length := by
    calc
      popped.queued.size = state.queued.size := poppedQueueCarrier
      _ = certificate.links.length := queueSize
  have poppedWaitingSize :
      popped.waitingFlags.size = popped.queued.size := by
    calc
      popped.waitingFlags.size =
          state.waitingFlags.size := poppedWaitingCarrier
      _ = state.queued.size := waitingSize
      _ = popped.queued.size := poppedQueueCarrier.symm
  have poppedCoreEquation :
      popped.core = state.core := by
    cases queueEquation : state.queue with
    | nil =>
        simp [popWorklist?, queueEquation] at popEquation
    | cons head rest =>
        simp [popWorklist?, queueEquation] at popEquation
        rcases popEquation with ⟨rfl, rfl⟩
        rfl
  have poppedCoreInvariant :
      WorklistCoreInvariant certificate popped := by
    unfold WorklistCoreInvariant at coreInvariant ⊢
    simpa [poppedCoreEquation] using coreInvariant
  rcases poppedCoreInvariant with
    ⟨poppedAbstractable, poppedOrdered,
      poppedConsistent, poppedPremisesCovered⟩
  have poppedCoverage :
      SchedulerCoverageExcept certificate popped index :=
    popWorklist?_success_schedulerCoverageExcept
      coverage popEquation
  let next :=
    processWorklistLink certificate
      certificate.worklistConsumers index popped
  have nextCore :
      WorklistCoreInvariant certificate next := by
    exact processWorklistLink_coreInvariant
      structural
        ⟨poppedAbstractable, poppedOrdered,
          poppedConsistent, poppedPremisesCovered⟩
  have nextCoverage :
      SchedulerCoverage certificate next := by
    exact processWorklistLink_schedulerCoverage
      structural poppedAbstractable poppedOrdered
        poppedPremisesCovered poppedCoverage
        poppedQueueFlagSound poppedWaitingFlagSound
        poppedQueueSize poppedWaitingSize lookup connective
  have nextBookkeeping :
      QueueFlagSound next ∧
        WaitingFlagSound next ∧
        next.queued.size = certificate.links.length ∧
        next.waitingFlags.size = next.queued.size := by
    simpa [next] using
      processWorklistLink_bookkeeping
        lookup connective poppedQueueFlagSound
          poppedWaitingFlagSound poppedQueueSize
            poppedWaitingSize
  have nextProvenance :
      QueueConnectiveSound certificate next ∧
        WaitingParSound certificate next := by
    simpa [next] using
      processWorklistLink_provenance
        lookup connective poppedQueueConnectiveSound
          poppedWaitingParSound
  have nextExactDiscipline :
      WorklistExactDiscipline next := by
    exact processWorklistLink_exactDiscipline
      lookup connective poppedQueueFlagComplete
        poppedQueueNodup poppedWaitingFlagComplete
          poppedWaitingNodup
  exact
    ⟨nextCore, nextCoverage,
      nextBookkeeping.1, nextBookkeeping.2.1,
      nextBookkeeping.2.2.1, nextBookkeeping.2.2.2,
      nextProvenance.1, nextProvenance.2,
      nextExactDiscipline⟩

/-- Event-driven saturation. Initial arming and newly marked premises enqueue
only dependent links. A tensor union requeues the current waiting par set.

The fuel is deliberately conservative. Exhaustion produces an incomplete
candidate, never an acceptance. -/
private structure UnificationWorklistRunResult (fuel : Nat) where
  state : UnificationWorklistState
  linkAttempts : Nat
  linkAttemptsBound : linkAttempts ≤ fuel

private def runUnificationWorklist (certificate : Certificate)
    (consumers : Array (List Nat)) :
    (fuel : Nat) → UnificationWorklistState →
      UnificationWorklistRunResult fuel
  | 0, state =>
      { state
        linkAttempts := 0
        linkAttemptsBound := Nat.le_refl 0 }
  | fuel + 1, state =>
      match popWorklist? state with
      | none =>
          { state
            linkAttempts := 0
            linkAttemptsBound := Nat.zero_le _ }
      | some (index, popped) =>
          let tail :=
            runUnificationWorklist certificate consumers fuel
              (processWorklistLink certificate consumers index popped)
          { state := tail.state
            linkAttempts := tail.linkAttempts + 1
            linkAttemptsBound := Nat.succ_le_succ tail.linkAttemptsBound }

/-- Every finite run exactly balances consumed queue entries against all
successful insertions, including insertions produced during the run. -/
private theorem runUnificationWorklist_balance
    (certificate : Certificate) (consumers : Array (List Nat))
    (fuel : Nat) (state : UnificationWorklistState) :
    let result :=
      runUnificationWorklist certificate consumers fuel state
    result.linkAttempts + result.state.queue.length +
          totalWorklistEnqueues state.stats =
      totalWorklistEnqueues result.state.stats +
        state.queue.length := by
  induction fuel generalizing state with
  | zero =>
      simp [runUnificationWorklist]
      omega
  | succ fuel induction =>
      cases popEquation : popWorklist? state with
      | none =>
          simp [runUnificationWorklist, popEquation]
          omega
      | some result =>
          rcases result with ⟨index, popped⟩
          let processed :=
            processWorklistLink certificate consumers index popped
          let tail :=
            runUnificationWorklist certificate consumers fuel processed
          have poppedBalance :=
            popWorklist?_success_balance popEquation
          have processedBalance :
              QueueInsertionBalanced popped processed := by
            simpa [processed] using
              processWorklistLink_balance_total
                certificate consumers index popped
          have tailBalance :
              tail.linkAttempts + tail.state.queue.length +
                    totalWorklistEnqueues processed.stats =
                totalWorklistEnqueues tail.state.stats +
                  processed.queue.length := by
            simpa [tail] using induction (state := processed)
          unfold QueueInsertionBalanced at processedBalance
          have combined :
              (tail.linkAttempts + 1) +
                    tail.state.queue.length +
                  totalWorklistEnqueues state.stats =
                totalWorklistEnqueues tail.state.stats +
                  state.queue.length := by
            omega
          simpa [runUnificationWorklist, popEquation,
            processed, tail] using combined

/-- If a finite run still has queued work, every available unit of fuel was
consumed. Early termination is possible only through an empty queue. -/
private theorem runUnificationWorklist_attempts_eq_fuel_of_queue_ne_nil
    (certificate : Certificate) (consumers : Array (List Nat))
    (fuel : Nat) (state : UnificationWorklistState)
    (nonempty :
      (runUnificationWorklist certificate consumers fuel
        state).state.queue ≠ []) :
    (runUnificationWorklist certificate consumers fuel
      state).linkAttempts = fuel := by
  induction fuel generalizing state with
  | zero =>
      simp [runUnificationWorklist]
  | succ fuel induction =>
      cases popEquation : popWorklist? state with
      | none =>
          have queueEmpty : state.queue = [] := by
            cases queueEquation : state.queue with
            | nil =>
                rfl
            | cons head rest =>
                simp [popWorklist?, queueEquation] at popEquation
          simp [runUnificationWorklist, popEquation,
            queueEmpty] at nonempty
      | some result =>
          rcases result with ⟨index, popped⟩
          let processed :=
            processWorklistLink certificate consumers index popped
          have tailNonempty :
              (runUnificationWorklist certificate consumers fuel
                processed).state.queue ≠ [] := by
            simpa [runUnificationWorklist, popEquation,
              processed] using nonempty
          have tailExact :=
            induction (state := processed) tailNonempty
          simp [runUnificationWorklist, popEquation,
            processed, tailExact]

/-- From canonical initialization, attempted pops plus the residual queue are
exactly all successful queue insertions observed by the final state. -/
private theorem runUnificationWorklist_initialized_attemptAccounting
    (certificate : Certificate) (consumers : Array (List Nat))
    (fuel : Nat) (core : UnificationState) :
    let initial := initializeWorklist certificate core
    let result :=
      runUnificationWorklist certificate consumers fuel initial
    result.linkAttempts + result.state.queue.length =
      totalWorklistEnqueues result.state.stats := by
  let initial := initializeWorklist certificate core
  let result :=
    runUnificationWorklist certificate consumers fuel initial
  have balance :
      result.linkAttempts + result.state.queue.length +
            totalWorklistEnqueues initial.stats =
        totalWorklistEnqueues result.state.stats +
          initial.queue.length := by
    simpa [result, initial] using
      runUnificationWorklist_balance
        certificate consumers fuel initial
  have initialExact :
      totalWorklistEnqueues initial.stats =
        initial.queue.length := by
    simpa [initial] using
      initializeWorklist_totalEnqueues_eq_queueLength
        certificate core
  dsimp [result, initial] at balance initialExact ⊢
  omega

/-- Popping scheduler work changes no executable-core field. -/
private theorem popWorklist?_success_core
    {state popped : UnificationWorklistState} {index : Nat}
    (equation : popWorklist? state = some (index, popped)) :
    popped.core = state.core := by
  cases queueEquation : state.queue with
  | nil =>
      simp [popWorklist?, queueEquation] at equation
  | cons head rest =>
      simp [popWorklist?, queueEquation] at equation
      rcases equation with ⟨rfl, rfl⟩
      rfl

/-- Popping one queue entry changes no operational statistics. -/
private theorem popWorklist?_success_stats
    {state popped : UnificationWorklistState} {index : Nat}
    (equation : popWorklist? state = some (index, popped)) :
    popped.stats = state.stats := by
  cases queueEquation : state.queue with
  | nil =>
      simp [popWorklist?, queueEquation] at equation
  | cons head rest =>
      simp [popWorklist?, queueEquation] at equation
      rcases equation with ⟨rfl, rfl⟩
      rfl

/-- Popping one queue entry leaves the waiting registry unchanged. -/
private theorem popWorklist?_success_waiting
    {state popped : UnificationWorklistState} {index : Nat}
    (equation : popWorklist? state = some (index, popped)) :
    popped.waiting = state.waiting := by
  cases queueEquation : state.queue with
  | nil =>
      simp [popWorklist?, queueEquation] at equation
  | cons head rest =>
      simp [popWorklist?, queueEquation] at equation
      rcases equation with ⟨rfl, rfl⟩
      rfl

/-- Every finite scheduler run preserves the canonical-initialization enqueue
counter. -/
private theorem runUnificationWorklist_initialEnqueues
    (certificate : Certificate) (consumers : Array (List Nat))
    (fuel : Nat) (state : UnificationWorklistState) :
    (runUnificationWorklist certificate consumers fuel
      state).state.stats.initialEnqueues =
        state.stats.initialEnqueues := by
  induction fuel generalizing state with
  | zero =>
      simp [runUnificationWorklist]
  | succ fuel induction =>
      cases popEquation : popWorklist? state with
      | none =>
          simp [runUnificationWorklist, popEquation]
      | some result =>
          rcases result with ⟨index, popped⟩
          have poppedInitial :
              popped.stats.initialEnqueues =
                state.stats.initialEnqueues := by
            rw [popWorklist?_success_stats popEquation]
          have tail :=
            induction
              (state :=
                processWorklistLink certificate consumers index popped)
          simpa [runUnificationWorklist, popEquation,
            poppedInitial] using tail

/-- Popping one queue entry does not record a connective firing. -/
private theorem popWorklist?_success_successfulFirings
    {state popped : UnificationWorklistState} {index : Nat}
    (equation : popWorklist? state = some (index, popped)) :
    popped.stats.successfulFirings =
      state.stats.successfulFirings := by
  cases queueEquation : state.queue with
  | nil =>
      simp [popWorklist?, queueEquation] at equation
  | cons head rest =>
      simp [popWorklist?, queueEquation] at equation
      rcases equation with ⟨rfl, rfl⟩
      rfl

/-- Every finite scheduler run preserves an exact history of distinct
submitted connective firings. -/
private theorem runUnificationWorklist_firingsAccounted
    (certificate : Certificate) (consumers : Array (List Nat))
    (structural : certificate.StructurallyWellFormed)
    (fuel : Nat) (state : UnificationWorklistState)
    (coreInvariant : WorklistCoreInvariant certificate state)
    (accounted : WorklistFiringsAccounted certificate state) :
    WorklistFiringsAccounted certificate
      (runUnificationWorklist certificate consumers fuel state).state := by
  induction fuel generalizing state with
  | zero =>
      simpa [runUnificationWorklist] using accounted
  | succ fuel induction =>
      cases popEquation : popWorklist? state with
      | none =>
          simpa [runUnificationWorklist, popEquation] using accounted
      | some result =>
          rcases result with ⟨index, popped⟩
          have poppedCore :
              popped.core = state.core :=
            popWorklist?_success_core popEquation
          have poppedCounter :
              popped.stats.successfulFirings =
                state.stats.successfulFirings :=
            popWorklist?_success_successfulFirings popEquation
          have poppedAccounted :
              WorklistFiringsAccounted certificate popped :=
            accounted.transport poppedCore poppedCounter
          have poppedInvariant :
              WorklistCoreInvariant certificate popped := by
            unfold WorklistCoreInvariant at coreInvariant ⊢
            simpa [poppedCore] using coreInvariant
          have processedAccounted :
              WorklistFiringsAccounted certificate
                (processWorklistLink certificate consumers
                  index popped) :=
            processWorklistLink_firingsAccounted
              structural consumers index
                poppedInvariant.1 poppedAccounted
          have processedInvariant :
              WorklistCoreInvariant certificate
                (processWorklistLink certificate consumers
                  index popped) :=
            processWorklistLink_coreInvariant
              structural poppedInvariant
          simpa [runUnificationWorklist, popEquation] using
            induction
              (state :=
                processWorklistLink certificate consumers index popped)
              processedInvariant processedAccounted

/-- Every finite canonical-consumer scheduler run preserves cumulative
enqueue-source charges. The production invariant supplies the exact bounded
waiting registry needed by each tensor requeue. -/
private theorem runUnificationWorklist_enqueueSourcesBounded
    (certificate : Certificate)
    (structural : certificate.StructurallyWellFormed)
    (fuel : Nat) (state : UnificationWorklistState)
    (invariant : WorklistRunInvariant certificate state)
    (bounded : WorklistEnqueueSourcesBounded certificate state) :
    WorklistEnqueueSourcesBounded certificate
      (runUnificationWorklist certificate
        certificate.worklistConsumers fuel state).state := by
  induction fuel generalizing state with
  | zero =>
      simpa [runUnificationWorklist] using bounded
  | succ fuel induction =>
      cases popEquation : popWorklist? state with
      | none =>
          simpa [runUnificationWorklist, popEquation] using bounded
      | some result =>
          rcases result with ⟨index, popped⟩
          have poppedStats :
              popped.stats = state.stats :=
            popWorklist?_success_stats popEquation
          have poppedBounded :
              WorklistEnqueueSourcesBounded certificate popped := by
            unfold WorklistEnqueueSourcesBounded at bounded ⊢
            simpa [poppedStats] using bounded
          have poppedWaiting :
              popped.waiting.length = state.waiting.length := by
            rw [popWorklist?_success_waiting popEquation]
          have stateWaitingBound :
              state.waiting.length ≤ certificate.links.length :=
            invariant.registryLengthBounds.2
          have processedBounded :
              WorklistEnqueueSourcesBounded certificate
                (processWorklistLink certificate
                  certificate.worklistConsumers index popped) :=
            processWorklistLink_enqueueSourcesBounded
              structural index
                (by simpa [poppedWaiting] using stateWaitingBound)
                poppedBounded
          have processedInvariant :
              WorklistRunInvariant certificate
                (processWorklistLink certificate
                  certificate.worklistConsumers index popped) :=
            popProcessWorklist_runInvariant
              structural invariant popEquation
          simpa [runUnificationWorklist, popEquation] using
            induction
              (state :=
                processWorklistLink certificate
                  certificate.worklistConsumers index popped)
              processedInvariant processedBounded

/-- The complete executable-core invariant bundle survives every finite
worklist run, including early queue exhaustion and conservative fuel
exhaustion. -/
private theorem runUnificationWorklist_coreInvariant
    (certificate : Certificate) (consumers : Array (List Nat))
    (structural : certificate.StructurallyWellFormed)
    (fuel : Nat) (state : UnificationWorklistState)
    (invariant : WorklistCoreInvariant certificate state) :
    WorklistCoreInvariant certificate
      (runUnificationWorklist certificate consumers fuel state).state := by
  induction fuel generalizing state with
  | zero =>
      simpa [runUnificationWorklist] using invariant
  | succ fuel induction =>
      cases popEquation : popWorklist? state with
      | none =>
          simpa [runUnificationWorklist, popEquation] using invariant
      | some result =>
          rcases result with ⟨index, popped⟩
          have poppedCore :
              popped.core = state.core :=
            popWorklist?_success_core popEquation
          have poppedInvariant :
              WorklistCoreInvariant certificate popped := by
            unfold WorklistCoreInvariant at invariant ⊢
            simpa [poppedCore] using invariant
          have processedInvariant :
              WorklistCoreInvariant certificate
                (processWorklistLink certificate consumers
                  index popped) :=
            processWorklistLink_coreInvariant
              structural poppedInvariant
          simpa [runUnificationWorklist, popEquation] using
            induction
              (state :=
                processWorklistLink certificate consumers index popped)
              processedInvariant

/-- Every finite scheduler run preserves semantic thread connectivity in the
active all-left reference subgraph. -/
private theorem runUnificationWorklist_threadConnected
    (certificate : Certificate) (consumers : Array (List Nat))
    (structural : certificate.StructurallyWellFormed)
    (fuel : Nat) (state : UnificationWorklistState)
    (invariant : WorklistCoreInvariant certificate state)
    (connected :
      UnificationMarking.ThreadConnected
        (state.core.toMarking certificate invariant.1)) :
    UnificationMarking.ThreadConnected
      ((runUnificationWorklist certificate consumers fuel state).state.core
        |>.toMarking certificate
          (runUnificationWorklist_coreInvariant certificate consumers
            structural fuel state invariant).1) := by
  induction fuel generalizing state with
  | zero =>
      exact UnificationState.threadConnected_of_eq
        invariant.1 _ (by simp [runUnificationWorklist]) connected
  | succ fuel induction =>
      cases popEquation : popWorklist? state with
      | none =>
          exact UnificationState.threadConnected_of_eq
            invariant.1 _ (by simp [runUnificationWorklist, popEquation])
            connected
      | some result =>
          rcases result with ⟨index, popped⟩
          have poppedCore : popped.core = state.core :=
            popWorklist?_success_core popEquation
          have poppedInvariant :
              WorklistCoreInvariant certificate popped := by
            unfold WorklistCoreInvariant at invariant ⊢
            simpa [poppedCore] using invariant
          have poppedConnected :
              UnificationMarking.ThreadConnected
                (popped.core.toMarking certificate poppedInvariant.1) :=
            UnificationState.threadConnected_of_eq
              invariant.1 poppedInvariant.1 poppedCore.symm connected
          have processedInvariant :
              WorklistCoreInvariant certificate
                (processWorklistLink certificate consumers
                  index popped) :=
            processWorklistLink_coreInvariant
              structural poppedInvariant
          have processedConnected :
              UnificationMarking.ThreadConnected
                ((processWorklistLink certificate consumers
                    index popped).core.toMarking
                  certificate processedInvariant.1) := by
            have preserved :
                UnificationMarking.ThreadConnected
                  ((processWorklistLink certificate consumers
                      index popped).core.toMarking certificate
                    (processWorklistLink_core_abstractable
                      poppedInvariant.1 poppedInvariant.2.1)) :=
              processWorklistLink_threadConnected
                (consumers := consumers) (index := index)
                poppedInvariant.1 poppedInvariant.2.1 poppedConnected
            unfold UnificationMarking.ThreadConnected
            intro firstVertex secondVertex firstToken secondToken
              firstMarked secondMarked synchronized
            exact
              (UnificationState.threadConnected_of_eq
                _ processedInvariant.1 rfl preserved)
                firstMarked secondMarked synchronized
          have tailConnected :
              UnificationMarking.ThreadConnected
                ((runUnificationWorklist certificate consumers fuel
                    (processWorklistLink certificate consumers
                      index popped)).state.core.toMarking certificate
                    (runUnificationWorklist_coreInvariant
                      certificate consumers structural fuel
                      (processWorklistLink certificate consumers
                        index popped) processedInvariant).1) :=
            induction
              (state :=
                processWorklistLink certificate consumers index popped)
              processedInvariant processedConnected
          have runStateEquation :
              (runUnificationWorklist certificate consumers
                (fuel + 1) state).state =
                (runUnificationWorklist certificate consumers fuel
                  (processWorklistLink certificate consumers
                    index popped)).state := by
            simp [runUnificationWorklist, popEquation]
          have transported :
              UnificationMarking.ThreadConnected
                ((runUnificationWorklist certificate consumers
                    (fuel + 1) state).state.core.toMarking certificate
                  (runUnificationWorklist_coreInvariant
                    certificate consumers structural (fuel + 1)
                    state invariant).1) :=
            UnificationState.threadConnected_of_eq
              (runUnificationWorklist_coreInvariant
                certificate consumers structural fuel
                (processWorklistLink certificate consumers
                  index popped) processedInvariant).1
              _
              (congrArg UnificationWorklistState.core
                runStateEquation.symm)
              tailConnected
          unfold UnificationMarking.ThreadConnected
          intro firstVertex secondVertex firstToken secondToken
            firstMarked secondMarked synchronized
          exact transported firstMarked secondMarked synchronized

/-- Every finite scheduler run preserves causal closure and exact threading
of the active all-left reference graph. -/
private theorem runUnificationWorklist_causallyThreaded
    (certificate : Certificate) (consumers : Array (List Nat))
    (structural : certificate.StructurallyWellFormed)
    (fuel : Nat) (state : UnificationWorklistState)
    (invariant : WorklistCoreInvariant certificate state)
    (coherent :
      UnificationMarking.CausallyThreaded
        (state.core.toMarking certificate invariant.1)) :
    UnificationMarking.CausallyThreaded
      ((runUnificationWorklist certificate consumers fuel state).state.core
        |>.toMarking certificate
          (runUnificationWorklist_coreInvariant certificate consumers
            structural fuel state invariant).1) := by
  induction fuel generalizing state with
  | zero =>
      exact UnificationState.causallyThreaded_of_eq
        invariant.1 _ (by simp [runUnificationWorklist]) coherent
  | succ fuel induction =>
      cases popEquation : popWorklist? state with
      | none =>
          exact UnificationState.causallyThreaded_of_eq
            invariant.1 _ (by simp [runUnificationWorklist, popEquation])
            coherent
      | some result =>
          rcases result with ⟨index, popped⟩
          have poppedCore : popped.core = state.core :=
            popWorklist?_success_core popEquation
          have poppedInvariant :
              WorklistCoreInvariant certificate popped := by
            unfold WorklistCoreInvariant at invariant ⊢
            simpa [poppedCore] using invariant
          have poppedCoherent :
              UnificationMarking.CausallyThreaded
                (popped.core.toMarking certificate poppedInvariant.1) :=
            UnificationState.causallyThreaded_of_eq
              invariant.1 poppedInvariant.1 poppedCore.symm coherent
          have processedInvariant :
              WorklistCoreInvariant certificate
                (processWorklistLink certificate consumers
                  index popped) :=
            processWorklistLink_coreInvariant
              structural poppedInvariant
          have processedCoherent :
              UnificationMarking.CausallyThreaded
                ((processWorklistLink certificate consumers
                    index popped).core.toMarking
                  certificate processedInvariant.1) := by
            have preserved :=
              processWorklistLink_causallyThreaded
                (consumers := consumers) (index := index)
                structural poppedInvariant.1 poppedInvariant.2.1
                poppedCoherent
            exact UnificationState.causallyThreaded_of_eq
              _ processedInvariant.1 rfl preserved
          have tailCoherent :
              UnificationMarking.CausallyThreaded
                ((runUnificationWorklist certificate consumers fuel
                    (processWorklistLink certificate consumers
                      index popped)).state.core.toMarking certificate
                    (runUnificationWorklist_coreInvariant
                      certificate consumers structural fuel
                      (processWorklistLink certificate consumers
                        index popped) processedInvariant).1) :=
            induction
              (state :=
                processWorklistLink certificate consumers index popped)
              processedInvariant processedCoherent
          have runStateEquation :
              (runUnificationWorklist certificate consumers
                (fuel + 1) state).state =
                (runUnificationWorklist certificate consumers fuel
                  (processWorklistLink certificate consumers
                    index popped)).state := by
            simp [runUnificationWorklist, popEquation]
          exact UnificationState.causallyThreaded_of_eq
            (runUnificationWorklist_coreInvariant
              certificate consumers structural fuel
              (processWorklistLink certificate consumers
                index popped) processedInvariant).1
            _
            (congrArg UnificationWorklistState.core
              runStateEquation.symm)
            tailCoherent

/-- Every finite worklist run is monotone on raw formula assignments. -/
private theorem runUnificationWorklist_preserves_assigned
    (certificate : Certificate) (consumers : Array (List Nat))
    (structural : certificate.StructurallyWellFormed)
    (fuel : Nat) (state : UnificationWorklistState)
    (invariant : WorklistCoreInvariant certificate state)
    {vertex : Vertex}
    (marked : state.core.assignedToken? vertex ≠ none) :
    ((runUnificationWorklist certificate consumers fuel state).state.core
      |>.assignedToken? vertex) ≠ none := by
  induction fuel generalizing state with
  | zero =>
      simpa [runUnificationWorklist] using marked
  | succ fuel induction =>
      cases popEquation : popWorklist? state with
      | none =>
          simpa [runUnificationWorklist, popEquation] using marked
      | some result =>
          rcases result with ⟨index, popped⟩
          have poppedCore : popped.core = state.core :=
            popWorklist?_success_core popEquation
          have poppedMarked :
              popped.core.assignedToken? vertex ≠ none := by
            simpa [poppedCore] using marked
          have poppedInvariant :
              WorklistCoreInvariant certificate popped := by
            unfold WorklistCoreInvariant at invariant ⊢
            simpa [poppedCore] using invariant
          have processedMarked :
              ((processWorklistLink certificate consumers index popped).core
                  |>.assignedToken? vertex) ≠ none :=
            processWorklistLink_preserves_assigned
              structural poppedInvariant.1 poppedMarked
          have processedInvariant :
              WorklistCoreInvariant certificate
                (processWorklistLink certificate consumers
                  index popped) :=
            processWorklistLink_coreInvariant
              structural poppedInvariant
          simpa [runUnificationWorklist, popEquation] using
            induction
              (state :=
                processWorklistLink certificate consumers index popped)
              processedInvariant processedMarked

/-- The exact production scheduler preserves its complete invariant through
every finite fuel prefix, including early quiescence and conservative fuel
exhaustion. -/
private theorem runUnificationWorklist_runInvariant
    (certificate : Certificate)
    (structural : certificate.StructurallyWellFormed)
    (fuel : Nat) (state : UnificationWorklistState)
    (invariant : WorklistRunInvariant certificate state) :
    WorklistRunInvariant certificate
      (runUnificationWorklist certificate
        certificate.worklistConsumers fuel state).state := by
  induction fuel generalizing state with
  | zero =>
      simpa [runUnificationWorklist] using invariant
  | succ fuel induction =>
      cases popEquation : popWorklist? state with
      | none =>
          simpa [runUnificationWorklist, popEquation] using invariant
      | some result =>
          rcases result with ⟨index, popped⟩
          have processedInvariant :
              WorklistRunInvariant certificate
                (processWorklistLink certificate
                  certificate.worklistConsumers index popped) :=
            popProcessWorklist_runInvariant
              structural invariant popEquation
          simpa [runUnificationWorklist, popEquation] using
            induction
              (state :=
                processWorklistLink certificate
                  certificate.worklistConsumers index popped)
              processedInvariant

private def worklistFuel (linkCount : Nat) : Nat :=
  UnificationWorklistStats.attemptBudget linkCount

/-- The exact production worklist run, from successful canonical axiom
initialization through its conservative attempt budget, carries the complete
core invariant bundle. -/
private theorem canonicalWorklistRun_coreInvariant
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    WorklistCoreInvariant certificate
      (runUnificationWorklist certificate certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state := by
  apply runUnificationWorklist_coreInvariant
  · exact structural
  · exact
      startAxioms?_success_initializeWorklist_coreInvariant
        structural startEquation

/-- The complete canonical worklist run preserves semantic connectivity of
every union-find thread inside the active all-left reference subgraph. -/
private theorem canonicalWorklistRun_threadConnected
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    UnificationMarking.ThreadConnected
      (final.core.toMarking certificate
        (canonicalWorklistRun_coreInvariant
          structural startEquation).1) := by
  let initial := initializeWorklist certificate started
  let fuel := worklistFuel certificate.links.length
  have initialInvariant :
      WorklistCoreInvariant certificate initial := by
    simpa [initial] using
      startAxioms?_success_initializeWorklist_coreInvariant
        structural startEquation
  rcases startAxioms?_success_threadConnected startEquation with
    ⟨startedAbstractable, startedConnected⟩
  have initialConnected :
      UnificationMarking.ThreadConnected
        (initial.core.toMarking certificate initialInvariant.1) := by
    exact UnificationState.threadConnected_of_eq
      startedAbstractable initialInvariant.1
      (by simp [initial, initializeWorklist])
      startedConnected
  have finalConnected :
      UnificationMarking.ThreadConnected
        ((runUnificationWorklist certificate
            certificate.worklistConsumers fuel initial).state.core.toMarking
          certificate
          (runUnificationWorklist_coreInvariant
            certificate certificate.worklistConsumers structural
            fuel initial initialInvariant).1) :=
    runUnificationWorklist_threadConnected
      certificate certificate.worklistConsumers structural
      fuel initial initialInvariant initialConnected
  dsimp [initial, fuel]
  unfold UnificationMarking.ThreadConnected
  intro firstVertex secondVertex firstToken secondToken
    firstMarked secondMarked synchronized
  exact
    (UnificationState.threadConnected_of_eq
      _ _ rfl finalConnected)
      firstMarked secondMarked synchronized

/-- The complete canonical worklist run is causally closed and every active
retained reference edge lies inside one semantic union-find thread. -/
private theorem canonicalWorklistRun_causallyThreaded
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    UnificationMarking.CausallyThreaded
      (final.core.toMarking certificate
        (canonicalWorklistRun_coreInvariant
          structural startEquation).1) := by
  let initial := initializeWorklist certificate started
  let fuel := worklistFuel certificate.links.length
  have initialInvariant :
      WorklistCoreInvariant certificate initial := by
    simpa [initial] using
      startAxioms?_success_initializeWorklist_coreInvariant
        structural startEquation
  rcases startAxioms?_success_causallyThreaded
      structural startEquation with
    ⟨startedAbstractable, startedCoherent⟩
  have initialCoherent :
      UnificationMarking.CausallyThreaded
        (initial.core.toMarking certificate initialInvariant.1) :=
    UnificationState.causallyThreaded_of_eq
      startedAbstractable initialInvariant.1
      (by simp [initial, initializeWorklist])
      startedCoherent
  have finalCoherent :
      UnificationMarking.CausallyThreaded
        ((runUnificationWorklist certificate
            certificate.worklistConsumers fuel initial).state.core.toMarking
          certificate
          (runUnificationWorklist_coreInvariant
            certificate certificate.worklistConsumers structural
            fuel initial initialInvariant).1) :=
    runUnificationWorklist_causallyThreaded
      certificate certificate.worklistConsumers structural
      fuel initial initialInvariant initialCoherent
  dsimp [initial, fuel]
  exact UnificationState.causallyThreaded_of_eq
    _ _ rfl finalCoherent

/-- Canonical worklist states have exact agreement between union-find token
classes and connected components of the active reference graph. -/
private theorem canonicalWorklistRun_threadComponentsExact
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    UnificationMarking.ThreadComponentsExact
      (final.core.toMarking certificate
        (canonicalWorklistRun_coreInvariant
          structural startEquation).1) :=
  ⟨canonicalWorklistRun_threadConnected structural startEquation,
    (canonicalWorklistRun_causallyThreaded
      structural startEquation).2⟩

/-- In a declaratively correct proof net, two marked tensor premises cannot
already belong to one semantic thread while the tensor conclusion remains
unmarked.  The active thread path plus the two fixed tensor edges would form
a cycle in the deterministic all-left switching. -/
private theorem sameThread_tensorDeadlock_false
    {certificate : Certificate} {state : UnificationState}
    (correct : certificate.DeclarativelyCorrect)
    (abstractable : state.Abstractable certificate)
    (connected :
      UnificationMarking.ThreadConnected
        (state.toMarking certificate abstractable))
    {left right conclusion token : Nat}
    (membership :
      Link.tensor left right conclusion ∈ certificate.links)
    (conclusionUnmarked :
      state.assignedToken? conclusion = none)
    (leftLookup : state.tokenAt? left = some token)
    (rightLookup : state.tokenAt? right = some token) :
    False := by
  have wellFormed :
      certificate.LinkWellFormed
        (.tensor left right conclusion) :=
    correct.1.2.2.2.2.1 _ membership
  rcases state.tokenAt?_some_witness leftLookup with
    ⟨leftRaw, leftMarked, leftRepresentative⟩
  rcases state.tokenAt?_some_witness rightLookup with
    ⟨rightRaw, rightMarked, rightRepresentative⟩
  have sameThread :
      (state.toMarking certificate abstractable).sameThread
        leftRaw rightRaw := by
    simp only [UnificationState.toMarking_sameThread]
    exact leftRepresentative.trans rightRepresentative.symm
  have abstractLeftMarked :
      (state.toMarking certificate abstractable).mark left =
        some leftRaw := by
    simpa only [UnificationState.toMarking_mark] using leftMarked
  have abstractRightMarked :
      (state.toMarking certificate abstractable).mark right =
        some rightRaw := by
    simpa only [UnificationState.toMarking_mark] using rightMarked
  have activeWalk :
      (state.toMarking certificate abstractable).activeReferenceGraph.Walk
        left right :=
    connected abstractLeftMarked abstractRightMarked sameThread
  rcases activeWalk.toSimple with ⟨steps, visited, simple⟩
  rcases simple.liftToEdgeSimplePathWithEdges
      ((state.toMarking certificate abstractable)
        |>.activeReferenceEdges_subset_referenceSwitchingGraph) with
    ⟨threadPath, threadStarts, threadFinishes, _threadVertices,
      threadEdgesActive⟩
  have threadStartFinishDifferent :
      threadPath.start ≠ threadPath.finish := by
    rw [threadStarts, threadFinishes]
    exact wellFormed.1
  have threadNonempty : threadPath.traversed ≠ [] := by
    intro empty
    have finishMembership :=
      threadPath.walk.finish_mem_visitedVertices
    have sameEndpoints : threadPath.finish = threadPath.start := by
      simpa [Graph.EdgeWalk.visitedVertices, empty] using finishMembership
    exact threadStartFinishDifferent sameEndpoints.symm
  have abstractConclusionUnmarked :
      (state.toMarking certificate abstractable).mark conclusion = none := by
    simpa only [UnificationState.toMarking_mark] using conclusionUnmarked
  have noActiveIncident :
      ∀ edge,
        edge ∈
            (state.toMarking certificate abstractable).activeReferenceEdges →
          (edge.first = conclusion ∨ edge.second = conclusion) →
            False := by
    intro edge edgeActive incident
    have endpoints := (List.mem_filter.mp edgeActive).2
    simp only [Bool.and_eq_true] at endpoints
    rcases incident with firstConclusion | secondConclusion
    · have markedConclusion :
          Option.isSome
            ((state.toMarking certificate abstractable).mark conclusion) =
              true := by
        simpa [firstConclusion] using endpoints.1
      rw [abstractConclusionUnmarked] at markedConclusion
      simp at markedConclusion
    · have markedConclusion :
          Option.isSome
            ((state.toMarking certificate abstractable).mark conclusion) =
              true := by
        simpa [secondConclusion] using endpoints.2
      rw [abstractConclusionUnmarked] at markedConclusion
      simp at markedConclusion
  have conclusionNotInThreadPath :
      conclusion ∉ threadPath.vertices := by
    intro conclusionMembership
    change conclusion ∈
      Graph.EdgeWalk.visitedVertices threadPath.start
        threadPath.traversed at conclusionMembership
    simp only [Graph.EdgeWalk.visitedVertices, List.mem_cons] at conclusionMembership
    rcases conclusionMembership with startConclusion | targetMembership
    · apply wellFormed.2.1
      rw [← threadStarts]
      exact startConclusion.symm
    · rcases List.mem_map.mp targetMembership with
        ⟨directed, directedMembership, targetConclusion⟩
      have edgeActive := threadEdgesActive directed directedMembership
      apply noActiveIncident directed.edge edgeActive
      cases forward : directed.forward with
      | false =>
          exact Or.inl (by
            simpa [Graph.DirectedEdge.target, forward] using
              targetConclusion)
      | true =>
          exact Or.inr (by
            simpa [Graph.DirectedEdge.target, forward] using
              targetConclusion)
  have referenceTensorEdges :=
    UnificationMarking.referenceSwitchingGraph_tensorEdges
      certificate membership
  let leftEdge : Edge := { first := left, second := conclusion }
  let rightEdge : Edge := { first := right, second := conclusion }
  have leftEdgeMembership :
      leftEdge ∈ certificate.referenceSwitchingGraph.edges := by
    simpa [leftEdge] using referenceTensorEdges.1
  have rightEdgeMembership :
      rightEdge ∈ certificate.referenceSwitchingGraph.edges := by
    simpa [rightEdge] using referenceTensorEdges.2
  rcases List.getElem?_of_mem leftEdgeMembership with
    ⟨leftIndex, leftEdgeLookup⟩
  rcases List.getElem?_of_mem rightEdgeMembership with
    ⟨rightIndex, rightEdgeLookup⟩
  let rightDirected :
      certificate.referenceSwitchingGraph.DirectedEdge := {
    index := rightIndex
    edge := rightEdge
    lookup := rightEdgeLookup
    forward := true }
  let leftDirected :
      certificate.referenceSwitchingGraph.DirectedEdge := {
    index := leftIndex
    edge := leftEdge
    lookup := leftEdgeLookup
    forward := false }
  have tensorIndicesDifferent : rightIndex ≠ leftIndex := by
    intro sameIndex
    have sameEdges : rightEdge = leftEdge := by
      apply Option.some.inj
      rw [← rightEdgeLookup, ← leftEdgeLookup, sameIndex]
    apply wellFormed.1
    have sameFirst := congrArg Edge.first sameEdges
    simpa [rightEdge, leftEdge] using sameFirst.symm
  let returnPath : certificate.referenceSwitchingGraph.EdgeSimplePath := {
    start := right
    finish := left
    traversed := [rightDirected, leftDirected]
    walk := by
      simpa [rightDirected, leftDirected, rightEdge, leftEdge,
        Graph.DirectedEdge.source, Graph.DirectedEdge.target] using
        Graph.EdgeWalk.step
          (Graph.EdgeWalk.step
            (Graph.EdgeWalk.refl
              (graph := certificate.referenceSwitchingGraph) right)
            rightDirected rfl rfl)
          leftDirected rfl rfl
    verticesNodup := by
      simp [Graph.EdgeWalk.visitedVertices, rightDirected, leftDirected,
        rightEdge, leftEdge, Graph.DirectedEdge.target,
        wellFormed.2.2.1]
      exact
        ⟨fun same => wellFormed.1 same.symm,
          fun same => wellFormed.2.1 same.symm⟩ }
  have returnNonempty : returnPath.traversed ≠ [] := by
    simp [returnPath]
  have meeting : threadPath.finish = returnPath.start := by
    simpa [returnPath] using threadFinishes
  have closing : returnPath.finish = threadPath.start := by
    simpa [returnPath] using threadStarts.symm
  have vertexDisjoint :
      ∀ vertex,
        vertex ∈ threadPath.vertices →
          vertex ∈ returnPath.vertices.tail.dropLast →
            False := by
    intro vertex threadMembership returnMembership
    have vertexConclusion : vertex = conclusion := by
      simpa [returnPath, Graph.EdgeSimplePath.vertices,
        Graph.EdgeWalk.visitedVertices, rightDirected, leftDirected,
        rightEdge, leftEdge, Graph.DirectedEdge.target] using
          returnMembership
    subst vertex
    exact conclusionNotInThreadPath threadMembership
  have leftEdgeNotActive :
      leftEdge ∉
        (state.toMarking certificate abstractable).activeReferenceEdges := by
    intro active
    exact noActiveIncident leftEdge active (by
      exact Or.inr rfl)
  have rightEdgeNotActive :
      rightEdge ∉
        (state.toMarking certificate abstractable).activeReferenceEdges := by
    intro active
    exact noActiveIncident rightEdge active (by
      exact Or.inr rfl)
  have edgeDisjoint :
      ∀ index,
        index ∈ threadPath.traversed.map Graph.DirectedEdge.index →
          index ∈ returnPath.traversed.map Graph.DirectedEdge.index →
            False := by
    intro index threadIndex returnIndex
    rcases List.mem_map.mp threadIndex with
      ⟨directed, directedMembership, directedIndex⟩
    have edgeActive := threadEdgesActive directed directedMembership
    change directed.edge ∈
      (state.toMarking certificate abstractable).activeReferenceEdges
        at edgeActive
    have returnCases : index = rightIndex ∨ index = leftIndex := by
      simpa [returnPath, rightDirected, leftDirected] using returnIndex
    rcases returnCases with rightCase | leftCase
    · have sameIndex : directed.index = rightIndex :=
        directedIndex.trans rightCase
      have sameEdge : directed.edge = rightEdge := by
        apply Option.some.inj
        rw [← directed.lookup, ← rightEdgeLookup, sameIndex]
      rw [sameEdge] at edgeActive
      exact rightEdgeNotActive edgeActive
    · have sameIndex : directed.index = leftIndex :=
        directedIndex.trans leftCase
      have sameEdge : directed.edge = leftEdge := by
        apply Option.some.inj
        rw [← directed.lookup, ← leftEdgeLookup, sameIndex]
      rw [sameEdge] at edgeActive
      exact leftEdgeNotActive edgeActive
  let cycle : certificate.referenceSwitchingGraph.EdgeSimpleCycle :=
    Graph.EdgeSimpleCycle.ofTwoPaths
      threadPath returnPath threadNonempty returnNonempty
      meeting closing vertexDisjoint edgeDisjoint
  have compact :=
    certificate.declarativelyCorrect_iff_structural_cuspAcyclic_referenceConnected
      |>.mp correct
  have referenceAcyclic :
      certificate.referenceSwitchingGraph.Acyclic := by
    simpa [Certificate.referenceSwitchingGraph] using
      compact.2.1.occurrenceSwitching_acyclic
        compact.1 certificate.referenceFullSwitchingSelection
  exact referenceAcyclic cycle

/-- Every submitted axiom endpoint remains assigned throughout the canonical
fuel-bounded worklist run. -/
private theorem canonicalWorklistRun_axiom_endpoints_assigned
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started)
    {left right : Vertex}
    (membership : Link.axiom left right ∈ certificate.links) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    final.core.assignedToken? left ≠ none ∧
      final.core.assignedToken? right ≠ none := by
  let initial := initializeWorklist certificate started
  let fuel := worklistFuel certificate.links.length
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers fuel initial).state
  have startedEndpoints :
      started.assignedToken? left ≠ none ∧
        started.assignedToken? right ≠ none :=
    certificate.startAxioms?_success_axiom_endpoints_assigned
      membership startEquation
  have initialInvariant :
      WorklistCoreInvariant certificate initial := by
    simpa [initial] using
      startAxioms?_success_initializeWorklist_coreInvariant
        structural startEquation
  have leftPreserved :
      final.core.assignedToken? left ≠ none := by
    simpa [final, fuel, initial] using
      runUnificationWorklist_preserves_assigned
        certificate certificate.worklistConsumers structural
        fuel initial initialInvariant startedEndpoints.1
  have rightPreserved :
      final.core.assignedToken? right ≠ none := by
    simpa [final, fuel, initial] using
      runUnificationWorklist_preserves_assigned
        certificate certificate.worklistConsumers structural
        fuel initial initialInvariant startedEndpoints.2
  exact ⟨leftPreserved, rightPreserved⟩

/-- The exact finite production run retains full scheduler coverage and exact
queue/waiting provenance together with all executable-core invariants. -/
private theorem canonicalWorklistRun_runInvariant
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    WorklistRunInvariant certificate
      (runUnificationWorklist certificate certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state := by
  apply runUnificationWorklist_runInvariant
  · exact structural
  · exact
      startAxioms?_success_initializeWorklist_runInvariant
        structural startEquation

/-- The canonical finite production run carries an exact history of distinct
submitted connective firings. -/
private theorem canonicalWorklistRun_firingsAccounted
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    WorklistFiringsAccounted certificate
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state := by
  apply runUnificationWorklist_firingsAccounted
  · exact structural
  · exact
      startAxioms?_success_initializeWorklist_coreInvariant
        structural startEquation
  · exact initializeWorklist_firingsAccounted certificate started

/-- No canonical finite production run can successfully fire more
connectives than the submitted link carrier contains. -/
private theorem canonicalWorklistRun_successfulFirings_le
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    final.stats.successfulFirings ≤ certificate.links.length := by
  exact
    (canonicalWorklistRun_firingsAccounted
      structural startEquation).successfulFirings_le

/-- The canonical finite production run preserves the per-firing cumulative
source charges from its zero-charged initialization. -/
private theorem canonicalWorklistRun_enqueueSourcesBounded
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    WorklistEnqueueSourcesBounded certificate
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state := by
  apply runUnificationWorklist_enqueueSourcesBounded
  · exact structural
  · exact
      startAxioms?_success_initializeWorklist_runInvariant
        structural startEquation
  · exact initializeWorklist_enqueueSourcesBounded certificate started

/-- The initialization-source counter of the canonical production run is
bounded by the submitted link carrier. -/
private theorem canonicalWorklistRun_initialEnqueues_le
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    final.stats.initialEnqueues ≤ certificate.links.length := by
  let initial := initializeWorklist certificate started
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length) initial).state
  have preserved :
      final.stats.initialEnqueues =
        initial.stats.initialEnqueues := by
    simpa [final] using
      runUnificationWorklist_initialEnqueues
        certificate certificate.worklistConsumers
          (worklistFuel certificate.links.length) initial
  have initialQueueBound :
      initial.queue.length ≤ certificate.links.length := by
    exact
      (startAxioms?_success_initializeWorklist_runInvariant
        structural startEquation).registryLengthBounds.1
  have initialExact :
      initial.stats.initialEnqueues =
        initial.queue.length := by
    rfl
  dsimp [final]
  calc
    (runUnificationWorklist certificate certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        initial).state.stats.initialEnqueues =
        initial.stats.initialEnqueues := preserved
    _ = initial.queue.length := initialExact
    _ ≤ certificate.links.length := initialQueueBound

/-- All successful queue insertions of the canonical production run fit within
the executable attempt budget. -/
private theorem canonicalWorklistRun_totalEnqueues_le_fuel
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    totalWorklistEnqueues final.stats ≤
      worklistFuel certificate.links.length := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  have firingBound :
      final.stats.successfulFirings ≤ certificate.links.length := by
    simpa [final] using
      canonicalWorklistRun_successfulFirings_le
        structural startEquation
  have sources :
      WorklistEnqueueSourcesBounded certificate final := by
    simpa [final] using
      canonicalWorklistRun_enqueueSourcesBounded
        structural startEquation
  have initialBound :
      final.stats.initialEnqueues ≤ certificate.links.length := by
    simpa [final] using
      canonicalWorklistRun_initialEnqueues_le
        structural startEquation
  have dependencyBound :
      final.stats.dependencyEnqueues ≤ certificate.links.length :=
    Nat.le_trans sources.1 firingBound
  have waitingBound :
      final.stats.waitingRequeues ≤
        certificate.links.length * certificate.links.length :=
    Nat.le_trans sources.2
      (Nat.mul_le_mul_left certificate.links.length firingBound)
  have totalBound :
      totalWorklistEnqueues final.stats ≤
        worklistFuel certificate.links.length := by
    unfold totalWorklistEnqueues worklistFuel
      UnificationWorklistStats.attemptBudget
    rw [Nat.mul_add]
    omega
  simpa [final] using totalBound

/-- The conservative production fuel is sufficient: every structurally
well-formed, successfully initialized canonical run exhausts its concrete
work queue before or exactly at the executable budget. -/
private theorem canonicalWorklistRun_queue_eq_nil
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state.queue = [] := by
  let fuel := worklistFuel certificate.links.length
  let initial := initializeWorklist certificate started
  let result :=
    runUnificationWorklist certificate
      certificate.worklistConsumers fuel initial
  change result.state.queue = []
  apply Classical.byContradiction
  intro nonempty
  have attemptsExact :
      result.linkAttempts = fuel := by
    exact
      runUnificationWorklist_attempts_eq_fuel_of_queue_ne_nil
        certificate certificate.worklistConsumers fuel initial
        (by simpa [result] using nonempty)
  have queuePositive :
      0 < result.state.queue.length := by
    cases queueEquation : result.state.queue with
    | nil =>
        exact False.elim (nonempty queueEquation)
    | cons head tail =>
        simp
  have accounting :
      result.linkAttempts + result.state.queue.length =
        totalWorklistEnqueues result.state.stats := by
    simpa [result, initial] using
      runUnificationWorklist_initialized_attemptAccounting
        certificate certificate.worklistConsumers fuel started
  have totalBound :
      totalWorklistEnqueues result.state.stats ≤ fuel := by
    simpa [result, fuel, initial] using
      canonicalWorklistRun_totalEnqueues_le_fuel
        structural startEquation
  omega

/-- If the canonical run leaves any formula occurrence unassigned, then the
certificate contains a concrete submitted connective whose conclusion is
still unfired.  Atomic occurrences cannot witness incompleteness because all
submitted axiom endpoints are initialized and assignment is monotone. -/
private theorem canonicalWorklistRun_incomplete_has_unfired_connective
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    final.core.allMarked = false →
      ∃ (index : Nat) (link : Link),
        certificate.links[index]? = some link ∧
          link.isConnective = true ∧
            ¬linkFiredIn final.core link := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  change
    final.core.allMarked = false →
      ∃ (index : Nat) (link : Link),
        certificate.links[index]? = some link ∧
          link.isConnective = true ∧
            ¬linkFiredIn final.core link
  intro incomplete
  have marksIncomplete :
      final.core.marks.all Option.isSome = false := by
    simpa [UnificationState.allMarked] using incomplete
  rcases Array.all_eq_false.mp marksIncomplete with
    ⟨vertex, markBound, unassignedElement⟩
  have rawNone : final.core.marks[vertex] = none := by
    cases rawLookup : final.core.marks[vertex] with
    | none =>
        rfl
    | some token =>
        simp [rawLookup] at unassignedElement
  have assignedNone :
      final.core.assignedToken? vertex = none := by
    unfold UnificationState.assignedToken?
    rw [Array.getElem?_eq_getElem markBound, rawNone]
    rfl
  have coreInvariant :
      WorklistCoreInvariant certificate final := by
    simpa [final] using
      canonicalWorklistRun_coreInvariant structural startEquation
  have formulaBound : vertex < certificate.formulas.size := by
    simpa [coreInvariant.1.markArraySize] using markBound
  rcases structurallyWellFormed_sourceLink_exists
      structural formulaBound with
    ⟨formula, link, index, _formulaLookup, linkLookup, source⟩
  have linkMembership : link ∈ certificate.links :=
    List.mem_of_getElem? linkLookup
  cases formula with
  | atom name positive =>
      cases link with
      | «axiom» left right =>
          have endpoints :
              final.core.assignedToken? left ≠ none ∧
                final.core.assignedToken? right ≠ none := by
            simpa [final] using
              canonicalWorklistRun_axiom_endpoints_assigned
                structural startEquation linkMembership
          simp [Link.containsAxiomEndpoint] at source
          rcases source with leftSource | rightSource
          · apply False.elim
            apply endpoints.1
            simpa [leftSource] using assignedNone
          · apply False.elim
            apply endpoints.2
            simpa [rightSource] using assignedNone
      | tensor left right conclusion =>
          simp [Link.containsAxiomEndpoint] at source
      | «par» left right conclusion =>
          simp [Link.containsAxiomEndpoint] at source
  | tensor formulaLeft formulaRight =>
      cases link with
      | «axiom» left right =>
          simp [Link.produces] at source
      | tensor left right conclusion =>
          simp [Link.produces] at source
          subst conclusion
          exact
            ⟨index, .tensor left right vertex, linkLookup, rfl,
              fun fired => fired assignedNone⟩
      | «par» left right conclusion =>
          simp [Link.produces] at source
          subst conclusion
          exact
            ⟨index, .par left right vertex, linkLookup, rfl,
              fun fired => fired assignedNone⟩
  | par formulaLeft formulaRight =>
      cases link with
      | «axiom» left right =>
          simp [Link.produces] at source
      | tensor left right conclusion =>
          simp [Link.produces] at source
          subst conclusion
          exact
            ⟨index, .tensor left right vertex, linkLookup, rfl,
              fun fired => fired assignedNone⟩
      | «par» left right conclusion =>
          simp [Link.produces] at source
          subst conclusion
          exact
            ⟨index, .par left right vertex, linkLookup, rfl,
              fun fired => fired assignedNone⟩

/-- The canonical fuel-sufficient run reaches a genuinely quiescent state.
Consequently every submitted connective that is still unfired exposes one of
the exact semantic obstruction witnesses, rather than hidden queued work or a
fuel artifact. -/
private theorem canonicalWorklistRun_unfired_obstruction
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    ∀ {index : Nat} {link : Link},
      certificate.links[index]? = some link →
        link.isConnective = true →
          ¬linkFiredIn final.core link →
            QuiescentConnectiveObstruction final index link := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  have invariant : WorklistRunInvariant certificate final := by
    simpa [final] using
      canonicalWorklistRun_runInvariant structural startEquation
  have quiescent : final.queue = [] := by
    simpa [final] using
      canonicalWorklistRun_queue_eq_nil structural startEquation
  change
    ∀ {index : Nat} {link : Link},
      certificate.links[index]? = some link →
        link.isConnective = true →
          ¬linkFiredIn final.core link →
            QuiescentConnectiveObstruction final index link
  intro index link lookup connective unfired
  exact
    SchedulerCoverage.quiescent_unfired_obstruction invariant.2.1
      quiescent lookup connective unfired

/-- Canonical incomplete marking is never an opaque scheduler failure: it
identifies an exact submitted connective together with one of the final
idle/waiting/deadlock obstruction witnesses. -/
private theorem canonicalWorklistRun_incomplete_obstruction
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    final.core.allMarked = false →
      ∃ (index : Nat) (link : Link),
        certificate.links[index]? = some link ∧
          link.isConnective = true ∧
            QuiescentConnectiveObstruction final index link := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  change
    final.core.allMarked = false →
      ∃ (index : Nat) (link : Link),
        certificate.links[index]? = some link ∧
          link.isConnective = true ∧
            QuiescentConnectiveObstruction final index link
  intro incomplete
  rcases
      canonicalWorklistRun_incomplete_has_unfired_connective
        structural startEquation incomplete with
    ⟨index, link, lookup, connective, unfired⟩
  exact
    ⟨index, link, lookup, connective,
      canonicalWorklistRun_unfired_obstruction
        structural startEquation lookup connective unfired⟩

/-- A concrete distinct-thread par that remains registered at quiescence,
indexed by its unassigned conclusion occurrence. -/
private def QuiescentWaitingParAt
    (certificate : Certificate)
    (state : UnificationWorklistState)
    (conclusion : Vertex) : Prop :=
  state.core.assignedToken? conclusion = none ∧
    ∃ (index left right leftToken rightToken : Nat),
      certificate.links[index]? =
          some (.par left right conclusion) ∧
        state.core.tokenAt? left = some leftToken ∧
          state.core.tokenAt? right = some rightToken ∧
            leftToken ≠ rightToken ∧
              index ∈ state.waiting

/-- The well-founded local alternative for an arbitrary unassigned formula:
strict descent to an unassigned premise or arrival at a registered waiting
par. -/
private def UnassignedFormulaDescentOrWaitingPar
    (certificate : Certificate)
    (state : UnificationWorklistState)
    (vertex : Vertex) : Prop :=
  (∃ blockedPremise : Vertex,
      blockedPremise < certificate.formulas.size ∧
        state.core.assignedToken? blockedPremise = none ∧
          certificate.formulaComplexityAt blockedPremise <
            certificate.formulaComplexityAt vertex) ∨
    QuiescentWaitingParAt certificate state vertex

/-- In a correct quiescent canonical run, every unassigned occurrence admits
the global chase step required by the progress proof. Atomic sources are
already initialized, tensor deadlocks are excluded by reference acyclicity,
and every remaining idle connective descends strictly through formula
complexity. -/
private theorem canonicalWorklistRun_unassigned_descends_or_waitingPar
    {certificate : Certificate} {started : UnificationState}
    (correct : certificate.DeclarativelyCorrect)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    ∀ {vertex : Vertex},
      vertex < certificate.formulas.size →
        final.core.assignedToken? vertex = none →
          UnassignedFormulaDescentOrWaitingPar
            certificate final vertex := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  change
    ∀ {vertex : Vertex},
      vertex < certificate.formulas.size →
        final.core.assignedToken? vertex = none →
          UnassignedFormulaDescentOrWaitingPar
            certificate final vertex
  have coreInvariant :
      WorklistCoreInvariant certificate final := by
    simpa [final] using
      canonicalWorklistRun_coreInvariant correct.1 startEquation
  have connected :
      UnificationMarking.ThreadConnected
        (final.core.toMarking certificate coreInvariant.1) := by
    unfold UnificationMarking.ThreadConnected
    intro firstVertex secondVertex firstToken secondToken
      firstMarked secondMarked synchronized
    dsimp [final] at firstMarked secondMarked synchronized ⊢
    exact
      (canonicalWorklistRun_threadConnected correct.1 startEquation)
        firstMarked secondMarked synchronized
  have assignedNoneOfTokenNone :
      ∀ {candidate : Vertex},
        final.core.tokenAt? candidate = none →
          final.core.assignedToken? candidate = none := by
    intro candidate tokenNone
    cases assigned :
        final.core.assignedToken? candidate with
    | none =>
        rfl
    | some rawToken =>
        have assignedNotNone :
            final.core.assignedToken? candidate ≠ none := by
          simp [assigned]
        rcases final.core.tokenAt?_exists_of_assigned assignedNotNone with
          ⟨token, yielded⟩
        rw [tokenNone] at yielded
        contradiction
  intro vertex vertexBound vertexUnassigned
  rcases structurallyWellFormed_sourceLink_exists
      correct.1 vertexBound with
    ⟨formula, link, index, _formulaLookup, linkLookup, source⟩
  have linkMembership : link ∈ certificate.links :=
    List.mem_of_getElem? linkLookup
  have compoundCase :
      link.produces vertex = true →
        UnassignedFormulaDescentOrWaitingPar
          certificate final vertex := by
    intro produces
    have connective : link.isConnective = true := by
      cases link with
      | «axiom» left right =>
          simp [Link.produces] at produces
      | «par» left right conclusion =>
          rfl
      | tensor left right conclusion =>
          rfl
    have unfired : ¬linkFiredIn final.core link := by
      cases link with
      | «axiom» left right =>
          simp [linkFiredIn]
      | «par» left right conclusion =>
          simp [Link.produces] at produces
          subst conclusion
          simpa [linkFiredIn] using vertexUnassigned
      | tensor left right conclusion =>
          simp [Link.produces] at produces
          subst conclusion
          simpa [linkFiredIn] using vertexUnassigned
    have obstruction :=
      canonicalWorklistRun_unfired_obstruction
        correct.1 startEquation linkLookup connective unfired
    cases link with
    | «axiom» left right =>
        simp [Link.produces] at produces
    | «par» left right conclusion =>
        simp [Link.produces] at produces
        subst conclusion
        have wellFormed :
            certificate.LinkWellFormed
              (.par left right vertex) :=
          correct.1.2.2.2.2.1 _ linkMembership
        have leftRank :
            certificate.formulaComplexityAt left <
              certificate.formulaComplexityAt vertex := by
          simpa [Certificate.linkConclusionComplexity] using
            wellFormed.premise_complexity_lt_conclusion
              (premise := left) (by simp [Link.premises])
        have rightRank :
            certificate.formulaComplexityAt right <
              certificate.formulaComplexityAt vertex := by
          simpa [Certificate.linkConclusionComplexity] using
            wellFormed.premise_complexity_lt_conclusion
              (premise := right) (by simp [Link.premises])
        rcases obstruction with
          ⟨conclusionUnassigned, idle | waiting⟩
        · rcases idle with leftIdle | rightIdle
          · exact .inl
              ⟨left, wellFormed.2.2.2.1,
                assignedNoneOfTokenNone leftIdle, leftRank⟩
          · exact .inl
              ⟨right, wellFormed.2.2.2.2.1,
                assignedNoneOfTokenNone rightIdle, rightRank⟩
        · rcases waiting with
            ⟨leftToken, rightToken, leftMarked, rightMarked,
              different, registered⟩
          exact .inr
            ⟨conclusionUnassigned, index, left, right,
              leftToken, rightToken, linkLookup, leftMarked,
              rightMarked, different, registered⟩
    | tensor left right conclusion =>
        simp [Link.produces] at produces
        subst conclusion
        have wellFormed :
            certificate.LinkWellFormed
              (.tensor left right vertex) :=
          correct.1.2.2.2.2.1 _ linkMembership
        have leftRank :
            certificate.formulaComplexityAt left <
              certificate.formulaComplexityAt vertex := by
          simpa [Certificate.linkConclusionComplexity] using
            wellFormed.premise_complexity_lt_conclusion
              (premise := left) (by simp [Link.premises])
        have rightRank :
            certificate.formulaComplexityAt right <
              certificate.formulaComplexityAt vertex := by
          simpa [Certificate.linkConclusionComplexity] using
            wellFormed.premise_complexity_lt_conclusion
              (premise := right) (by simp [Link.premises])
        rcases obstruction with
          ⟨conclusionUnassigned, idle | deadlock⟩
        · rcases idle with leftIdle | rightIdle
          · exact .inl
              ⟨left, wellFormed.2.2.2.1,
                assignedNoneOfTokenNone leftIdle, leftRank⟩
          · exact .inl
              ⟨right, wellFormed.2.2.2.2.1,
                assignedNoneOfTokenNone rightIdle, rightRank⟩
        · rcases deadlock with
            ⟨token, leftMarked, rightMarked⟩
          exact False.elim
            (sameThread_tensorDeadlock_false
              correct coreInvariant.1 connected linkMembership
              conclusionUnassigned leftMarked rightMarked)
  cases formula with
  | atom name positive =>
      cases link with
      | «axiom» left right =>
          have endpoints :
              final.core.assignedToken? left ≠ none ∧
                final.core.assignedToken? right ≠ none := by
            simpa [final] using
              canonicalWorklistRun_axiom_endpoints_assigned
                correct.1 startEquation linkMembership
          simp [Link.containsAxiomEndpoint] at source
          rcases source with leftSource | rightSource
          · exact False.elim
              (endpoints.1 (by simpa [leftSource] using vertexUnassigned))
          · exact False.elim
              (endpoints.2 (by simpa [rightSource] using vertexUnassigned))
      | tensor left right conclusion =>
          simp [Link.containsAxiomEndpoint] at source
      | «par» left right conclusion =>
          simp [Link.containsAxiomEndpoint] at source
  | tensor formulaLeft formulaRight =>
      exact compoundCase source
  | par formulaLeft formulaRight =>
      exact compoundCase source

/-- Strict formula-complexity descent is well founded: every unassigned
occurrence in a correct quiescent run reaches a concrete registered waiting
par whose conclusion is no more complex than the starting occurrence. -/
private theorem canonicalWorklistRun_unassigned_reaches_waitingPar
    {certificate : Certificate} {started : UnificationState}
    (correct : certificate.DeclarativelyCorrect)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    ∀ {vertex : Vertex},
      vertex < certificate.formulas.size →
        final.core.assignedToken? vertex = none →
          ∃ conclusion,
            QuiescentWaitingParAt certificate final conclusion ∧
              certificate.formulaComplexityAt conclusion ≤
                certificate.formulaComplexityAt vertex := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  change
    ∀ {vertex : Vertex},
      vertex < certificate.formulas.size →
        final.core.assignedToken? vertex = none →
          ∃ conclusion,
            QuiescentWaitingParAt certificate final conclusion ∧
              certificate.formulaComplexityAt conclusion ≤
                certificate.formulaComplexityAt vertex
  have general :
      ∀ rank vertex,
        certificate.formulaComplexityAt vertex = rank →
          vertex < certificate.formulas.size →
            final.core.assignedToken? vertex = none →
              ∃ conclusion,
                QuiescentWaitingParAt certificate final conclusion ∧
                  certificate.formulaComplexityAt conclusion ≤ rank := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank induction =>
        intro vertex rankEquation vertexBound vertexUnassigned
        have alternative :=
          canonicalWorklistRun_unassigned_descends_or_waitingPar
            correct startEquation vertexBound vertexUnassigned
        rcases alternative with descent | waiting
        · rcases descent with
            ⟨blockedPremise, blockedBound, blockedUnassigned,
              strictDescent⟩
          have blockedRank :
              certificate.formulaComplexityAt blockedPremise < rank := by
            simpa [rankEquation] using strictDescent
          rcases induction
              (certificate.formulaComplexityAt blockedPremise)
              blockedRank blockedPremise rfl blockedBound
              blockedUnassigned with
            ⟨conclusion, reached, conclusionBound⟩
          exact
            ⟨conclusion, reached,
              Nat.le_trans conclusionBound
                (Nat.le_of_lt blockedRank)⟩
        · exact
            ⟨vertex, waiting, by simp [rankEquation]⟩
  intro vertex vertexBound vertexUnassigned
  exact
    general (certificate.formulaComplexityAt vertex) vertex rfl
      vertexBound vertexUnassigned

/-- Least-number principle specialized locally so the unification module does
not depend on private sequentialization helpers. -/
private theorem unification_exists_least_nat_up_to
    (property : Nat → Prop) :
    ∀ bound, (∃ value, value ≤ bound ∧ property value) →
      ∃ least, property least ∧
        ∀ value, property value → least ≤ value := by
  intro bound
  induction bound with
  | zero =>
      rintro ⟨value, valueBound, propertyValue⟩
      have valueZero : value = 0 := by omega
      subst value
      exact ⟨0, propertyValue, by intro; omega⟩
  | succ bound induction =>
      intro existsBounded
      by_cases existsEarlier :
          ∃ value, value ≤ bound ∧ property value
      · exact induction existsEarlier
      · rcases existsBounded with
          ⟨value, valueBound, propertyValue⟩
        have notEarlier : ¬value ≤ bound := by
          intro earlier
          exact existsEarlier ⟨value, earlier, propertyValue⟩
        have valueLast : value = bound + 1 := by omega
        subst value
        refine ⟨bound + 1, propertyValue, ?_⟩
        intro other propertyOther
        have otherNotEarlier : ¬other ≤ bound := by
          intro earlier
          exact existsEarlier ⟨other, earlier, propertyOther⟩
        omega

private theorem unification_exists_least_nat
    (property : Nat → Prop)
    (existsProperty : ∃ value, property value) :
    ∃ least, property least ∧
      ∀ value, property value → least ≤ value := by
  rcases existsProperty with ⟨bound, propertyBound⟩
  exact unification_exists_least_nat_up_to property bound
    ⟨bound, by omega, propertyBound⟩

/-- A quiescent obstruction at a minimum-complexity unassigned conclusion
cannot be idle: both strictly smaller premises are already assigned. -/
private theorem minimumUnassigned_threadObstruction
    {certificate : Certificate} {state : UnificationWorklistState}
    {index vertex : Vertex} {link : Link}
    (structural : certificate.StructurallyWellFormed)
    (linkLookup : certificate.links[index]? = some link)
    (produces : link.produces vertex = true)
    (minimality :
      ∀ {candidate : Vertex},
        candidate < certificate.formulas.size →
          state.core.assignedToken? candidate = none →
            certificate.formulaComplexityAt vertex ≤
              certificate.formulaComplexityAt candidate)
    (obstruction :
      QuiescentConnectiveObstruction state index link) :
    link.isConnective = true ∧
      QuiescentThreadObstruction state index link := by
  have linkMembership : link ∈ certificate.links :=
    List.mem_of_getElem? linkLookup
  cases link with
  | «axiom» left right =>
      simp [Link.produces] at produces
  | tensor left right conclusion =>
      simp [Link.produces] at produces
      subst conclusion
      have wellFormed :
          certificate.LinkWellFormed
            (.tensor left right vertex) :=
        structural.2.2.2.2.1 _ linkMembership
      have leftRank :
          certificate.formulaComplexityAt left <
            certificate.formulaComplexityAt vertex := by
        simpa [Certificate.linkConclusionComplexity] using
          wellFormed.premise_complexity_lt_conclusion
            (premise := left) (by simp [Link.premises])
      have rightRank :
          certificate.formulaComplexityAt right <
            certificate.formulaComplexityAt vertex := by
        simpa [Certificate.linkConclusionComplexity] using
          wellFormed.premise_complexity_lt_conclusion
            (premise := right) (by simp [Link.premises])
      have leftAssigned :
          state.core.assignedToken? left ≠ none := by
        intro leftUnassigned
        have lower :=
          minimality wellFormed.2.2.2.1 leftUnassigned
        omega
      have rightAssigned :
          state.core.assignedToken? right ≠ none := by
        intro rightUnassigned
        have lower :=
          minimality wellFormed.2.2.2.2.1 rightUnassigned
        omega
      rcases state.core.tokenAt?_exists_of_assigned leftAssigned with
        ⟨leftToken, leftLookup⟩
      rcases state.core.tokenAt?_exists_of_assigned rightAssigned with
        ⟨rightToken, rightLookup⟩
      rcases obstruction with
        ⟨conclusionUnassigned, idle | deadlock⟩
      · rcases idle with leftIdle | rightIdle
        · rw [leftIdle] at leftLookup
          contradiction
        · rw [rightIdle] at rightLookup
          contradiction
      · exact ⟨rfl, conclusionUnassigned, deadlock⟩
  | «par» left right conclusion =>
      simp [Link.produces] at produces
      subst conclusion
      have wellFormed :
          certificate.LinkWellFormed
            (.par left right vertex) :=
        structural.2.2.2.2.1 _ linkMembership
      have leftRank :
          certificate.formulaComplexityAt left <
            certificate.formulaComplexityAt vertex := by
        simpa [Certificate.linkConclusionComplexity] using
          wellFormed.premise_complexity_lt_conclusion
            (premise := left) (by simp [Link.premises])
      have rightRank :
          certificate.formulaComplexityAt right <
            certificate.formulaComplexityAt vertex := by
        simpa [Certificate.linkConclusionComplexity] using
          wellFormed.premise_complexity_lt_conclusion
            (premise := right) (by simp [Link.premises])
      have leftAssigned :
          state.core.assignedToken? left ≠ none := by
        intro leftUnassigned
        have lower :=
          minimality wellFormed.2.2.2.1 leftUnassigned
        omega
      have rightAssigned :
          state.core.assignedToken? right ≠ none := by
        intro rightUnassigned
        have lower :=
          minimality wellFormed.2.2.2.2.1 rightUnassigned
        omega
      rcases state.core.tokenAt?_exists_of_assigned leftAssigned with
        ⟨leftToken, leftLookup⟩
      rcases state.core.tokenAt?_exists_of_assigned rightAssigned with
        ⟨rightToken, rightLookup⟩
      rcases obstruction with
        ⟨conclusionUnassigned, idle | waiting⟩
      · rcases idle with leftIdle | rightIdle
        · rw [leftIdle] at leftLookup
          contradiction
        · rw [rightIdle] at rightLookup
          contradiction
      · exact ⟨rfl, conclusionUnassigned, waiting⟩

/-- Choosing an unmarked conclusion of least formula complexity eliminates
the idle-premise branch.  Thus every incomplete canonical run exposes one of
the two genuine thread obstructions that correctness must rule out. -/
private theorem canonicalWorklistRun_incomplete_thread_obstruction
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    final.core.allMarked = false →
      ∃ (index vertex : Nat) (link : Link),
        certificate.links[index]? = some link ∧
          link.produces vertex = true ∧
            final.core.assignedToken? vertex = none ∧
              (∀ {candidate : Vertex},
                candidate < certificate.formulas.size →
                  final.core.assignedToken? candidate = none →
                    certificate.formulaComplexityAt vertex ≤
                      certificate.formulaComplexityAt candidate) ∧
                link.isConnective = true ∧
                  QuiescentThreadObstruction final index link := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  change
    final.core.allMarked = false →
      ∃ (index vertex : Nat) (link : Link),
        certificate.links[index]? = some link ∧
          link.produces vertex = true ∧
            final.core.assignedToken? vertex = none ∧
              (∀ {candidate : Vertex},
                candidate < certificate.formulas.size →
                  final.core.assignedToken? candidate = none →
                    certificate.formulaComplexityAt vertex ≤
                      certificate.formulaComplexityAt candidate) ∧
                link.isConnective = true ∧
                  QuiescentThreadObstruction final index link
  intro incomplete
  have coreInvariant :
      WorklistCoreInvariant certificate final := by
    simpa [final] using
      canonicalWorklistRun_coreInvariant structural startEquation
  have marksIncomplete :
      final.core.marks.all Option.isSome = false := by
    simpa [UnificationState.allMarked] using incomplete
  rcases Array.all_eq_false.mp marksIncomplete with
    ⟨witness, witnessMarkBound, witnessUnassignedElement⟩
  have witnessRawNone : final.core.marks[witness] = none := by
    cases lookup : final.core.marks[witness] with
    | none =>
        rfl
    | some token =>
        simp [lookup] at witnessUnassignedElement
  have witnessAssignedNone :
      final.core.assignedToken? witness = none := by
    unfold UnificationState.assignedToken?
    rw [Array.getElem?_eq_getElem witnessMarkBound, witnessRawNone]
    rfl
  have witnessFormulaBound :
      witness < certificate.formulas.size := by
    simpa [coreInvariant.1.markArraySize] using witnessMarkBound
  let property : Nat → Prop := fun rank =>
    ∃ vertex,
      vertex < certificate.formulas.size ∧
        final.core.assignedToken? vertex = none ∧
          certificate.formulaComplexityAt vertex = rank
  have propertyExists : ∃ rank, property rank :=
    ⟨certificate.formulaComplexityAt witness,
      witness, witnessFormulaBound, witnessAssignedNone, rfl⟩
  rcases unification_exists_least_nat property propertyExists with
    ⟨least, ⟨vertex, vertexBound, vertexUnassigned, vertexRank⟩,
      leastBound⟩
  have minimality :
      ∀ {candidate : Vertex},
        candidate < certificate.formulas.size →
          final.core.assignedToken? candidate = none →
            certificate.formulaComplexityAt vertex ≤
              certificate.formulaComplexityAt candidate := by
    intro candidate candidateBound candidateUnassigned
    have bound :=
      leastBound (certificate.formulaComplexityAt candidate)
        ⟨candidate, candidateBound, candidateUnassigned, rfl⟩
    simpa [vertexRank] using bound
  rcases
      structurallyWellFormed_sourceLink_exists
        structural vertexBound with
    ⟨formula, link, index, _formulaLookup, linkLookup, source⟩
  have linkMembership : link ∈ certificate.links :=
    List.mem_of_getElem? linkLookup
  have compoundCase :
      link.produces vertex = true →
        ∃ (resultIndex resultVertex : Nat) (resultLink : Link),
          certificate.links[resultIndex]? = some resultLink ∧
            resultLink.produces resultVertex = true ∧
              final.core.assignedToken? resultVertex = none ∧
                (∀ {candidate : Vertex},
                  candidate < certificate.formulas.size →
                    final.core.assignedToken? candidate = none →
                      certificate.formulaComplexityAt resultVertex ≤
                        certificate.formulaComplexityAt candidate) ∧
                  resultLink.isConnective = true ∧
                    QuiescentThreadObstruction final resultIndex resultLink := by
    intro produces
    have connective : link.isConnective = true := by
      cases link <;>
        simp [Link.produces, Link.isConnective] at produces ⊢
    have unfired : ¬linkFiredIn final.core link := by
      cases link with
      | «axiom» left right =>
          simp [Link.isConnective] at connective
      | tensor left right conclusion =>
          simp [Link.produces] at produces
          subst conclusion
          exact fun fired => fired vertexUnassigned
      | «par» left right conclusion =>
          simp [Link.produces] at produces
          subst conclusion
          exact fun fired => fired vertexUnassigned
    have obstruction :
        QuiescentConnectiveObstruction final index link :=
      canonicalWorklistRun_unfired_obstruction
        structural startEquation linkLookup connective unfired
    have strengthened :=
      minimumUnassigned_threadObstruction
        structural linkLookup produces minimality obstruction
    exact
      ⟨index, vertex, link, linkLookup, produces, vertexUnassigned,
        minimality, strengthened.1, strengthened.2⟩
  cases formula with
  | atom name positive =>
      cases link with
      | «axiom» left right =>
          have endpoints :
              final.core.assignedToken? left ≠ none ∧
                final.core.assignedToken? right ≠ none := by
            simpa [final] using
              canonicalWorklistRun_axiom_endpoints_assigned
                structural startEquation linkMembership
          simp [Link.containsAxiomEndpoint] at source
          rcases source with leftSource | rightSource
          · exact False.elim
              (endpoints.1 (by
                simpa [leftSource] using vertexUnassigned))
          · exact False.elim
              (endpoints.2 (by
                simpa [rightSource] using vertexUnassigned))
      | tensor left right conclusion =>
          simp [Link.containsAxiomEndpoint] at source
      | «par» left right conclusion =>
          simp [Link.containsAxiomEndpoint] at source
  | tensor formulaLeft formulaRight =>
      exact compoundCase source
  | par formulaLeft formulaRight =>
      exact compoundCase source

/-- Declarative proof-net correctness eliminates the same-thread tensor
deadlock branch.  Therefore any incomplete canonical run is witnessed by one
submitted par whose two assigned premises remain in distinct threads. -/
private theorem canonicalWorklistRun_incomplete_waitingPar
    {certificate : Certificate} {started : UnificationState}
    (correct : certificate.DeclarativelyCorrect)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    final.core.allMarked = false →
      ∃ index left right conclusion leftToken rightToken,
        certificate.links[index]? =
            some (.par left right conclusion) ∧
          final.core.assignedToken? conclusion = none ∧
            final.core.tokenAt? left = some leftToken ∧
              final.core.tokenAt? right = some rightToken ∧
                leftToken ≠ rightToken ∧
                  index ∈ final.waiting ∧
                    (∀ {candidate : Vertex},
                      candidate < certificate.formulas.size →
                        final.core.assignedToken? candidate = none →
                          certificate.formulaComplexityAt conclusion ≤
                            certificate.formulaComplexityAt candidate) ∧
                    ¬((final.core.toMarking certificate
                        (canonicalWorklistRun_coreInvariant
                          correct.1 startEquation).1)
                      |>.activeReferenceGraph.Walk left right) := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  change
    final.core.allMarked = false →
      ∃ index left right conclusion leftToken rightToken,
        certificate.links[index]? =
            some (.par left right conclusion) ∧
          final.core.assignedToken? conclusion = none ∧
            final.core.tokenAt? left = some leftToken ∧
              final.core.tokenAt? right = some rightToken ∧
                leftToken ≠ rightToken ∧
                  index ∈ final.waiting ∧
                    (∀ {candidate : Vertex},
                      candidate < certificate.formulas.size →
                        final.core.assignedToken? candidate = none →
                          certificate.formulaComplexityAt conclusion ≤
                            certificate.formulaComplexityAt candidate) ∧
                    ¬((final.core.toMarking certificate
                        (canonicalWorklistRun_coreInvariant
                          correct.1 startEquation).1)
                      |>.activeReferenceGraph.Walk left right)
  intro incomplete
  rcases canonicalWorklistRun_incomplete_thread_obstruction
      correct.1 startEquation incomplete with
    ⟨index, vertex, link, linkLookup, produces, _vertexUnassigned,
      minimality, _connective, obstruction⟩
  have coreInvariant :
      WorklistCoreInvariant certificate final := by
    simpa [final] using
      canonicalWorklistRun_coreInvariant correct.1 startEquation
  have connected :
      UnificationMarking.ThreadConnected
        (final.core.toMarking certificate coreInvariant.1) := by
    unfold UnificationMarking.ThreadConnected
    intro firstVertex secondVertex firstToken secondToken
      firstMarked secondMarked synchronized
    dsimp [final] at firstMarked secondMarked synchronized ⊢
    exact
      (canonicalWorklistRun_threadConnected correct.1 startEquation)
        firstMarked secondMarked synchronized
  have exactComponents :
      UnificationMarking.ThreadComponentsExact
        (final.core.toMarking certificate coreInvariant.1) := by
    dsimp [final]
    exact canonicalWorklistRun_threadComponentsExact
      correct.1 startEquation
  cases link with
  | «axiom» left right =>
      simp [QuiescentThreadObstruction] at obstruction
  | «par» left right conclusion =>
      simp [Link.produces] at produces
      subst vertex
      rcases obstruction with
        ⟨conclusionUnmarked, leftToken, rightToken,
          leftMarked, rightMarked, different, registered⟩
      rcases final.core.tokenAt?_some_witness leftMarked with
        ⟨leftRaw, leftRawMarked, leftRepresentative⟩
      rcases final.core.tokenAt?_some_witness rightMarked with
        ⟨rightRaw, rightRawMarked, rightRepresentative⟩
      have abstractLeftMarked :
          (final.core.toMarking certificate coreInvariant.1).mark left =
            some leftRaw := by
        simpa only [UnificationState.toMarking_mark] using leftRawMarked
      have abstractRightMarked :
          (final.core.toMarking certificate coreInvariant.1).mark right =
            some rightRaw := by
        simpa only [UnificationState.toMarking_mark] using rightRawMarked
      have notSynchronized :
          ¬(final.core.toMarking certificate coreInvariant.1).sameThread
            leftRaw rightRaw := by
        simp only [UnificationState.toMarking_sameThread]
        intro representativesEqual
        apply different
        rw [← leftRepresentative, ← rightRepresentative]
        exact representativesEqual
      have noActiveWalk :
          ¬((final.core.toMarking certificate coreInvariant.1)
            |>.activeReferenceGraph.Walk left right) := by
        intro walk
        exact notSynchronized
          ((exactComponents.walk_iff_sameThread
              (final.core.toMarking certificate coreInvariant.1)
              abstractLeftMarked abstractRightMarked).mp walk)
      exact
        ⟨index, left, right, conclusion, leftToken, rightToken,
          linkLookup, conclusionUnmarked, leftMarked, rightMarked,
          different, registered, minimality, by
            simpa only using noActiveWalk⟩
  | tensor left right conclusion =>
      simp [Link.produces] at produces
      subst vertex
      rcases obstruction with
        ⟨conclusionUnmarked, token, leftMarked, rightMarked⟩
      have linkMembership :
          Link.tensor left right conclusion ∈ certificate.links :=
        List.mem_of_getElem? linkLookup
      exact False.elim
        (sameThread_tensorDeadlock_false
          correct coreInvariant.1 connected linkMembership
          conclusionUnmarked leftMarked rightMarked)

/-- At quiescence, a forward par frontier with its retained left premise
assigned is either waiting on an unassigned right premise or is registered
with two distinct live tokens. -/
private theorem canonicalWorklistRun_par_frontier_status
    {certificate : Certificate} {started : UnificationState}
    (correct : certificate.DeclarativelyCorrect)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started)
    {index left right conclusion : Nat}
    (linkLookup :
      certificate.links[index]? =
        some (.par left right conclusion))
    (conclusionUnmarked :
      let final :=
        (runUnificationWorklist certificate
          certificate.worklistConsumers
          (worklistFuel certificate.links.length)
          (initializeWorklist certificate started)).state
      final.core.assignedToken? conclusion = none)
    (leftAssigned :
      let final :=
        (runUnificationWorklist certificate
          certificate.worklistConsumers
          (worklistFuel certificate.links.length)
          (initializeWorklist certificate started)).state
      final.core.assignedToken? left ≠ none) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    final.core.assignedToken? right = none ∨
      ∃ leftToken rightToken,
        final.core.tokenAt? left = some leftToken ∧
          final.core.tokenAt? right = some rightToken ∧
            leftToken ≠ rightToken ∧
              index ∈ final.waiting := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  change final.core.assignedToken? conclusion = none at conclusionUnmarked
  change final.core.assignedToken? left ≠ none at leftAssigned
  change
    final.core.assignedToken? right = none ∨
      ∃ leftToken rightToken,
        final.core.tokenAt? left = some leftToken ∧
          final.core.tokenAt? right = some rightToken ∧
            leftToken ≠ rightToken ∧
              index ∈ final.waiting
  have unfired :
      ¬linkFiredIn final.core (.par left right conclusion) := by
    intro fired
    exact fired conclusionUnmarked
  have obstruction :
      QuiescentConnectiveObstruction
        final index (.par left right conclusion) := by
    simpa [final] using
      canonicalWorklistRun_unfired_obstruction
        correct.1 startEquation linkLookup rfl unfired
  rcases obstruction with
    ⟨_conclusionUnmarked, idle | waiting⟩
  · rcases idle with leftIdle | rightIdle
    · rcases final.core.tokenAt?_exists_of_assigned leftAssigned with
        ⟨leftToken, leftLookup⟩
      rw [leftIdle] at leftLookup
      contradiction
    · apply Or.inl
      apply Classical.byContradiction
      intro rightAssigned
      rcases final.core.tokenAt?_exists_of_assigned rightAssigned with
        ⟨rightToken, rightLookup⟩
      rw [rightIdle] at rightLookup
      contradiction
  · exact Or.inr waiting

/-- At quiescence, a forward tensor frontier cannot have both premises
assigned in a correct proof net: that would be the already-excluded
same-thread tensor deadlock.  Therefore the premise opposite any assigned
frontier source is exactly unassigned. -/
private theorem canonicalWorklistRun_tensor_frontier_status
    {certificate : Certificate} {started : UnificationState}
    (correct : certificate.DeclarativelyCorrect)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started)
    {index left right conclusion : Nat}
    (linkLookup :
      certificate.links[index]? =
        some (.tensor left right conclusion))
    (conclusionUnmarked :
      let final :=
        (runUnificationWorklist certificate
          certificate.worklistConsumers
          (worklistFuel certificate.links.length)
          (initializeWorklist certificate started)).state
      final.core.assignedToken? conclusion = none)
    (sourceAssigned :
      let final :=
        (runUnificationWorklist certificate
          certificate.worklistConsumers
          (worklistFuel certificate.links.length)
          (initializeWorklist certificate started)).state
      final.core.assignedToken? left ≠ none ∨
        final.core.assignedToken? right ≠ none) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    (final.core.assignedToken? left ≠ none ∧
        final.core.assignedToken? right = none) ∨
      (final.core.assignedToken? right ≠ none ∧
        final.core.assignedToken? left = none) := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  change final.core.assignedToken? conclusion = none at conclusionUnmarked
  change
    final.core.assignedToken? left ≠ none ∨
      final.core.assignedToken? right ≠ none at sourceAssigned
  change
    (final.core.assignedToken? left ≠ none ∧
        final.core.assignedToken? right = none) ∨
      (final.core.assignedToken? right ≠ none ∧
        final.core.assignedToken? left = none)
  have unfired :
      ¬linkFiredIn final.core (.tensor left right conclusion) := by
    intro fired
    exact fired conclusionUnmarked
  have obstruction :
      QuiescentConnectiveObstruction
        final index (.tensor left right conclusion) := by
    simpa [final] using
      canonicalWorklistRun_unfired_obstruction
        correct.1 startEquation linkLookup rfl unfired
  rcases obstruction with
    ⟨_conclusionUnmarked, idle | deadlock⟩
  · rcases idle with leftIdle | rightIdle
    · have leftUnassigned :
          final.core.assignedToken? left = none := by
        apply Classical.byContradiction
        intro leftAssigned
        rcases final.core.tokenAt?_exists_of_assigned leftAssigned with
          ⟨leftToken, leftLookup⟩
        rw [leftIdle] at leftLookup
        contradiction
      rcases sourceAssigned with leftAssigned | rightAssigned
      · exact False.elim (leftAssigned leftUnassigned)
      · exact Or.inr ⟨rightAssigned, leftUnassigned⟩
    · have rightUnassigned :
          final.core.assignedToken? right = none := by
        apply Classical.byContradiction
        intro rightAssigned
        rcases final.core.tokenAt?_exists_of_assigned rightAssigned with
          ⟨rightToken, rightLookup⟩
        rw [rightIdle] at rightLookup
        contradiction
      rcases sourceAssigned with leftAssigned | rightAssigned
      · exact Or.inl ⟨leftAssigned, rightUnassigned⟩
      · exact False.elim (rightAssigned rightUnassigned)
  · rcases deadlock with
      ⟨token, leftLookup, rightLookup⟩
    have coreInvariant :
        WorklistCoreInvariant certificate final := by
      simpa [final] using
        canonicalWorklistRun_coreInvariant correct.1 startEquation
    have connected :
        UnificationMarking.ThreadConnected
          (final.core.toMarking certificate coreInvariant.1) := by
      unfold UnificationMarking.ThreadConnected
      intro firstVertex secondVertex firstToken secondToken
        firstMarked secondMarked synchronized
      dsimp [final] at firstMarked secondMarked synchronized ⊢
      exact
        (canonicalWorklistRun_threadConnected correct.1 startEquation)
          firstMarked secondMarked synchronized
    have linkMembership :
        Link.tensor left right conclusion ∈ certificate.links :=
      List.mem_of_getElem? linkLookup
    exact False.elim
      (sameThread_tensorDeadlock_false
        correct coreInvariant.1 connected linkMembership
        conclusionUnmarked leftLookup rightLookup)

/-- A directed reference-switching occurrence has the retained forward
orientation of a concrete submitted par or tensor link. -/
private def ForwardReferenceConnectiveOccurrence
    (certificate : Certificate)
    (boundary : certificate.referenceSwitchingGraph.DirectedEdge) : Prop :=
  (∃ (index left right conclusion : Nat),
      certificate.links[index]? =
          some (.par left right conclusion) ∧
        boundary.source = left ∧
          boundary.target = conclusion) ∨
    ∃ (index left right conclusion : Nat),
      certificate.links[index]? =
          some (.tensor left right conclusion) ∧
        (boundary.source = left ∨ boundary.source = right) ∧
          boundary.target = conclusion

/-- Exact scheduler meaning of a marked-to-unmarked forward occurrence on
the retained reference path.  A par either waits on its unassigned omitted
premise or is registered on two distinct threads.  A tensor's opposite
premise must be unassigned. -/
private def PathFrontierSchedulerObstruction
    (certificate : Certificate)
    (state : UnificationWorklistState)
    (boundary : certificate.referenceSwitchingGraph.DirectedEdge) : Prop :=
  (∃ (index left right conclusion : Nat),
      certificate.links[index]? =
          some (.par left right conclusion) ∧
        boundary.source = left ∧
          boundary.target = conclusion ∧
            (state.core.assignedToken? right = none ∨
              ∃ leftToken rightToken,
                state.core.tokenAt? left = some leftToken ∧
                  state.core.tokenAt? right = some rightToken ∧
                    leftToken ≠ rightToken ∧
                      index ∈ state.waiting)) ∨
    ∃ (index left right conclusion : Nat),
      certificate.links[index]? =
          some (.tensor left right conclusion) ∧
        boundary.target = conclusion ∧
          ((boundary.source = left ∧
              state.core.assignedToken? right = none) ∨
            (boundary.source = right ∧
              state.core.assignedToken? left = none))

/-- A quiescent forward frontier either descends strictly to an unassigned
premise or is itself a concrete distinct-thread waiting par. -/
private def PathFrontierDescentOrWaitingPar
    (certificate : Certificate)
    (state : UnificationWorklistState)
  (boundary : certificate.referenceSwitchingGraph.DirectedEdge) : Prop :=
  (∃ blockedPremise : Vertex,
      blockedPremise < certificate.formulas.size ∧
        state.core.assignedToken? blockedPremise = none ∧
          certificate.formulaComplexityAt blockedPremise <
            certificate.formulaComplexityAt boundary.target) ∨
    ∃ (index left right conclusion leftToken rightToken : Nat),
      certificate.links[index]? =
          some (.par left right conclusion) ∧
        boundary.source = left ∧
          boundary.target = conclusion ∧
            state.core.tokenAt? left = some leftToken ∧
              state.core.tokenAt? right = some rightToken ∧
                leftToken ≠ rightToken ∧
                  index ∈ state.waiting

/-- Structural formula descent turns the exact scheduler classification into
the chase alternative used by the global progress proof. -/
private theorem pathFrontierSchedulerObstruction_descent_or_waitingPar
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {state : UnificationWorklistState}
    {boundary : certificate.referenceSwitchingGraph.DirectedEdge}
    (obstruction :
      PathFrontierSchedulerObstruction certificate state boundary) :
    PathFrontierDescentOrWaitingPar certificate state boundary := by
  rcases obstruction with parObstruction | tensorObstruction
  · rcases parObstruction with
      ⟨index, left, right, conclusion, linkLookup,
        sourceEquation, targetEquation, status⟩
    rcases status with rightUnassigned | waiting
    · have linkMembership :
          Link.par left right conclusion ∈ certificate.links :=
        List.mem_of_getElem? linkLookup
      have wellFormed :
          certificate.LinkWellFormed
            (.par left right conclusion) :=
        structural.2.2.2.2.1 _ linkMembership
      have rightRank :
          certificate.formulaComplexityAt right <
            certificate.formulaComplexityAt conclusion := by
        simpa [Certificate.linkConclusionComplexity] using
          wellFormed.premise_complexity_lt_conclusion
            (premise := right) (by simp [Link.premises])
      exact .inl
        ⟨right, wellFormed.2.2.2.2.1, rightUnassigned,
          by simpa [targetEquation] using rightRank⟩
    · rcases waiting with
        ⟨leftToken, rightToken, leftMarked, rightMarked,
          different, registered⟩
      exact .inr
        ⟨index, left, right, conclusion, leftToken, rightToken,
          linkLookup, sourceEquation, targetEquation,
          leftMarked, rightMarked, different, registered⟩
  · rcases tensorObstruction with
      ⟨index, left, right, conclusion, linkLookup,
        targetEquation, status⟩
    have linkMembership :
        Link.tensor left right conclusion ∈ certificate.links :=
      List.mem_of_getElem? linkLookup
    have wellFormed :
        certificate.LinkWellFormed
          (.tensor left right conclusion) :=
      structural.2.2.2.2.1 _ linkMembership
    rcases status with
      ⟨_sourceLeft, rightUnassigned⟩ |
        ⟨_sourceRight, leftUnassigned⟩
    · have rightRank :
          certificate.formulaComplexityAt right <
            certificate.formulaComplexityAt conclusion := by
        simpa [Certificate.linkConclusionComplexity] using
          wellFormed.premise_complexity_lt_conclusion
            (premise := right) (by simp [Link.premises])
      exact .inl
        ⟨right, wellFormed.2.2.2.2.1, rightUnassigned,
          by simpa [targetEquation] using rightRank⟩
    · have leftRank :
          certificate.formulaComplexityAt left <
            certificate.formulaComplexityAt conclusion := by
        simpa [Certificate.linkConclusionComplexity] using
          wellFormed.premise_complexity_lt_conclusion
            (premise := left) (by simp [Link.premises])
      exact .inl
        ⟨left, wellFormed.2.2.2.1, leftUnassigned,
          by simpa [targetEquation] using leftRank⟩

/-- The local frontier alternative cannot descend forever.  Starting from any
unassigned forward-frontier conclusion, strict premise descent reaches a
concrete registered waiting par, while the direct waiting branch is already
such an endpoint. -/
private theorem canonicalWorklistRun_pathFrontier_reaches_waitingPar
    {certificate : Certificate} {started : UnificationState}
    (correct : certificate.DeclarativelyCorrect)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    ∀ {boundary :
        certificate.referenceSwitchingGraph.DirectedEdge},
      final.core.assignedToken? boundary.target = none →
        PathFrontierSchedulerObstruction
          certificate final boundary →
          ∃ conclusion,
            QuiescentWaitingParAt certificate final conclusion ∧
              certificate.formulaComplexityAt conclusion ≤
                certificate.formulaComplexityAt boundary.target := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  change
    ∀ {boundary :
        certificate.referenceSwitchingGraph.DirectedEdge},
      final.core.assignedToken? boundary.target = none →
        PathFrontierSchedulerObstruction
          certificate final boundary →
          ∃ conclusion,
            QuiescentWaitingParAt certificate final conclusion ∧
              certificate.formulaComplexityAt conclusion ≤
                certificate.formulaComplexityAt boundary.target
  intro boundary targetUnassigned obstruction
  have alternative :=
    pathFrontierSchedulerObstruction_descent_or_waitingPar
      correct.1 obstruction
  rcases alternative with descent | waiting
  · rcases descent with
      ⟨blockedPremise, blockedBound, blockedUnassigned,
        strictDescent⟩
    rcases canonicalWorklistRun_unassigned_reaches_waitingPar
        correct startEquation blockedBound blockedUnassigned with
      ⟨conclusion, reached, conclusionBound⟩
    exact
      ⟨conclusion, reached,
        Nat.le_trans conclusionBound
          (Nat.le_of_lt strictDescent)⟩
  · rcases waiting with
      ⟨index, left, right, conclusion, leftToken, rightToken,
        linkLookup, _sourceEquation, targetEquation,
        leftMarked, rightMarked, different, registered⟩
    subst conclusion
    exact
      ⟨boundary.target,
        ⟨targetUnassigned, index, left, right,
          leftToken, rightToken, linkLookup, leftMarked,
          rightMarked, different, registered⟩,
        Nat.le_refl _⟩

/-- Any quiescent forward connective frontier with an assigned source and an
unassigned conclusion has the exact residual scheduler status recorded by
`PathFrontierSchedulerObstruction`. -/
private theorem canonicalWorklistRun_forwardFrontier_status
    {certificate : Certificate} {started : UnificationState}
    (correct : certificate.DeclarativelyCorrect)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started)
    {boundary : certificate.referenceSwitchingGraph.DirectedEdge}
    (sourceAssigned :
      let final :=
        (runUnificationWorklist certificate
          certificate.worklistConsumers
          (worklistFuel certificate.links.length)
          (initializeWorklist certificate started)).state
      final.core.assignedToken? boundary.source ≠ none)
    (targetUnmarked :
      let final :=
        (runUnificationWorklist certificate
          certificate.worklistConsumers
          (worklistFuel certificate.links.length)
          (initializeWorklist certificate started)).state
      final.core.assignedToken? boundary.target = none)
    (origin :
      ForwardReferenceConnectiveOccurrence certificate boundary) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    PathFrontierSchedulerObstruction certificate final boundary := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  change final.core.assignedToken? boundary.source ≠ none at sourceAssigned
  change final.core.assignedToken? boundary.target = none at targetUnmarked
  change PathFrontierSchedulerObstruction certificate final boundary
  rcases origin with parOrigin | tensorOrigin
  · rcases parOrigin with
      ⟨index, left, right, conclusion, linkLookup,
        sourceEquation, targetEquation⟩
    have conclusionUnmarked :
        final.core.assignedToken? conclusion = none := by
      simpa [targetEquation] using targetUnmarked
    have leftAssigned :
        final.core.assignedToken? left ≠ none := by
      simpa [sourceEquation] using sourceAssigned
    have status :=
      canonicalWorklistRun_par_frontier_status
        correct startEquation linkLookup conclusionUnmarked leftAssigned
    exact Or.inl
      ⟨index, left, right, conclusion, linkLookup,
        sourceEquation, targetEquation, status⟩
  · rcases tensorOrigin with
      ⟨index, left, right, conclusion, linkLookup,
        sourceEquation, targetEquation⟩
    have conclusionUnmarked :
        final.core.assignedToken? conclusion = none := by
      simpa [targetEquation] using targetUnmarked
    have oneSourceAssigned :
        final.core.assignedToken? left ≠ none ∨
          final.core.assignedToken? right ≠ none := by
      rcases sourceEquation with sourceLeft | sourceRight
      · exact Or.inl (by simpa [sourceLeft] using sourceAssigned)
      · exact Or.inr (by simpa [sourceRight] using sourceAssigned)
    have status :=
      canonicalWorklistRun_tensor_frontier_status
        correct startEquation linkLookup conclusionUnmarked
        oneSourceAssigned
    rcases sourceEquation with sourceLeft | sourceRight
    · rcases status with
        ⟨_leftAssigned, rightUnassigned⟩ |
          ⟨_rightAssigned, leftUnassigned⟩
      · exact Or.inr
          ⟨index, left, right, conclusion, linkLookup,
            targetEquation, Or.inl ⟨sourceLeft, rightUnassigned⟩⟩
      · exact False.elim
          (sourceAssigned (by simpa [sourceLeft] using leftUnassigned))
    · rcases status with
        ⟨_leftAssigned, rightUnassigned⟩ |
          ⟨_rightAssigned, leftUnassigned⟩
      · exact False.elim
          (sourceAssigned (by simpa [sourceRight] using rightUnassigned))
      · exact Or.inr
          ⟨index, left, right, conclusion, linkLookup,
            targetEquation, Or.inr ⟨sourceRight, leftUnassigned⟩⟩

/-- The residual waiting-par obstruction is path-exposed, not merely a pair
of disconnected scheduler tokens.  A correct proof net supplies an exact
reference-switching path between the premises which avoids the par
conclusion; failure of the active subgraph to connect the endpoints therefore
identifies an exact marked-to-unmarked edge occurrence on that path. Completed
axiom initialization and causal closure classify the occurrence as a forward
premise-to-conclusion edge of a concrete submitted par or tensor. -/
private theorem canonicalWorklistRun_incomplete_waitingParPath
    {certificate : Certificate} {started : UnificationState}
    (correct : certificate.DeclarativelyCorrect)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    final.core.allMarked = false →
      ∃ (index left right conclusion leftToken rightToken : Nat)
          (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (boundary :
            certificate.referenceSwitchingGraph.DirectedEdge)
          (before after :
            List certificate.referenceSwitchingGraph.DirectedEdge),
        certificate.links[index]? =
            some (.par left right conclusion) ∧
          final.core.assignedToken? conclusion = none ∧
            final.core.tokenAt? left = some leftToken ∧
              final.core.tokenAt? right = some rightToken ∧
                leftToken ≠ rightToken ∧
                  index ∈ final.waiting ∧
                    (∀ {candidate : Vertex},
                      candidate < certificate.formulas.size →
                        final.core.assignedToken? candidate = none →
                          certificate.formulaComplexityAt conclusion ≤
                            certificate.formulaComplexityAt candidate) ∧
                      ¬((final.core.toMarking certificate
                          (canonicalWorklistRun_coreInvariant
                            correct.1 startEquation).1)
                        |>.activeReferenceGraph.Walk left right) ∧
                      path.start = left ∧
                        path.finish = right ∧
                          conclusion ∉ path.vertices ∧
                            path.traversed =
                                before ++ boundary :: after ∧
                              (∀ candidate ∈ before,
                                ((final.core.toMarking certificate
                                    (canonicalWorklistRun_coreInvariant
                                      correct.1 startEquation).1)
                                  |>.mark candidate.source).isSome = true ∧
                                  ((final.core.toMarking certificate
                                      (canonicalWorklistRun_coreInvariant
                                        correct.1 startEquation).1)
                                    |>.mark candidate.target).isSome = true) ∧
                                boundary ∈ path.traversed ∧
                              ((final.core.toMarking certificate
                                  (canonicalWorklistRun_coreInvariant
                                    correct.1 startEquation).1)
                                |>.activeReferenceGraph.Walk
                                  left boundary.source) ∧
                                final.core.tokenAt? boundary.source =
                                    some leftToken ∧
                                final.core.assignedToken?
                                    boundary.source ≠ none ∧
                                final.core.assignedToken?
                                    boundary.target = none ∧
                                  boundary.target ≠ left ∧
                                    boundary.target ≠ right ∧
                                      boundary.target ≠ conclusion ∧
                                        ((∃ (frontierIndex frontierLeft
                                                frontierRight
                                                frontierConclusion : Nat),
                                            certificate.links[frontierIndex]? =
                                                some (.par frontierLeft
                                                  frontierRight
                                                  frontierConclusion) ∧
                                              boundary.source =
                                                  frontierLeft ∧
                                                boundary.target =
                                                  frontierConclusion) ∨
                                          ∃ (frontierIndex frontierLeft
                                                frontierRight
                                                frontierConclusion : Nat),
                                            certificate.links[frontierIndex]? =
                                                some (.tensor frontierLeft
                                                  frontierRight
                                                  frontierConclusion) ∧
                                              (boundary.source =
                                                  frontierLeft ∨
                                                boundary.source =
                                                  frontierRight) ∧
                                                boundary.target =
                                                  frontierConclusion) := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  change
    final.core.allMarked = false →
      ∃ (index left right conclusion leftToken rightToken : Nat)
          (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (boundary :
            certificate.referenceSwitchingGraph.DirectedEdge)
          (before after :
            List certificate.referenceSwitchingGraph.DirectedEdge),
        certificate.links[index]? =
            some (.par left right conclusion) ∧
          final.core.assignedToken? conclusion = none ∧
            final.core.tokenAt? left = some leftToken ∧
              final.core.tokenAt? right = some rightToken ∧
                leftToken ≠ rightToken ∧
                  index ∈ final.waiting ∧
                    (∀ {candidate : Vertex},
                      candidate < certificate.formulas.size →
                        final.core.assignedToken? candidate = none →
                          certificate.formulaComplexityAt conclusion ≤
                            certificate.formulaComplexityAt candidate) ∧
                      ¬((final.core.toMarking certificate
                          (canonicalWorklistRun_coreInvariant
                            correct.1 startEquation).1)
                        |>.activeReferenceGraph.Walk left right) ∧
                      path.start = left ∧
                        path.finish = right ∧
                          conclusion ∉ path.vertices ∧
                            path.traversed =
                                before ++ boundary :: after ∧
                              (∀ candidate ∈ before,
                                ((final.core.toMarking certificate
                                    (canonicalWorklistRun_coreInvariant
                                      correct.1 startEquation).1)
                                  |>.mark candidate.source).isSome = true ∧
                                  ((final.core.toMarking certificate
                                      (canonicalWorklistRun_coreInvariant
                                        correct.1 startEquation).1)
                                    |>.mark candidate.target).isSome = true) ∧
                                boundary ∈ path.traversed ∧
                              ((final.core.toMarking certificate
                                  (canonicalWorklistRun_coreInvariant
                                    correct.1 startEquation).1)
                                |>.activeReferenceGraph.Walk
                                  left boundary.source) ∧
                                final.core.tokenAt? boundary.source =
                                    some leftToken ∧
                                final.core.assignedToken?
                                    boundary.source ≠ none ∧
                                final.core.assignedToken?
                                    boundary.target = none ∧
                                  boundary.target ≠ left ∧
                                    boundary.target ≠ right ∧
                                      boundary.target ≠ conclusion ∧
                                        ((∃ (frontierIndex frontierLeft
                                                frontierRight
                                                frontierConclusion : Nat),
                                            certificate.links[frontierIndex]? =
                                                some (.par frontierLeft
                                                  frontierRight
                                                  frontierConclusion) ∧
                                              boundary.source =
                                                  frontierLeft ∧
                                                boundary.target =
                                                  frontierConclusion) ∨
                                          ∃ (frontierIndex frontierLeft
                                                frontierRight
                                                frontierConclusion : Nat),
                                            certificate.links[frontierIndex]? =
                                                some (.tensor frontierLeft
                                                  frontierRight
                                                  frontierConclusion) ∧
                                              (boundary.source =
                                                  frontierLeft ∨
                                                boundary.source =
                                                  frontierRight) ∧
                                                boundary.target =
                                                  frontierConclusion)
  intro incomplete
  rcases canonicalWorklistRun_incomplete_waitingPar
      correct startEquation incomplete with
    ⟨index, left, right, conclusion, leftToken, rightToken,
      linkLookup, conclusionUnmarked, leftMarked, rightMarked,
      different, registered, minimality, noActiveWalk⟩
  have linkMembership :
      Link.par left right conclusion ∈ certificate.links :=
    List.mem_of_getElem? linkLookup
  rcases
      correct.parPremises_referencePath_avoids_conclusion linkMembership with
    ⟨path, pathStarts, pathFinishes, conclusionAvoided⟩
  have coreInvariant :
      WorklistCoreInvariant certificate final := by
    simpa [final] using
      canonicalWorklistRun_coreInvariant correct.1 startEquation
  let marking :=
    final.core.toMarking certificate coreInvariant.1
  have noActivePath :
      ¬marking.activeReferenceGraph.Walk path.start path.finish := by
    intro walk
    apply noActiveWalk
    simpa [marking, pathStarts, pathFinishes] using walk
  rcases final.core.tokenAt?_some_witness leftMarked with
    ⟨leftRaw, leftRawMarked, leftRepresentative⟩
  rcases final.core.tokenAt?_some_witness rightMarked with
    ⟨rightRaw, rightRawMarked, _rightRepresentative⟩
  have abstractLeftMarked :
      (marking.mark left).isSome = true := by
    simp [marking, leftRawMarked]
  rcases marking.referencePath_has_first_marked_to_unmarked_boundary
      path
      (by simpa [pathStarts] using abstractLeftMarked)
      noActivePath with
    ⟨before, boundary, after, traversalEquation,
      prefixAccepted, boundarySourceMarked,
      boundaryTargetUnmarked, activePrefix⟩
  have boundaryMembership : boundary ∈ path.traversed := by
    rw [traversalEquation]
    simp
  have activeFromLeft :
      marking.activeReferenceGraph.Walk left boundary.source := by
    simpa [pathStarts] using activePrefix
  have boundarySourceAssigned :
      final.core.assignedToken? boundary.source ≠ none := by
    change
      ((final.core.toMarking certificate coreInvariant.1).mark
        boundary.source).isSome = true at boundarySourceMarked
    simp only [UnificationState.toMarking_mark] at boundarySourceMarked
    intro sourceUnassigned
    rw [sourceUnassigned] at boundarySourceMarked
    contradiction
  rcases final.core.tokenAt?_exists_of_assigned boundarySourceAssigned with
    ⟨boundarySourceToken, boundarySourceLookup⟩
  rcases final.core.tokenAt?_some_witness boundarySourceLookup with
    ⟨boundarySourceRaw, boundarySourceRawMarked,
      boundarySourceRepresentative⟩
  have exactComponents :
      marking.ThreadComponentsExact := by
    exact
      canonicalWorklistRun_threadComponentsExact
        correct.1 startEquation
  have abstractBoundarySourceMarked :
      marking.mark boundary.source = some boundarySourceRaw := by
    simpa [marking] using boundarySourceRawMarked
  have sameThread :
      marking.sameThread leftRaw boundarySourceRaw := by
    exact
      (exactComponents.walk_iff_sameThread
        marking
        (by simpa [marking] using leftRawMarked)
        abstractBoundarySourceMarked).mp activeFromLeft
  have boundarySourceTokenEquation :
      boundarySourceToken = leftToken := by
    simp only [marking, UnificationState.toMarking_sameThread] at sameThread
    rw [leftRepresentative, boundarySourceRepresentative] at sameThread
    exact sameThread.symm
  have boundarySourceTokenLookup :
      final.core.tokenAt? boundary.source = some leftToken := by
    rw [boundarySourceLookup, boundarySourceTokenEquation]
  have boundaryTargetAssignedNone :
      final.core.assignedToken? boundary.target = none := by
    change
      ((final.core.toMarking certificate coreInvariant.1).mark
        boundary.target).isSome = false at boundaryTargetUnmarked
    simp only [UnificationState.toMarking_mark] at boundaryTargetUnmarked
    cases assigned : final.core.assignedToken? boundary.target with
    | none =>
        rfl
    | some token =>
        simp [assigned] at boundaryTargetUnmarked
  have boundaryTargetMembership :
      boundary.target ∈ path.vertices :=
    (path.directed_endpoints_mem_vertices boundaryMembership).2
  have boundaryTargetNeLeft : boundary.target ≠ left := by
    intro same
    rw [same, leftRawMarked] at boundaryTargetAssignedNone
    contradiction
  have boundaryTargetNeRight : boundary.target ≠ right := by
    intro same
    rw [same, rightRawMarked] at boundaryTargetAssignedNone
    contradiction
  have boundaryTargetNeConclusion : boundary.target ≠ conclusion := by
    intro same
    exact conclusionAvoided (same ▸ boundaryTargetMembership)
  have causal :
      marking.MarkingCausallyClosed := by
    exact
      (canonicalWorklistRun_causallyThreaded
        correct.1 startEquation).1
  have axiomsMarked :
      ∀ {axiomIndex axiomLeft axiomRight : Nat},
        certificate.links[axiomIndex]? =
            some (Link.axiom axiomLeft axiomRight) →
          (marking.mark axiomLeft).isSome = true ∧
            (marking.mark axiomRight).isSome = true := by
    intro axiomIndex axiomLeft axiomRight axiomLookup
    have axiomMembership :
        Link.axiom axiomLeft axiomRight ∈ certificate.links :=
      List.mem_of_getElem? axiomLookup
    have assigned :=
      canonicalWorklistRun_axiom_endpoints_assigned
        correct.1 startEquation axiomMembership
    constructor
    · change
        (final.core.assignedToken? axiomLeft).isSome = true
      cases equation : final.core.assignedToken? axiomLeft with
      | none => exact False.elim (assigned.1 equation)
      | some token => rfl
    · change
        (final.core.assignedToken? axiomRight).isSome = true
      cases equation : final.core.assignedToken? axiomRight with
      | none => exact False.elim (assigned.2 equation)
      | some token => rfl
  have boundaryOrigin :=
    marking.marked_to_unmarked_referenceEdge_connective_origin
      causal axiomsMarked boundary boundarySourceMarked
      boundaryTargetUnmarked
  exact
    ⟨index, left, right, conclusion, leftToken, rightToken, path, boundary,
      before, after,
      linkLookup, conclusionUnmarked, leftMarked, rightMarked, different,
      registered, minimality, noActiveWalk, pathStarts, pathFinishes,
      conclusionAvoided, traversalEquation, prefixAccepted,
      boundaryMembership, activeFromLeft,
      boundarySourceTokenLookup, boundarySourceAssigned,
      boundaryTargetAssignedNone, boundaryTargetNeLeft,
      boundaryTargetNeRight, boundaryTargetNeConclusion, boundaryOrigin⟩

/-- The first and last inactive frontiers bracket one exact path
decomposition.  This statement does not claim that every vertex in the
intervening middle list is unmarked.  The left frontier source carries the
waiting par's left token; the right frontier target carries its right token.
Both frontier orientations are classified occurrence-exactly by submitted
connective links. -/
private theorem canonicalWorklistRun_incomplete_twoSidedPathRegion
    {certificate : Certificate} {started : UnificationState}
    (correct : certificate.DeclarativelyCorrect)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    final.core.allMarked = false →
      ∃ (left right leftToken rightToken : Nat)
          (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (leftBoundary rightBoundary :
            certificate.referenceSwitchingGraph.DirectedEdge)
          (before middle after :
            List certificate.referenceSwitchingGraph.DirectedEdge),
        path.start = left ∧
          path.finish = right ∧
            path.traversed =
              before ++
                leftBoundary :: (middle ++ rightBoundary :: after) ∧
              ((final.core.toMarking certificate
                  (canonicalWorklistRun_coreInvariant
                    correct.1 startEquation).1)
                |>.activeReferenceGraph.Walk
                  left leftBoundary.source) ∧
                final.core.tokenAt? leftBoundary.source =
                    some leftToken ∧
                  final.core.assignedToken?
                      leftBoundary.target = none ∧
                    final.core.assignedToken?
                        rightBoundary.source = none ∧
                      final.core.tokenAt? rightBoundary.target =
                          some rightToken ∧
                        ((final.core.toMarking certificate
                            (canonicalWorklistRun_coreInvariant
                              correct.1 startEquation).1)
                          |>.activeReferenceGraph.Walk
                            rightBoundary.target right) ∧
                          leftToken ≠ rightToken ∧
                            leftBoundary ≠ rightBoundary ∧
                              ForwardReferenceConnectiveOccurrence
                                certificate leftBoundary ∧
                                ForwardReferenceConnectiveOccurrence
                                  certificate rightBoundary.reverse := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  change
    final.core.allMarked = false →
      ∃ (left right leftToken rightToken : Nat)
          (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (leftBoundary rightBoundary :
            certificate.referenceSwitchingGraph.DirectedEdge)
          (before middle after :
            List certificate.referenceSwitchingGraph.DirectedEdge),
        path.start = left ∧
          path.finish = right ∧
            path.traversed =
              before ++
                leftBoundary :: (middle ++ rightBoundary :: after) ∧
              ((final.core.toMarking certificate
                  (canonicalWorklistRun_coreInvariant
                    correct.1 startEquation).1)
                |>.activeReferenceGraph.Walk
                  left leftBoundary.source) ∧
                final.core.tokenAt? leftBoundary.source =
                    some leftToken ∧
                  final.core.assignedToken?
                      leftBoundary.target = none ∧
                    final.core.assignedToken?
                        rightBoundary.source = none ∧
                      final.core.tokenAt? rightBoundary.target =
                          some rightToken ∧
                        ((final.core.toMarking certificate
                            (canonicalWorklistRun_coreInvariant
                              correct.1 startEquation).1)
                          |>.activeReferenceGraph.Walk
                            rightBoundary.target right) ∧
                          leftToken ≠ rightToken ∧
                            leftBoundary ≠ rightBoundary ∧
                              ForwardReferenceConnectiveOccurrence
                                certificate leftBoundary ∧
                                ForwardReferenceConnectiveOccurrence
                                  certificate rightBoundary.reverse
  intro incomplete
  rcases canonicalWorklistRun_incomplete_waitingParPath
      correct startEquation incomplete with
    ⟨_index, left, right, _conclusion, leftToken, rightToken,
      path, leftBoundary, leftBefore, leftAfter, _waitingLookup,
      _waitingConclusionUnmarked, leftMarked, rightMarked, different,
      _registered, _minimality, noActiveWalk, pathStarts, pathFinishes,
      _conclusionAvoided, leftTraversalEquation, leftPrefixMarked,
      _leftBoundaryMembership, activeFromLeft, leftBoundaryToken,
      leftBoundarySourceAssigned, leftBoundaryTargetUnmarked,
      _leftBoundaryTargetNeLeft, _leftBoundaryTargetNeRight,
      _leftBoundaryTargetNeConclusion, leftBoundaryOrigin⟩
  have coreInvariant :
      WorklistCoreInvariant certificate final := by
    simpa [final] using
      canonicalWorklistRun_coreInvariant correct.1 startEquation
  let marking :=
    final.core.toMarking certificate coreInvariant.1
  have noActivePath :
      ¬marking.activeReferenceGraph.Walk path.start path.finish := by
    intro walk
    apply noActiveWalk
    simpa [marking, pathStarts, pathFinishes] using walk
  rcases final.core.tokenAt?_some_witness rightMarked with
    ⟨rightRaw, rightRawMarked, rightRepresentative⟩
  have abstractRightMarked :
      (marking.mark path.finish).isSome = true := by
    simp [marking, pathFinishes, rightRawMarked]
  rcases marking.referencePath_has_last_unmarked_to_marked_boundary
      path abstractRightMarked noActivePath with
    ⟨rightBefore, rightBoundary, rightAfter,
      rightTraversalEquation, rightBoundarySourceUnmarked,
      rightBoundaryTargetMarked, activeToRight⟩
  have rightBoundaryMembership :
      rightBoundary ∈ path.traversed := by
    rw [rightTraversalEquation]
    simp
  have rightBoundarySourceAssignedNone :
      final.core.assignedToken? rightBoundary.source = none := by
    change
      ((final.core.toMarking certificate coreInvariant.1).mark
        rightBoundary.source).isSome = false at rightBoundarySourceUnmarked
    simp only [UnificationState.toMarking_mark] at rightBoundarySourceUnmarked
    cases assigned : final.core.assignedToken? rightBoundary.source with
    | none => rfl
    | some token =>
        simp [assigned] at rightBoundarySourceUnmarked
  have rightBoundaryTargetAssigned :
      final.core.assignedToken? rightBoundary.target ≠ none := by
    change
      ((final.core.toMarking certificate coreInvariant.1).mark
        rightBoundary.target).isSome = true at rightBoundaryTargetMarked
    simp only [UnificationState.toMarking_mark] at rightBoundaryTargetMarked
    intro targetUnassigned
    rw [targetUnassigned] at rightBoundaryTargetMarked
    contradiction
  rcases final.core.tokenAt?_exists_of_assigned
      rightBoundaryTargetAssigned with
    ⟨rightBoundaryToken, rightBoundaryTokenLookup⟩
  rcases final.core.tokenAt?_some_witness rightBoundaryTokenLookup with
    ⟨rightBoundaryRaw, rightBoundaryRawMarked,
      rightBoundaryRepresentative⟩
  have exactComponents :
      marking.ThreadComponentsExact :=
    canonicalWorklistRun_threadComponentsExact
      correct.1 startEquation
  have abstractRightBoundaryMarked :
      marking.mark rightBoundary.target = some rightBoundaryRaw := by
    simpa [marking] using rightBoundaryRawMarked
  have rightThread :
      marking.sameThread rightBoundaryRaw rightRaw := by
    exact
      (exactComponents.walk_iff_sameThread
        marking abstractRightBoundaryMarked
        (by simpa [marking] using rightRawMarked)).mp
          (by simpa [pathFinishes] using activeToRight)
  have rightBoundaryTokenEquation :
      rightBoundaryToken = rightToken := by
    simp only [marking, UnificationState.toMarking_sameThread] at rightThread
    rw [rightBoundaryRepresentative, rightRepresentative] at rightThread
    exact rightThread
  have rightBoundaryTargetToken :
      final.core.tokenAt? rightBoundary.target = some rightToken := by
    rw [rightBoundaryTokenLookup, rightBoundaryTokenEquation]
  have rightBoundaryInLeftAfter :
      rightBoundary ∈ leftAfter := by
    have decomposedMembership :
        rightBoundary ∈
          leftBefore ++ leftBoundary :: leftAfter := by
      simpa [leftTraversalEquation] using rightBoundaryMembership
    simp only [List.mem_append, List.mem_cons] at decomposedMembership
    rcases decomposedMembership with
      inLeftPrefix | atLeftBoundary | inLeftAfter
    · have sourceMarked :=
        (leftPrefixMarked rightBoundary inLeftPrefix).1
      rw [sourceMarked] at rightBoundarySourceUnmarked
      contradiction
    · subst rightBoundary
      exact False.elim
        (leftBoundarySourceAssigned rightBoundarySourceAssignedNone)
    · exact inLeftAfter
  rcases List.mem_iff_append.mp rightBoundaryInLeftAfter with
    ⟨middle, after, leftAfterEquation⟩
  have twoSidedTraversal :
      path.traversed =
        leftBefore ++
          leftBoundary :: (middle ++ rightBoundary :: after) := by
    rw [leftTraversalEquation, leftAfterEquation]
  have activeFromRight :
      marking.activeReferenceGraph.Walk rightBoundary.target right := by
    simpa [pathFinishes] using activeToRight
  have boundariesDifferent : leftBoundary ≠ rightBoundary := by
    intro same
    apply leftBoundarySourceAssigned
    rw [same]
    exact rightBoundarySourceAssignedNone
  have causal :
      marking.MarkingCausallyClosed :=
    (canonicalWorklistRun_causallyThreaded
      correct.1 startEquation).1
  have axiomsMarked :
      ∀ {axiomIndex axiomLeft axiomRight : Nat},
        certificate.links[axiomIndex]? =
            some (Link.axiom axiomLeft axiomRight) →
          (marking.mark axiomLeft).isSome = true ∧
            (marking.mark axiomRight).isSome = true := by
    intro axiomIndex axiomLeft axiomRight axiomLookup
    have axiomMembership :
        Link.axiom axiomLeft axiomRight ∈ certificate.links :=
      List.mem_of_getElem? axiomLookup
    have assigned :=
      canonicalWorklistRun_axiom_endpoints_assigned
        correct.1 startEquation axiomMembership
    constructor
    · change (final.core.assignedToken? axiomLeft).isSome = true
      cases equation : final.core.assignedToken? axiomLeft with
      | none => exact False.elim (assigned.1 equation)
      | some token => rfl
    · change (final.core.assignedToken? axiomRight).isSome = true
      cases equation : final.core.assignedToken? axiomRight with
      | none => exact False.elim (assigned.2 equation)
      | some token => rfl
  have rightBoundaryOrigin :=
    marking.marked_to_unmarked_referenceEdge_connective_origin
      causal axiomsMarked rightBoundary.reverse
      (by simpa using rightBoundaryTargetMarked)
      (by simpa using rightBoundarySourceUnmarked)
  exact
    ⟨left, right, leftToken, rightToken, path, leftBoundary, rightBoundary,
      leftBefore, middle, after, pathStarts, pathFinishes,
      twoSidedTraversal, activeFromLeft, leftBoundaryToken,
      leftBoundaryTargetUnmarked, rightBoundarySourceAssignedNone,
      rightBoundaryTargetToken, activeFromRight, different,
      boundariesDifferent,
      by simpa [ForwardReferenceConnectiveOccurrence] using
        leftBoundaryOrigin,
      by simpa [ForwardReferenceConnectiveOccurrence] using
        rightBoundaryOrigin⟩

/-- Both inactive frontiers of the exact path decomposition satisfy the local
quiescent scheduler classification, with the right side viewed in its
retained forward connective orientation. -/
private theorem canonicalWorklistRun_incomplete_twoSidedSchedulerRegion
    {certificate : Certificate} {started : UnificationState}
    (correct : certificate.DeclarativelyCorrect)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    final.core.allMarked = false →
      ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (leftBoundary rightBoundary :
            certificate.referenceSwitchingGraph.DirectedEdge)
          (before middle after :
            List certificate.referenceSwitchingGraph.DirectedEdge),
        path.traversed =
            before ++
              leftBoundary :: (middle ++ rightBoundary :: after) ∧
          leftBoundary ≠ rightBoundary ∧
            final.core.assignedToken? leftBoundary.target = none ∧
              final.core.assignedToken? rightBoundary.source = none ∧
                PathFrontierSchedulerObstruction
                    certificate final leftBoundary ∧
                  PathFrontierSchedulerObstruction
                    certificate final rightBoundary.reverse := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  change
    final.core.allMarked = false →
      ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (leftBoundary rightBoundary :
            certificate.referenceSwitchingGraph.DirectedEdge)
          (before middle after :
            List certificate.referenceSwitchingGraph.DirectedEdge),
        path.traversed =
            before ++
              leftBoundary :: (middle ++ rightBoundary :: after) ∧
          leftBoundary ≠ rightBoundary ∧
            final.core.assignedToken? leftBoundary.target = none ∧
              final.core.assignedToken? rightBoundary.source = none ∧
                PathFrontierSchedulerObstruction
                    certificate final leftBoundary ∧
                  PathFrontierSchedulerObstruction
                    certificate final rightBoundary.reverse
  intro incomplete
  rcases canonicalWorklistRun_incomplete_twoSidedPathRegion
      correct startEquation incomplete with
    ⟨_left, _right, _leftToken, _rightToken, path,
      leftBoundary, rightBoundary, before, middle, after,
      _pathStarts, _pathFinishes, traversalEquation,
      _activeFromLeft, leftBoundaryToken, leftBoundaryTargetUnmarked,
      rightBoundarySourceUnmarked, rightBoundaryToken, _activeFromRight,
      _tokensDifferent, boundariesDifferent,
      leftBoundaryOrigin, rightBoundaryOrigin⟩
  rcases final.core.tokenAt?_some_witness leftBoundaryToken with
    ⟨leftRaw, leftRawMarked, _leftRepresentative⟩
  have leftBoundarySourceAssigned :
      final.core.assignedToken? leftBoundary.source ≠ none := by
    rw [leftRawMarked]
    simp
  rcases final.core.tokenAt?_some_witness rightBoundaryToken with
    ⟨rightRaw, rightRawMarked, _rightRepresentative⟩
  have rightBoundaryTargetAssigned :
      final.core.assignedToken? rightBoundary.reverse.source ≠ none := by
    simpa using (show
      final.core.assignedToken? rightBoundary.target ≠ none by
        rw [rightRawMarked]
        simp)
  have rightBoundaryReverseTargetUnmarked :
      final.core.assignedToken? rightBoundary.reverse.target = none := by
    simpa using rightBoundarySourceUnmarked
  have leftStatus :=
    canonicalWorklistRun_forwardFrontier_status
      correct startEquation leftBoundarySourceAssigned
      leftBoundaryTargetUnmarked leftBoundaryOrigin
  have rightStatus :=
    canonicalWorklistRun_forwardFrontier_status
      correct startEquation rightBoundaryTargetAssigned
      rightBoundaryReverseTargetUnmarked rightBoundaryOrigin
  exact
    ⟨path, leftBoundary, rightBoundary, before, middle, after,
      traversalEquation, boundariesDifferent,
      leftBoundaryTargetUnmarked, rightBoundarySourceUnmarked,
      leftStatus, rightStatus⟩

/-- Cut the bracket at the first return from the unmarked region to a marked
vertex.  Unlike the coarser two-sided bracket, every occurrence strictly
between the returned boundaries has unmarked endpoints. -/
private theorem canonicalWorklistRun_incomplete_firstInactiveBlock
    {certificate : Certificate} {started : UnificationState}
    (correct : certificate.DeclarativelyCorrect)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    final.core.allMarked = false →
      ∃ (waitingConclusion : Vertex)
          (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (leftBoundary reentry :
            certificate.referenceSwitchingGraph.DirectedEdge)
          (before inactive after :
            List certificate.referenceSwitchingGraph.DirectedEdge),
        final.core.assignedToken? waitingConclusion = none ∧
          (∀ {candidate : Vertex},
            candidate < certificate.formulas.size →
              final.core.assignedToken? candidate = none →
                certificate.formulaComplexityAt waitingConclusion ≤
                  certificate.formulaComplexityAt candidate) ∧
          path.traversed =
              before ++
                leftBoundary :: (inactive ++ reentry :: after) ∧
            leftBoundary ≠ reentry ∧
              final.core.assignedToken? leftBoundary.target = none ∧
              (∀ candidate ∈ inactive,
                final.core.assignedToken? candidate.source = none ∧
                  final.core.assignedToken? candidate.target = none) ∧
                final.core.assignedToken? reentry.source = none ∧
                  final.core.assignedToken? reentry.target ≠ none ∧
                    PathFrontierSchedulerObstruction
                        certificate final leftBoundary ∧
                      PathFrontierSchedulerObstruction
                        certificate final reentry.reverse := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  change
    final.core.allMarked = false →
      ∃ (waitingConclusion : Vertex)
          (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (leftBoundary reentry :
            certificate.referenceSwitchingGraph.DirectedEdge)
          (before inactive after :
            List certificate.referenceSwitchingGraph.DirectedEdge),
        final.core.assignedToken? waitingConclusion = none ∧
          (∀ {candidate : Vertex},
            candidate < certificate.formulas.size →
              final.core.assignedToken? candidate = none →
                certificate.formulaComplexityAt waitingConclusion ≤
                  certificate.formulaComplexityAt candidate) ∧
          path.traversed =
              before ++
                leftBoundary :: (inactive ++ reentry :: after) ∧
            leftBoundary ≠ reentry ∧
              final.core.assignedToken? leftBoundary.target = none ∧
              (∀ candidate ∈ inactive,
                final.core.assignedToken? candidate.source = none ∧
                  final.core.assignedToken? candidate.target = none) ∧
                final.core.assignedToken? reentry.source = none ∧
                  final.core.assignedToken? reentry.target ≠ none ∧
                    PathFrontierSchedulerObstruction
                        certificate final leftBoundary ∧
                      PathFrontierSchedulerObstruction
                        certificate final reentry.reverse
  intro incomplete
  rcases canonicalWorklistRun_incomplete_waitingParPath
      correct startEquation incomplete with
    ⟨_index, left, right, waitingConclusion, _leftToken, _rightToken,
      path, leftBoundary, leftBefore, leftAfter, _waitingLookup,
      waitingConclusionUnmarked, _leftMarked, rightMarked, _different,
      _registered, minimality, _noActiveWalk, pathStarts, pathFinishes,
      _conclusionAvoided, leftTraversalEquation, _leftPrefixMarked,
      _leftBoundaryMembership, _activeFromLeft, _leftBoundaryToken,
      leftBoundarySourceAssigned, leftBoundaryTargetUnmarked,
      _leftBoundaryTargetNeLeft, _leftBoundaryTargetNeRight,
      _leftBoundaryTargetNeConclusion, leftBoundaryOrigin⟩
  have coreInvariant :
      WorklistCoreInvariant certificate final := by
    simpa [final] using
      canonicalWorklistRun_coreInvariant correct.1 startEquation
  let marking :=
    final.core.toMarking certificate coreInvariant.1
  rcases path.suffixAfter leftTraversalEquation with
    ⟨suffix, suffixStarts, suffixFinishes, suffixSteps, _suffixSubset⟩
  have suffixStartUnmarked :
      (marking.mark suffix.start).isSome = false := by
    change (final.core.assignedToken? suffix.start).isSome = false
    rw [suffixStarts, leftBoundaryTargetUnmarked]
    rfl
  rcases final.core.tokenAt?_some_witness rightMarked with
    ⟨rightRaw, rightRawMarked, _rightRepresentative⟩
  have suffixFinishMarked :
      (marking.mark suffix.finish).isSome = true := by
    simp [marking, suffixFinishes, pathFinishes, rightRawMarked]
  rcases marking.referencePath_has_first_unmarked_to_marked_boundary
      suffix suffixStartUnmarked suffixFinishMarked with
    ⟨inactive, reentry, after, suffixTraversalEquation,
      inactiveUnmarked, reentrySourceUnmarked,
      reentryTargetMarked⟩
  have leftAfterEquation :
      leftAfter = inactive ++ reentry :: after :=
    suffixSteps.symm.trans suffixTraversalEquation
  have traversalEquation :
      path.traversed =
        leftBefore ++
          leftBoundary :: (inactive ++ reentry :: after) := by
    rw [leftTraversalEquation, leftAfterEquation]
  have assignedNoneOfUnmarked :
      ∀ {vertex : Vertex},
        (marking.mark vertex).isSome = false →
          final.core.assignedToken? vertex = none := by
    intro vertex unmarked
    change
      (final.core.assignedToken? vertex).isSome = false at unmarked
    cases equation : final.core.assignedToken? vertex with
    | none => rfl
    | some token =>
        simp [equation] at unmarked
  have inactiveAssignedNone :
      ∀ candidate ∈ inactive,
        final.core.assignedToken? candidate.source = none ∧
          final.core.assignedToken? candidate.target = none := by
    intro candidate membership
    rcases inactiveUnmarked candidate membership with
      ⟨sourceUnmarked, targetUnmarked⟩
    exact
      ⟨assignedNoneOfUnmarked sourceUnmarked,
        assignedNoneOfUnmarked targetUnmarked⟩
  have reentrySourceAssignedNone :
      final.core.assignedToken? reentry.source = none :=
    assignedNoneOfUnmarked reentrySourceUnmarked
  have reentryTargetAssigned :
      final.core.assignedToken? reentry.target ≠ none := by
    intro targetUnassigned
    change
      (final.core.assignedToken? reentry.target).isSome = true
        at reentryTargetMarked
    rw [targetUnassigned] at reentryTargetMarked
    contradiction
  have boundariesDifferent : leftBoundary ≠ reentry := by
    intro same
    apply reentryTargetAssigned
    rw [← same]
    exact leftBoundaryTargetUnmarked
  have causal :
      marking.MarkingCausallyClosed :=
    (canonicalWorklistRun_causallyThreaded
      correct.1 startEquation).1
  have axiomsMarked :
      ∀ {axiomIndex axiomLeft axiomRight : Nat},
        certificate.links[axiomIndex]? =
            some (Link.axiom axiomLeft axiomRight) →
          (marking.mark axiomLeft).isSome = true ∧
            (marking.mark axiomRight).isSome = true := by
    intro axiomIndex axiomLeft axiomRight axiomLookup
    have axiomMembership :
        Link.axiom axiomLeft axiomRight ∈ certificate.links :=
      List.mem_of_getElem? axiomLookup
    have assigned :=
      canonicalWorklistRun_axiom_endpoints_assigned
        correct.1 startEquation axiomMembership
    constructor
    · change (final.core.assignedToken? axiomLeft).isSome = true
      cases equation : final.core.assignedToken? axiomLeft with
      | none => exact False.elim (assigned.1 equation)
      | some token => rfl
    · change (final.core.assignedToken? axiomRight).isSome = true
      cases equation : final.core.assignedToken? axiomRight with
      | none => exact False.elim (assigned.2 equation)
      | some token => rfl
  have reentryOrigin :
      ForwardReferenceConnectiveOccurrence certificate reentry.reverse := by
    have origin :=
      marking.marked_to_unmarked_referenceEdge_connective_origin
        causal axiomsMarked reentry.reverse
        (by simpa using reentryTargetMarked)
        (by simpa using reentrySourceUnmarked)
    simpa [ForwardReferenceConnectiveOccurrence] using origin
  have leftStatus :=
    canonicalWorklistRun_forwardFrontier_status
      correct startEquation leftBoundarySourceAssigned
      leftBoundaryTargetUnmarked
      (by simpa [ForwardReferenceConnectiveOccurrence] using
        leftBoundaryOrigin)
  have reentryStatus :=
    canonicalWorklistRun_forwardFrontier_status
      (boundary := reentry.reverse)
      correct startEquation (by simpa using reentryTargetAssigned)
      (by simpa using reentrySourceAssignedNone)
      reentryOrigin
  exact
    ⟨waitingConclusion, path, leftBoundary, reentry, leftBefore, inactive,
      after, waitingConclusionUnmarked, minimality, traversalEquation,
      boundariesDifferent,
      leftBoundaryTargetUnmarked, inactiveAssignedNone,
      reentrySourceAssignedNone, reentryTargetAssigned,
      leftStatus, reentryStatus⟩

/-- Relative to a globally minimum-complexity unassigned occurrence, a
frontier chase either rises strictly above that minimum or stops at a
concrete distinct-thread waiting par. -/
private def PathFrontierAboveMinimumOrWaitingPar
    (certificate : Certificate)
    (state : UnificationWorklistState)
    (minimum : Vertex)
    (boundary : certificate.referenceSwitchingGraph.DirectedEdge) : Prop :=
  certificate.formulaComplexityAt minimum <
      certificate.formulaComplexityAt boundary.target ∨
    ∃ (index left right conclusion leftToken rightToken : Nat),
      certificate.links[index]? =
          some (.par left right conclusion) ∧
        boundary.source = left ∧
          boundary.target = conclusion ∧
            state.core.tokenAt? left = some leftToken ∧
              state.core.tokenAt? right = some rightToken ∧
                leftToken ≠ rightToken ∧
                  index ∈ state.waiting

/-- Global minimality normalizes a raw strict-premise descent into a strict
rank gap from the selected minimum obstruction. -/
private theorem
    pathFrontierDescentOrWaitingPar_aboveMinimum_or_waitingPar
    {certificate : Certificate}
    {state : UnificationWorklistState}
    {minimum : Vertex}
    {boundary : certificate.referenceSwitchingGraph.DirectedEdge}
    (minimality :
      ∀ {candidate : Vertex},
        candidate < certificate.formulas.size →
          state.core.assignedToken? candidate = none →
            certificate.formulaComplexityAt minimum ≤
              certificate.formulaComplexityAt candidate)
    (alternative :
      PathFrontierDescentOrWaitingPar certificate state boundary) :
    PathFrontierAboveMinimumOrWaitingPar
      certificate state minimum boundary := by
  rcases alternative with descent | waiting
  · rcases descent with
      ⟨blockedPremise, blockedBound, blockedUnassigned, strictDescent⟩
    exact .inl
      (Nat.lt_of_le_of_lt
        (minimality blockedBound blockedUnassigned)
        strictDescent)
  · exact .inr waiting

/-- The first contiguous inactive block exposes the rank-normalized chase
alternative at both orientations: each boundary is strictly above the global
minimum obstruction or is a concrete distinct-thread waiting par. -/
private theorem
    canonicalWorklistRun_incomplete_firstInactiveBlock_aboveMinimumOrWaiting
    {certificate : Certificate} {started : UnificationState}
    (correct : certificate.DeclarativelyCorrect)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    final.core.allMarked = false →
      ∃ (waitingConclusion : Vertex)
          (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (leftBoundary reentry :
            certificate.referenceSwitchingGraph.DirectedEdge)
          (before inactive after :
            List certificate.referenceSwitchingGraph.DirectedEdge),
        final.core.assignedToken? waitingConclusion = none ∧
          (∀ {candidate : Vertex},
            candidate < certificate.formulas.size →
              final.core.assignedToken? candidate = none →
                certificate.formulaComplexityAt waitingConclusion ≤
                  certificate.formulaComplexityAt candidate) ∧
          path.traversed =
              before ++
                leftBoundary :: (inactive ++ reentry :: after) ∧
            leftBoundary ≠ reentry ∧
              final.core.assignedToken? leftBoundary.target = none ∧
                (∀ candidate ∈ inactive,
                  final.core.assignedToken? candidate.source = none ∧
                    final.core.assignedToken? candidate.target = none) ∧
                  final.core.assignedToken? reentry.source = none ∧
                    final.core.assignedToken? reentry.target ≠ none ∧
                      PathFrontierAboveMinimumOrWaitingPar
                          certificate final waitingConclusion leftBoundary ∧
                        PathFrontierAboveMinimumOrWaitingPar
                          certificate final waitingConclusion
                          reentry.reverse := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  change
    final.core.allMarked = false →
      ∃ (waitingConclusion : Vertex)
          (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (leftBoundary reentry :
            certificate.referenceSwitchingGraph.DirectedEdge)
          (before inactive after :
            List certificate.referenceSwitchingGraph.DirectedEdge),
        final.core.assignedToken? waitingConclusion = none ∧
          (∀ {candidate : Vertex},
            candidate < certificate.formulas.size →
              final.core.assignedToken? candidate = none →
                certificate.formulaComplexityAt waitingConclusion ≤
                  certificate.formulaComplexityAt candidate) ∧
          path.traversed =
              before ++
                leftBoundary :: (inactive ++ reentry :: after) ∧
            leftBoundary ≠ reentry ∧
              final.core.assignedToken? leftBoundary.target = none ∧
                (∀ candidate ∈ inactive,
                  final.core.assignedToken? candidate.source = none ∧
                    final.core.assignedToken? candidate.target = none) ∧
                  final.core.assignedToken? reentry.source = none ∧
                    final.core.assignedToken? reentry.target ≠ none ∧
                      PathFrontierAboveMinimumOrWaitingPar
                          certificate final waitingConclusion leftBoundary ∧
                        PathFrontierAboveMinimumOrWaitingPar
                          certificate final waitingConclusion
                          reentry.reverse
  intro incomplete
  rcases canonicalWorklistRun_incomplete_firstInactiveBlock
      correct startEquation incomplete with
    ⟨waitingConclusion, path, leftBoundary, reentry,
      before, inactive, after, waitingConclusionUnmarked,
      minimality, traversalEquation, boundariesDifferent,
      leftBoundaryTargetUnmarked, inactiveAssignedNone,
      reentrySourceUnmarked, reentryTargetMarked,
      leftStatus, reentryStatus⟩
  have leftRawAlternative :=
    pathFrontierSchedulerObstruction_descent_or_waitingPar
      correct.1 leftStatus
  have reentryRawAlternative :=
    pathFrontierSchedulerObstruction_descent_or_waitingPar
      correct.1 reentryStatus
  have leftAlternative :=
    pathFrontierDescentOrWaitingPar_aboveMinimum_or_waitingPar
      minimality leftRawAlternative
  have reentryAlternative :=
    pathFrontierDescentOrWaitingPar_aboveMinimum_or_waitingPar
      minimality reentryRawAlternative
  exact
    ⟨waitingConclusion, path, leftBoundary, reentry,
      before, inactive, after, waitingConclusionUnmarked,
      minimality, traversalEquation, boundariesDifferent,
      leftBoundaryTargetUnmarked, inactiveAssignedNone,
      reentrySourceUnmarked, reentryTargetMarked,
      leftAlternative, reentryAlternative⟩

/-- Both orientations bracketing the first contiguous inactive block have
well-founded chase endpoints.  Each reaches a concrete registered waiting par
without increasing formula complexity, while the exact inactive path
decomposition is retained for the final global exclusion argument. -/
private theorem
    canonicalWorklistRun_incomplete_firstInactiveBlock_reachesWaitingPars
    {certificate : Certificate} {started : UnificationState}
    (correct : certificate.DeclarativelyCorrect)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    final.core.allMarked = false →
      ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (leftBoundary reentry :
            certificate.referenceSwitchingGraph.DirectedEdge)
          (before inactive after :
            List certificate.referenceSwitchingGraph.DirectedEdge)
          (leftWaiting rightWaiting : Vertex),
        path.traversed =
            before ++
              leftBoundary :: (inactive ++ reentry :: after) ∧
          leftBoundary ≠ reentry ∧
            final.core.assignedToken? leftBoundary.target = none ∧
              (∀ candidate ∈ inactive,
                final.core.assignedToken? candidate.source = none ∧
                  final.core.assignedToken? candidate.target = none) ∧
                final.core.assignedToken? reentry.source = none ∧
                  final.core.assignedToken? reentry.target ≠ none ∧
                    QuiescentWaitingParAt
                        certificate final leftWaiting ∧
                      certificate.formulaComplexityAt leftWaiting ≤
                        certificate.formulaComplexityAt
                          leftBoundary.target ∧
                        QuiescentWaitingParAt
                            certificate final rightWaiting ∧
                          certificate.formulaComplexityAt rightWaiting ≤
                            certificate.formulaComplexityAt
                              reentry.source := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  change
    final.core.allMarked = false →
      ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (leftBoundary reentry :
            certificate.referenceSwitchingGraph.DirectedEdge)
          (before inactive after :
            List certificate.referenceSwitchingGraph.DirectedEdge)
          (leftWaiting rightWaiting : Vertex),
        path.traversed =
            before ++
              leftBoundary :: (inactive ++ reentry :: after) ∧
          leftBoundary ≠ reentry ∧
            final.core.assignedToken? leftBoundary.target = none ∧
              (∀ candidate ∈ inactive,
                final.core.assignedToken? candidate.source = none ∧
                  final.core.assignedToken? candidate.target = none) ∧
                final.core.assignedToken? reentry.source = none ∧
                  final.core.assignedToken? reentry.target ≠ none ∧
                    QuiescentWaitingParAt
                        certificate final leftWaiting ∧
                      certificate.formulaComplexityAt leftWaiting ≤
                        certificate.formulaComplexityAt
                          leftBoundary.target ∧
                        QuiescentWaitingParAt
                            certificate final rightWaiting ∧
                          certificate.formulaComplexityAt rightWaiting ≤
                            certificate.formulaComplexityAt
                              reentry.source
  intro incomplete
  rcases canonicalWorklistRun_incomplete_firstInactiveBlock
      correct startEquation incomplete with
    ⟨_minimum, path, leftBoundary, reentry,
      before, inactive, after, _minimumUnassigned,
      _minimality, traversalEquation, boundariesDifferent,
      leftBoundaryTargetUnassigned, inactiveUnassigned,
      reentrySourceUnassigned, reentryTargetAssigned,
      leftStatus, reentryStatus⟩
  rcases canonicalWorklistRun_pathFrontier_reaches_waitingPar
      correct startEquation leftBoundaryTargetUnassigned leftStatus with
    ⟨leftWaiting, leftReached, leftRank⟩
  have reverseTargetUnassigned :
      final.core.assignedToken? reentry.reverse.target = none := by
    simpa using reentrySourceUnassigned
  rcases canonicalWorklistRun_pathFrontier_reaches_waitingPar
      correct startEquation reverseTargetUnassigned reentryStatus with
    ⟨rightWaiting, rightReached, rightRank⟩
  have rightRankAtSource :
      certificate.formulaComplexityAt rightWaiting ≤
        certificate.formulaComplexityAt reentry.source := by
    simpa using rightRank
  exact
    ⟨path, leftBoundary, reentry, before, inactive, after,
      leftWaiting, rightWaiting, traversalEquation,
      boundariesDifferent, leftBoundaryTargetUnassigned,
      inactiveUnassigned, reentrySourceUnassigned,
      reentryTargetAssigned, leftReached, leftRank,
      rightReached, rightRankAtSource⟩

/-- Every incomplete correct canonical run now exposes a path occurrence
with a complete local scheduler classification.  This checkpoint separates
the remaining global geometric exclusion from queue bookkeeping: the path
frontier is either a registered/distinct-thread par, a par with its omitted
premise unassigned, or a tensor with its opposite premise unassigned. -/
private theorem canonicalWorklistRun_incomplete_pathFrontierStatus
    {certificate : Certificate} {started : UnificationState}
    (correct : certificate.DeclarativelyCorrect)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    final.core.allMarked = false →
      ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (boundary :
            certificate.referenceSwitchingGraph.DirectedEdge),
        boundary ∈ path.traversed ∧
          final.core.assignedToken? boundary.source ≠ none ∧
            final.core.assignedToken? boundary.target = none ∧
              PathFrontierSchedulerObstruction
                certificate final boundary := by
  let final :=
    (runUnificationWorklist certificate
      certificate.worklistConsumers
      (worklistFuel certificate.links.length)
      (initializeWorklist certificate started)).state
  change
    final.core.allMarked = false →
      ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (boundary :
            certificate.referenceSwitchingGraph.DirectedEdge),
        boundary ∈ path.traversed ∧
          final.core.assignedToken? boundary.source ≠ none ∧
            final.core.assignedToken? boundary.target = none ∧
              PathFrontierSchedulerObstruction
                certificate final boundary
  intro incomplete
  rcases canonicalWorklistRun_incomplete_waitingParPath
      correct startEquation incomplete with
    ⟨index, left, right, conclusion, leftToken, rightToken,
      path, boundary, _before, _after, waitingLookup,
      waitingConclusionUnmarked,
      leftMarked, rightMarked, different, registered, _minimality,
      noActiveWalk,
      pathStarts, pathFinishes, conclusionAvoided, _traversalEquation,
      _prefixAccepted, boundaryMembership,
      _activeFromLeft, _boundarySourceToken, boundarySourceAssigned,
      boundaryTargetUnmarked, boundaryTargetNeLeft,
      boundaryTargetNeRight, boundaryTargetNeConclusion,
      parOrigin | tensorOrigin⟩
  · rcases parOrigin with
      ⟨frontierIndex, frontierLeft, frontierRight,
        frontierConclusion, frontierLookup, sourceEquation,
        targetEquation⟩
    have frontierConclusionUnmarked :
        final.core.assignedToken? frontierConclusion = none := by
      simpa [targetEquation] using boundaryTargetUnmarked
    have frontierLeftAssigned :
        final.core.assignedToken? frontierLeft ≠ none := by
      simpa [sourceEquation] using boundarySourceAssigned
    have frontierStatus :=
      canonicalWorklistRun_par_frontier_status
        correct startEquation frontierLookup frontierConclusionUnmarked
        frontierLeftAssigned
    exact
      ⟨path, boundary, boundaryMembership, boundarySourceAssigned,
        boundaryTargetUnmarked, Or.inl
          ⟨frontierIndex, frontierLeft, frontierRight,
            frontierConclusion, frontierLookup, sourceEquation,
            targetEquation, frontierStatus⟩⟩
  · rcases tensorOrigin with
      ⟨frontierIndex, frontierLeft, frontierRight,
        frontierConclusion, frontierLookup,
        sourceEquation, targetEquation⟩
    have frontierConclusionUnmarked :
        final.core.assignedToken? frontierConclusion = none := by
      simpa [targetEquation] using boundaryTargetUnmarked
    have sourceAssigned :
        final.core.assignedToken? frontierLeft ≠ none ∨
          final.core.assignedToken? frontierRight ≠ none := by
      rcases sourceEquation with sourceLeft | sourceRight
      · exact Or.inl (by
          simpa [sourceLeft] using boundarySourceAssigned)
      · exact Or.inr (by
          simpa [sourceRight] using boundarySourceAssigned)
    have frontierStatus :=
      canonicalWorklistRun_tensor_frontier_status
        correct startEquation frontierLookup frontierConclusionUnmarked
        sourceAssigned
    rcases sourceEquation with sourceLeft | sourceRight
    · rcases frontierStatus with
        ⟨leftAssigned, rightUnassigned⟩ |
          ⟨rightAssigned, leftUnassigned⟩
      · exact
          ⟨path, boundary, boundaryMembership, boundarySourceAssigned,
            boundaryTargetUnmarked, Or.inr
              ⟨frontierIndex, frontierLeft, frontierRight,
                frontierConclusion, frontierLookup, targetEquation,
                Or.inl ⟨sourceLeft, rightUnassigned⟩⟩⟩
      · exact False.elim
          (by
            apply boundarySourceAssigned
            simpa [sourceLeft] using leftUnassigned)
    · rcases frontierStatus with
        ⟨leftAssigned, rightUnassigned⟩ |
          ⟨rightAssigned, leftUnassigned⟩
      · exact False.elim
          (by
            apply boundarySourceAssigned
            simpa [sourceRight] using rightUnassigned)
      · exact
          ⟨path, boundary, boundaryMembership, boundarySourceAssigned,
            boundaryTargetUnmarked, Or.inr
              ⟨frontierIndex, frontierLeft, frontierRight,
                frontierConclusion, frontierLookup, targetEquation,
                Or.inr ⟨sourceRight, leftUnassigned⟩⟩⟩

/-- The canonical finite production run keeps both concrete scheduler
registries within the submitted-link carrier. -/
private theorem canonicalWorklistRun_registryLengthBounds
    {certificate : Certificate} {started : UnificationState}
    (structural : certificate.StructurallyWellFormed)
    (startEquation :
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState = some started) :
    let final :=
      (runUnificationWorklist certificate
        certificate.worklistConsumers
        (worklistFuel certificate.links.length)
        (initializeWorklist certificate started)).state
    final.queue.length ≤ certificate.links.length ∧
      final.waiting.length ≤ certificate.links.length := by
  exact
    (canonicalWorklistRun_runInvariant
      structural startEquation).registryLengthBounds

/-- Detailed deterministic Guerrini-style parsing candidate with exact scan
statistics and a proof-relevant quadratic link-visit bound.

This executable does not enumerate switchings or cycles. It starts one thread
per axiom, forwards unary/par links whose premise tokens agree, and unifies
binary/tensor links whose premise tokens differ. A candidate is returned only
when every formula occurrence is marked, every connective fired, exactly one
component remains, and its frontier is exactly the public conclusion boundary.

The returned tree is still untrusted data. `unificationReconstruct` below
independently verifies it before exposing a proof-bearing result. Errors from
this tier are inconclusive except for `malformedInput`. -/
def unificationDerivationCandidateWithStats (certificate : Certificate) :
    Except UnificationError (UnificationCandidateResult certificate) := do
  if certificate.wellFormed != true then
    throw <| certificate.unificationError .malformedInput
      "structural well-formedness failed"
  let started ← match
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState with
    | none =>
        throw <| certificate.unificationError .axiomInitializationFailed
          "axiom endpoints could not be initialized as disjoint threads"
    | some value => pure value
  let saturated :=
    saturateUnification certificate.links certificate.links.length started
  if !saturated.state.allMarked then
    throw <| certificate.unificationError .incompleteMarking
      s!"saturation left unmarked formula occurrences after {saturated.state.firedConnectives} connective firings"
  if saturated.state.startedAxioms + saturated.state.firedConnectives !=
      certificate.links.length then
    throw <| certificate.unificationError .incompleteLinkFiring
      s!"fired {saturated.state.startedAxioms} axioms and {saturated.state.firedConnectives} connectives"
  let component ←
    match saturated.state.liveComponents with
    | [component] => pure component
    | components =>
        throw <| certificate.unificationError .nonUniqueThread
          s!"saturation retained {components.length} live token classes"
  if component.frontier.length != certificate.conclusions.length then
    throw <| certificate.unificationError .boundaryMismatch
      "the parsed frontier length differs from the public conclusion boundary"
  let order ← match
      occurrenceOrder? component.frontier certificate.conclusions with
    | none =>
        throw <| certificate.unificationError .boundaryMismatch
          "a public conclusion occurrence is absent from the parsed frontier"
    | some value => pure value
  if order.eraseDups.length != order.length then
    throw <| certificate.unificationError .boundaryMismatch
      "the public conclusion boundary repeats a parsed frontier occurrence"
  have bounds :=
    saturateUnification_stats certificate.links certificate.links.length
      started
  pure {
    tree := .exchange order component.tree
    stats := saturated.stats
    passesBound := bounds.1
    linkVisitsExact := bounds.2
  }

/-- Compatibility projection of the derivation-only unification candidate. -/
def unificationDerivationCandidate (certificate : Certificate) :
    Except UnificationError CutFreeDerivation :=
  certificate.unificationDerivationCandidateWithStats.map (·.tree)

/-- Event-driven ready/waiting worklist candidate.

This prototype keeps the Figure-5 token semantics and derivation components,
but replaces full repeated scans with dependency enqueues plus a waiting-par
set requeued after tensor unions. Its production fuel is proved sufficient to
empty the queue, but it has no universal correct-net completeness or linear
complexity theorem yet. -/
def unificationWorklistDerivationCandidate (certificate : Certificate) :
    Except UnificationError
      (UnificationWorklistCandidateResult certificate) := do
  if certificate.wellFormed != true then
    throw <| certificate.unificationError .malformedInput
      "structural well-formedness failed"
  let started ← match
      certificate.startAxioms? certificate.links
        certificate.initialUnificationState with
    | none =>
        throw <| certificate.unificationError .axiomInitializationFailed
          "axiom endpoints could not be initialized as disjoint threads"
    | some value => pure value
  let consumers := certificate.worklistConsumers
  let initial := certificate.initializeWorklist started
  let run :=
    runUnificationWorklist certificate consumers
      (worklistFuel certificate.links.length) initial
  let saturated := run.state
  let finalStats :=
    { saturated.stats with linkAttempts := run.linkAttempts }
  if !saturated.core.allMarked then
    throw <| certificate.unificationError .incompleteMarking
      s!"worklist left unmarked formula occurrences after {finalStats.linkAttempts} link attempts"
  if saturated.core.startedAxioms + saturated.core.firedConnectives !=
      certificate.links.length then
    throw <| certificate.unificationError .incompleteLinkFiring
      s!"worklist fired {saturated.core.startedAxioms} axioms and {saturated.core.firedConnectives} connectives"
  let component ←
    match saturated.core.liveComponents with
    | [component] => pure component
    | components =>
        throw <| certificate.unificationError .nonUniqueThread
          s!"worklist retained {components.length} live token classes"
  if component.frontier.length != certificate.conclusions.length then
    throw <| certificate.unificationError .boundaryMismatch
      "the worklist frontier length differs from the public conclusion boundary"
  let order ← match
      occurrenceOrder? component.frontier certificate.conclusions with
    | none =>
        throw <| certificate.unificationError .boundaryMismatch
          "a public conclusion occurrence is absent from the worklist frontier"
    | some value => pure value
  if order.eraseDups.length != order.length then
    throw <| certificate.unificationError .boundaryMismatch
      "the public conclusion boundary repeats a worklist frontier occurrence"
  pure {
    tree := .exchange order component.tree
    stats := finalStats
    attemptsBound := by
      simpa [worklistFuel] using run.linkAttemptsBound
  }

/-- Option compatibility wrapper for the detailed unification candidate. -/
def unificationDerivationCandidate? (certificate : Certificate) :
    Option CutFreeDerivation :=
  certificate.unificationDerivationCandidate.toOption

/-- Detailed proof-bearing deterministic unification fast path retaining scan
statistics. -/
def unificationReconstructWithStats (certificate : Certificate) :
    Except UnificationError (UnificationVerificationResult certificate) := do
  let candidate ← certificate.unificationDerivationCandidateWithStats
  match certificate.verifyDerivation? candidate.tree with
  | none =>
      throw <| certificate.unificationError .candidateVerificationFailed
        "the completed derivation failed independent verification"
  | some verification => pure { candidate, verification }

/-- Compatibility projection of the proof-bearing unification result. -/
def unificationReconstruct (certificate : Certificate) :
    Except UnificationError (DerivationVerificationResult certificate) :=
  certificate.unificationReconstructWithStats.map (·.verification)

/-- Proof-bearing fast path for deterministic unification. The generated tree
must pass the independent derivation verifier, including formula inference,
desequentialization, and intrinsic proof-net equivalence. -/
def unificationReconstruct? (certificate : Certificate) :
    Option (DerivationVerificationResult certificate) :=
  certificate.unificationReconstruct.toOption

/-- Independently verify the event-driven worklist candidate and retain its
operational counters. -/
def unificationWorklistReconstructWithStats (certificate : Certificate) :
    Except UnificationError
      (UnificationWorklistVerificationResult certificate) := do
  let candidate ← certificate.unificationWorklistDerivationCandidate
  match certificate.verifyDerivation? candidate.tree with
  | none =>
      throw <| certificate.unificationError .candidateVerificationFailed
        "the completed worklist derivation failed independent verification"
  | some verification => pure { candidate, verification }

/-- Proof-bearing option wrapper for the event-driven worklist prototype. -/
def unificationWorklistReconstruct? (certificate : Certificate) :
    Option (UnificationWorklistVerificationResult certificate) :=
  certificate.unificationWorklistReconstructWithStats.toOption

/-- Boolean event-driven worklist fast path. `false` is an inconclusive miss. -/
def unificationWorklistFastCheck (certificate : Certificate) : Bool :=
  certificate.unificationWorklistReconstruct?.isSome

/-- Every verified event-driven worklist success is reference accepted. -/
theorem unificationWorklistReconstruct?_accepted
    {certificate : Certificate}
    {result : UnificationWorklistVerificationResult certificate}
    (_equation :
      certificate.unificationWorklistReconstruct? = some result) :
    certificate.check = true := by
  rw [← result.verification.equivalent.check_eq]
  exact result.verification.outputAccepted

/-- Soundness of the event-driven worklist Boolean fast path. -/
theorem unificationWorklistFastCheck_sound (certificate : Certificate)
    (accepted : certificate.unificationWorklistFastCheck = true) :
    certificate.check = true := by
  unfold unificationWorklistFastCheck at accepted
  cases equation : certificate.unificationWorklistReconstruct? with
  | none => simp [equation] at accepted
  | some result =>
      exact certificate.unificationWorklistReconstruct?_accepted equation

/-- Exact worklist-first decision with the certified recursive reconstruction
fallback. This is exact but not yet a pure-worklist or linear criterion. -/
def unificationWorklistCheck (certificate : Certificate) : Bool :=
  certificate.unificationWorklistFastCheck ||
    certificate.reconstructsDerivation

/-- The worklist-first hybrid is extensionally equal to the reference checker. -/
theorem unificationWorklistCheck_eq_check (certificate : Certificate) :
    certificate.unificationWorklistCheck = certificate.check := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro accepted
    simp only [unificationWorklistCheck, Bool.or_eq_true] at accepted
    rcases accepted with fast | fallback
    · exact certificate.unificationWorklistFastCheck_sound fast
    · exact certificate.reconstructsDerivation_eq_true_iff_check.mp fallback
  · intro accepted
    simp only [unificationWorklistCheck, Bool.or_eq_true]
    exact Or.inr
      (certificate.reconstructsDerivation_eq_true_iff_check.mpr accepted)

/-- Iff form of exact agreement for the worklist-first hybrid. -/
theorem unificationWorklistCheck_eq_true_iff_check
    (certificate : Certificate) :
    certificate.unificationWorklistCheck = true ↔
      certificate.check = true := by
  rw [certificate.unificationWorklistCheck_eq_check]

/-- Proposition-level correctness interface for the worklist-first hybrid. -/
theorem unificationWorklistCheck_eq_true_iff_declarativelyCorrect
    (certificate : Certificate) :
    certificate.unificationWorklistCheck = true ↔
      certificate.DeclarativelyCorrect := by
  rw [certificate.unificationWorklistCheck_eq_check,
    certificate.check_iff_declarativelyCorrect]

/-- Boolean deterministic-unification fast path. A `false` result is a
heuristic miss, not yet a mathematical rejection. -/
def unificationFastCheck (certificate : Certificate) : Bool :=
  certificate.unificationReconstruct?.isSome

/-- A detailed unification success is reference-checker accepted. -/
theorem unificationReconstruct_accepted
    {certificate : Certificate}
    {result : DerivationVerificationResult certificate}
    (_equation : certificate.unificationReconstruct = .ok result) :
    certificate.check = true := by
  rw [← result.equivalent.check_eq]
  exact result.outputAccepted

/-- Successful deterministic unification exposes the complete proof-bearing
verification contract. -/
theorem unificationReconstruct?_sound
    {certificate : Certificate}
    {result : DerivationVerificationResult certificate}
    (_equation : certificate.unificationReconstruct? = some result) :
    certificate.StructurallyWellFormed ∧
      certificate.conclusionFormulas? = some result.sequent ∧
      result.tree.infer? = some result.sequent ∧
      result.tree.desequentialize? = some result.output ∧
      result.output.check = true ∧
      result.output.ProofNetEquivalent certificate :=
  ⟨result.inputStructural, result.inputLabels, result.inferred,
    result.desequentialized, result.outputAccepted, result.equivalent⟩

/-- Every successful deterministic unification result is accepted by the
reference proof-net semantics. -/
theorem unificationReconstruct?_accepted
    {certificate : Certificate}
    {result : DerivationVerificationResult certificate}
    (_equation : certificate.unificationReconstruct? = some result) :
    certificate.check = true := by
  rw [← result.equivalent.check_eq]
  exact result.outputAccepted

/-- Boolean fast-path success is exactly the existence of a proof-bearing
unification result. -/
theorem unificationFastCheck_eq_true_iff
    {certificate : Certificate} :
    certificate.unificationFastCheck = true ↔
      ∃ result : DerivationVerificationResult certificate,
        certificate.unificationReconstruct? = some result := by
  unfold unificationFastCheck
  cases equation : certificate.unificationReconstruct? with
  | none => simp
  | some result => simp

/-- Soundness of the Boolean deterministic-unification fast path. -/
theorem unificationFastCheck_sound (certificate : Certificate)
    (accepted : certificate.unificationFastCheck = true) :
    certificate.check = true := by
  unfold unificationFastCheck at accepted
  cases equation : certificate.unificationReconstruct? with
  | none => simp [equation] at accepted
  | some result =>
      exact certificate.unificationReconstruct?_accepted equation

/-- Exact switching-free decision procedure with the event-driven worklist,
then the eager deterministic scan, then the previously certified recursive
sequentializer as its completeness fallback.

The fallback is exhaustive in the worst case. Consequently this definition
does not yet constitute the linear-time algorithm from Guerrini's theorem. -/
def unificationCheck (certificate : Certificate) : Bool :=
  certificate.unificationWorklistFastCheck ||
    (certificate.unificationFastCheck ||
      certificate.reconstructsDerivation)

/-- The hybrid unification decision is extensionally equal to the reference
all-switchings checker. -/
theorem unificationCheck_eq_check (certificate : Certificate) :
    certificate.unificationCheck = certificate.check := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro accepted
    simp only [unificationCheck, Bool.or_eq_true] at accepted
    rcases accepted with worklist | fast | fallback
    · exact certificate.unificationWorklistFastCheck_sound worklist
    · exact certificate.unificationFastCheck_sound fast
    · exact certificate.reconstructsDerivation_eq_true_iff_check.mp fallback
  · intro accepted
    simp only [unificationCheck, Bool.or_eq_true]
    exact Or.inr <| Or.inr
      (certificate.reconstructsDerivation_eq_true_iff_check.mpr accepted)

/-- Iff form of exact agreement between the hybrid unification decision and
the reference checker. -/
theorem unificationCheck_eq_true_iff_check (certificate : Certificate) :
    certificate.unificationCheck = true ↔ certificate.check = true := by
  rw [certificate.unificationCheck_eq_check]

/-- Proposition-level correctness interface for the hybrid unification
decision. -/
theorem unificationCheck_eq_true_iff_declarativelyCorrect
    (certificate : Certificate) :
    certificate.unificationCheck = true ↔
      certificate.DeclarativelyCorrect := by
  rw [certificate.unificationCheck_eq_check,
    certificate.check_iff_declarativelyCorrect]

end Certificate

end ProofNetIR
