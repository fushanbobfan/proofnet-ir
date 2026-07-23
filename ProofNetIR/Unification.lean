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

/-- Conservative executable link-attempt budget for the current worklist
prototype. This is not a completeness theorem for the chosen fuel. -/
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
executable link-attempt budget. Fuel sufficiency for every correct net remains
a separate completeness obligation. -/
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

/-- Equality of exactly the executable fields observed by the independent
unification semantics. Parsed derivation components and work counters are
intentionally ignored. -/
structure ObservationEquivalent
    (first second : UnificationState) : Prop where
  marks : first.marks = second.marks
  parents : first.parents = second.parents

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
  unfold representative
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
  unfold representative
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
          · injection equation with stateEquation
            subst next
            exact ⟨rfl, rfl⟩

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

private structure UnificationWorklistState where
  core : UnificationState
  queue : List Nat
  queued : Array Bool
  waiting : List Nat
  waitingFlags : Array Bool
  stats : UnificationWorklistStats

private def pushConsumer (consumers : Array (List Nat))
    (vertex linkIndex : Nat) : Array (List Nat) :=
  match consumers[vertex]? with
  | none => consumers
  | some indices =>
      consumers.setIfInBounds vertex (linkIndex :: indices)

/-- Precompute the links that can become newly armed when a formula occurrence
is marked. Structural well-formedness ensures resource-linear use, but this
builder also fails closed on out-of-range vertices. -/
private def worklistConsumers (certificate : Certificate) :
    Array (List Nat) :=
  certificate.links.zipIdx.foldl
    (fun consumers (link, linkIndex) =>
      match link with
      | .axiom _ _ => consumers
      | .par left right _ | .tensor left right _ =>
          let withLeft := pushConsumer consumers left linkIndex
          pushConsumer withLeft right linkIndex)
    (Array.replicate certificate.formulas.size [])

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

private def addWaiting (index : Nat)
    (state : UnificationWorklistState) : UnificationWorklistState :=
  if (state.waitingFlags[index]?).getD true then
    state
  else
    { state with
      waiting := index :: state.waiting
      waitingFlags := state.waitingFlags.setIfInBounds index true }

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

private def initializeWorklist (certificate : Certificate)
    (core : UnificationState) : UnificationWorklistState :=
  let initial : UnificationWorklistState :=
    { core
      queue := []
      queued := Array.replicate certificate.links.length false
      waiting := []
      waitingFlags := Array.replicate certificate.links.length false
      stats :=
        { initialEnqueues := 0
          dependencyEnqueues := 0
          waitingRequeues := 0
          linkAttempts := 0
          successfulFirings := 0 } }
  certificate.links.zipIdx.foldl
    (fun state (link, index) =>
      match link with
      | .axiom _ _ => state
      | _ => enqueueWorklist .initial index state)
    initial

private def popWorklist? (state : UnificationWorklistState) :
    Option (Nat × UnificationWorklistState) :=
  match state.queue with
  | [] => none
  | index :: rest =>
      some (index,
        { state with
          queue := rest
          queued := state.queued.setIfInBounds index false })

private def recordWorklistFiring (state : UnificationWorklistState) :
    UnificationWorklistState :=
  { state with
    stats :=
      { state.stats with
        successfulFirings := state.stats.successfulFirings + 1 } }

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

private def worklistFuel (linkCount : Nat) : Nat :=
  UnificationWorklistStats.attemptBudget linkCount

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
set requeued after tensor unions. It has no universal completeness or linear
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
