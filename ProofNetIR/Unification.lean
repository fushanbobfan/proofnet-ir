import ProofNetIR.UnificationSemantics

namespace ProofNetIR

/-- A partially parsed proof component used by the executable Guerrini-style
unification pass. `frontier` records the formula occurrences currently exposed
by `tree`, in exactly the order inferred by the derivation. -/
structure UnificationComponent where
  tree : CutFreeDerivation
  frontier : List Vertex
  deriving Repr, DecidableEq

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

/-- Mark one connective conclusion and increment the connective counter,
without changing the token partition or parsed components. -/
def markConclusion (state : UnificationState)
    (conclusion token : Nat) : UnificationState :=
  { state with
    marks := state.marks.setIfInBounds conclusion (some token)
    firedConnectives := state.firedConnectives + 1 }

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

/-- Live parsed component for a representative token. -/
def componentAt? (state : UnificationState) (token : Nat) :
    Option UnificationComponent := do
  let component ← state.components[state.representative token]?
  component

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
  let token := state.parents.size
  let component : UnificationComponent :=
    { tree := .axiom name positive
      frontier := [left, right] }
  pure {
    marks :=
      (state.marks.setIfInBounds left (some token)).setIfInBounds right
        (some token)
    parents := state.parents.push token
    components := state.components.push (some component)
    startedAxioms := state.startedAxioms + 1
    firedConnectives := state.firedConnectives
  }

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
    Option UnificationState := do
  guard (state.marks[conclusion]? = some none)
  let leftToken ← state.tokenAt? left
  let rightToken ← state.tokenAt? right
  guard (leftToken != rightToken)
  let leftComponent ← state.componentAt? leftToken
  let rightComponent ← state.componentAt? rightToken
  let (leftFocus, leftContext) ←
    pickVertex? leftComponent.frontier left
  let (rightFocus, rightContext) ←
    pickVertex? rightComponent.frontier right
  let representative := min leftToken rightToken
  let retired := max leftToken rightToken
  let nextComponent : UnificationComponent :=
    { tree :=
        .tensor leftFocus rightFocus leftComponent.tree rightComponent.tree
      frontier := conclusion :: (leftContext ++ rightContext) }
  let marked := state.markConclusion conclusion representative
  pure {
    marked with
    parents := state.parents.setIfInBounds retired representative
    components :=
      (state.components.setIfInBounds representative (some nextComponent))
        |>.setIfInBounds retired none
  }

/-- Try one connective. `none` means that the link is currently idle, waiting,
already fired, or a binary deadlock; it is not an exception. -/
private def fireConnective? (state : UnificationState) :
    Link → Option UnificationState
  | .axiom _ _ => none
  | .par left right conclusion =>
      firePar? state left right conclusion
  | .tensor left right conclusion =>
      fireTensor? state left right conclusion

/-- One deterministic left-to-right pass over all connective links. -/
private def unificationPass (links : List Link)
    (initial : UnificationState) : UnificationState × Nat :=
  links.foldl
    (fun (state, progress) link =>
      match fireConnective? state link with
      | none => (state, progress)
      | some next => (next, progress + 1))
    (initial, 0)

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
