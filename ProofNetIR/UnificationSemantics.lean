import ProofNetIR.ReconstructionChecker

namespace ProofNetIR

/-- Proof-irrelevant state for the abstract Guerrini Figure-5 rules.

Unlike the executable union-find state, `sameThread` is an arbitrary
equivalence relation on the fixed carrier `Nat`. `tokenCount` allocates the
initial segment below it; natural numbers at or above the count are already
present in the carrier but cannot occur in a stored mark. This fixed-carrier
encoding lets successive states share one relation type. The two bound fields
make every stored mark refer to a submitted formula occurrence and an
allocated token. -/
structure UnificationMarking (certificate : Certificate) where
  tokenCount : Nat
  mark : Vertex → Option Nat
  sameThread : Nat → Nat → Prop
  sameThreadEquivalence : Equivalence sameThread
  markedVertexBound :
    ∀ {vertex token}, mark vertex = some token →
      vertex < certificate.formulas.size
  markedTokenBound :
    ∀ {vertex token}, mark vertex = some token →
      token < tokenCount

namespace UnificationMarking

/-- Two proof-irrelevant markings are equal when their observable token count,
raw marks, and thread relation are equal. Bound and equivalence witnesses are
proof-irrelevant. -/
@[ext]
theorem ext {first second : UnificationMarking certificate}
    (tokenCount : first.tokenCount = second.tokenCount)
    (mark : first.mark = second.mark)
    (sameThread : first.sameThread = second.sameThread) :
    first = second := by
  cases first
  cases second
  simp_all

/-- Mark one formula occurrence, leaving every other occurrence unchanged. -/
def setMark (mark : Vertex → Option Nat) (vertex token : Nat) :
    Vertex → Option Nat :=
  fun candidate => if candidate = vertex then some token else mark candidate

/-- In the fixed `Nat` carrier, allocating a fresh token preserves the global
thread relation. Freshness is a separate side condition: before allocation,
the newly exposed number must be unrelated to every allocated token. -/
def FreshExtension (state : UnificationMarking certificate)
    (_fresh : Nat) (left right : Nat) : Prop :=
  state.sameThread left right

/-- The carrier element about to be allocated is isolated from every token
that is already allocated. -/
def IsFreshToken (state : UnificationMarking certificate)
    (fresh : Nat) : Prop :=
  ∀ {old}, old < state.tokenCount →
    ¬state.sameThread old fresh

/-- Fresh-token allocation preserves an equivalence relation on the fixed
carrier. This theorem is a regression guard against accidentally defining the
extension only on the allocated initial segment. -/
theorem freshExtension_equivalence
    (state : UnificationMarking certificate) (fresh : Nat) :
    Equivalence (state.FreshExtension fresh) :=
  state.sameThreadEquivalence

/-- Merge the two old equivalence classes containing `leftToken` and
`rightToken`. This formula is the exact one-step equivalence closure because
`state.sameThread` is already an equivalence relation. -/
def MergeExtension (state : UnificationMarking certificate)
    (leftToken rightToken left right : Nat) : Prop :=
  state.sameThread left right ∨
    ((state.sameThread left leftToken ∨
        state.sameThread left rightToken) ∧
      (state.sameThread right leftToken ∨
        state.sameThread right rightToken))

/-- Merging two equivalence classes again yields an equivalence relation. -/
theorem mergeExtension_equivalence
    (state : UnificationMarking certificate)
    (leftToken rightToken : Nat) :
    Equivalence (state.MergeExtension leftToken rightToken) := by
  rcases state.sameThreadEquivalence with
    ⟨reflexive, symmetric, transitive⟩
  have transportLeft {first second : Nat}
      (related : state.sameThread first second) :
      (state.sameThread second leftToken ∨
          state.sameThread second rightToken) →
        (state.sameThread first leftToken ∨
          state.sameThread first rightToken) := by
    intro membership
    rcases membership with membership | membership
    · exact Or.inl (transitive related membership)
    · exact Or.inr (transitive related membership)
  have transportRight {first second : Nat}
      (related : state.sameThread first second) :
      (state.sameThread first leftToken ∨
          state.sameThread first rightToken) →
        (state.sameThread second leftToken ∨
          state.sameThread second rightToken) := by
    exact transportLeft (symmetric related)
  refine ⟨?_, ?_, ?_⟩
  · intro token
    exact Or.inl (reflexive token)
  · intro first second related
    rcases related with old | ⟨firstMerged, secondMerged⟩
    · exact Or.inl (symmetric old)
    · exact Or.inr ⟨secondMerged, firstMerged⟩
  · intro first second third firstSecond secondThird
    rcases firstSecond with
      oldFirstSecond | ⟨firstMerged, secondMerged⟩
    · rcases secondThird with
        oldSecondThird | ⟨secondMerged', thirdMerged⟩
      · exact Or.inl (transitive oldFirstSecond oldSecondThird)
      · exact Or.inr
          ⟨transportLeft oldFirstSecond secondMerged', thirdMerged⟩
    · rcases secondThird with
        oldSecondThird | ⟨secondMerged', thirdMerged⟩
      · exact Or.inr
          ⟨firstMerged, transportRight oldSecondThird secondMerged⟩
      · exact Or.inr ⟨firstMerged, thirdMerged⟩

end UnificationMarking

/-- The three source-level unification rules. -/
inductive UnificationRuleKind where
  | start
  | forward
  | unify
  deriving Repr, DecidableEq, BEq

/-- Independent one-step semantics for Guerrini's Figure-5 unification.

The constructors state their enabling conditions and exact state update
without mentioning the eager scan, queue, waiting set, or executable
union-find representation. -/
inductive UnificationStep (certificate : Certificate) :
    UnificationMarking certificate →
    UnificationMarking certificate → Prop
  | start
      {state next : UnificationMarking certificate}
      {left right : Vertex}
      (linkMembership : Link.axiom left right ∈ certificate.links)
      (leftUnmarked : state.mark left = none)
      (rightUnmarked : state.mark right = none)
      (freshIsolated :
        state.IsFreshToken state.tokenCount)
      (tokenCount :
        next.tokenCount = state.tokenCount + 1)
      (marking :
        next.mark =
          UnificationMarking.setMark
            (UnificationMarking.setMark state.mark left state.tokenCount)
            right state.tokenCount)
      (threads :
        ∀ first second,
          next.sameThread first second ↔
            state.FreshExtension state.tokenCount first second) :
      UnificationStep certificate state next
  | forward
      {state next : UnificationMarking certificate}
      {left right conclusion : Vertex}
      {leftToken rightToken outputToken : Nat}
      (linkMembership :
        Link.par left right conclusion ∈ certificate.links)
      (conclusionUnmarked : state.mark conclusion = none)
      (leftMarked : state.mark left = some leftToken)
      (rightMarked : state.mark right = some rightToken)
      (premisesSynchronized :
        state.sameThread leftToken rightToken)
      (outputTokenAllocated : outputToken < state.tokenCount)
      (outputTokenSynchronized :
        state.sameThread outputToken leftToken)
      (tokenCount :
        next.tokenCount = state.tokenCount)
      (marking :
        next.mark =
          UnificationMarking.setMark state.mark conclusion outputToken)
      (threads :
        next.sameThread = state.sameThread) :
      UnificationStep certificate state next
  | unify
      {state next : UnificationMarking certificate}
      {left right conclusion : Vertex}
      {leftToken rightToken outputToken : Nat}
      (linkMembership :
        Link.tensor left right conclusion ∈ certificate.links)
      (conclusionUnmarked : state.mark conclusion = none)
      (leftMarked : state.mark left = some leftToken)
      (rightMarked : state.mark right = some rightToken)
      (premisesDistinct :
        ¬state.sameThread leftToken rightToken)
      (outputTokenAllocated : outputToken < state.tokenCount)
      (outputTokenFromPremiseThread :
        state.sameThread outputToken leftToken ∨
          state.sameThread outputToken rightToken)
      (tokenCount :
        next.tokenCount = state.tokenCount)
      (marking :
        next.mark =
          UnificationMarking.setMark state.mark conclusion outputToken)
      (threads :
        ∀ first second,
          next.sameThread first second ↔
            state.MergeExtension leftToken rightToken first second) :
      UnificationStep certificate state next

namespace UnificationStep

/-- Every abstract transition uses a submitted link of the corresponding
Figure-5 class. -/
theorem link_exists {certificate : Certificate}
    {state next : UnificationMarking certificate}
    (step : UnificationStep certificate state next) :
    (∃ left right,
      Link.axiom left right ∈ certificate.links) ∨
    (∃ left right conclusion,
      Link.par left right conclusion ∈ certificate.links) ∨
    (∃ left right conclusion,
      Link.tensor left right conclusion ∈ certificate.links) := by
  cases step with
  | start membership =>
      exact Or.inl ⟨_, _, membership⟩
  | forward membership =>
      exact Or.inr <| Or.inl ⟨_, _, _, membership⟩
  | unify membership =>
      exact Or.inr <| Or.inr ⟨_, _, _, membership⟩

/-- Each Figure-5 transition marks the conclusion occurrence of the link it
fires. For an axiom/start transition, both axiom conclusions are marked with
the fresh token. -/
theorem marks_fired_conclusion {certificate : Certificate}
    {state next : UnificationMarking certificate}
    (step : UnificationStep certificate state next) :
    (∃ left right,
      Link.axiom left right ∈ certificate.links ∧
        (next.mark left).isSome = true ∧
        (next.mark right).isSome = true) ∨
    (∃ left right conclusion,
      Link.par left right conclusion ∈ certificate.links ∧
        (next.mark conclusion).isSome = true) ∨
    (∃ left right conclusion,
      Link.tensor left right conclusion ∈ certificate.links ∧
        (next.mark conclusion).isSome = true) := by
  cases step with
  | start membership leftUnmarked rightUnmarked freshIsolated
      tokenCount marking threads =>
      left
      refine ⟨_, _, membership, ?_, ?_⟩
      · simp [marking, UnificationMarking.setMark]
      · simp [marking, UnificationMarking.setMark]
  | forward membership conclusionUnmarked leftMarked rightMarked
      premisesSynchronized outputTokenAllocated outputTokenSynchronized
      tokenCount marking threads =>
      right
      left
      refine ⟨_, _, _, membership, ?_⟩
      simp [marking, UnificationMarking.setMark]
  | unify membership conclusionUnmarked leftMarked rightMarked
      premisesDistinct outputTokenAllocated outputTokenFromPremiseThread
      tokenCount marking threads =>
      right
      right
      refine ⟨_, _, _, membership, ?_⟩
      simp [marking, UnificationMarking.setMark]

/-- Abstract unification never retires an allocated token number. Start adds
one token; forward and unify preserve the allocation count. -/
theorem tokenCount_mono {certificate : Certificate}
    {state next : UnificationMarking certificate}
    (step : UnificationStep certificate state next) :
    state.tokenCount ≤ next.tokenCount := by
  cases step with
  | start _ _ _ _ tokenCount _ _ =>
      rw [tokenCount]
      exact Nat.le_add_right _ _
  | forward _ _ _ _ _ _ _ tokenCount _ _ =>
      exact Nat.le_of_eq tokenCount.symm
  | unify _ _ _ _ _ _ _ tokenCount _ _ =>
      exact Nat.le_of_eq tokenCount.symm

end UnificationStep

end ProofNetIR
