import ProofNetIR.ReconstructionChecker

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

/-- Current token class yielded by a marked formula occurrence. -/
def tokenAt? (state : UnificationState) (vertex : Vertex) : Option Nat := do
  let assigned ← state.marks[vertex]?
  let token ← assigned
  pure (state.representative token)

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
    Option UnificationState := do
  guard (state.marks[conclusion]? = some none)
  let leftToken ← state.tokenAt? left
  let rightToken ← state.tokenAt? right
  guard (leftToken == rightToken)
  let component ← state.componentAt? leftToken
  let (leftFocus, afterLeft) ← pickVertex? component.frontier left
  let (rightFocus, context) ← pickVertex? afterLeft right
  let nextComponent : UnificationComponent :=
    { tree := .par leftFocus rightFocus component.tree
      frontier := context ++ [conclusion] }
  pure {
    state with
    marks := state.marks.setIfInBounds conclusion (some leftToken)
    components :=
      state.components.setIfInBounds leftToken (some nextComponent)
    firedConnectives := state.firedConnectives + 1
  }

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
  pure {
    state with
    marks := state.marks.setIfInBounds conclusion (some representative)
    parents := state.parents.setIfInBounds retired representative
    components :=
      (state.components.setIfInBounds representative (some nextComponent))
        |>.setIfInBounds retired none
    firedConnectives := state.firedConnectives + 1
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

/-- Repeat deterministic passes until saturation. Every successful firing marks
a fresh connective conclusion, so `links.length` passes are sufficient. -/
private def saturateUnification (links : List Link) :
    Nat → UnificationState → UnificationState
  | 0, state => state
  | fuel + 1, state =>
      let (next, progress) := unificationPass links state
      if progress == 0 then next
      else saturateUnification links fuel next

/-- Detailed deterministic Guerrini-style parsing candidate.

This executable does not enumerate switchings or cycles. It starts one thread
per axiom, forwards unary/par links whose premise tokens agree, and unifies
binary/tensor links whose premise tokens differ. A candidate is returned only
when every formula occurrence is marked, every connective fired, exactly one
component remains, and its frontier is exactly the public conclusion boundary.

The returned tree is still untrusted data. `unificationReconstruct` below
independently verifies it before exposing a proof-bearing result. Errors from
this tier are inconclusive except for `malformedInput`. -/
def unificationDerivationCandidate (certificate : Certificate) :
    Except UnificationError CutFreeDerivation := do
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
  if !saturated.allMarked then
    throw <| certificate.unificationError .incompleteMarking
      s!"saturation left unmarked formula occurrences after {saturated.firedConnectives} connective firings"
  if saturated.startedAxioms + saturated.firedConnectives !=
      certificate.links.length then
    throw <| certificate.unificationError .incompleteLinkFiring
      s!"fired {saturated.startedAxioms} axioms and {saturated.firedConnectives} connectives"
  let component ←
    match saturated.liveComponents with
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
  pure (.exchange order component.tree)

/-- Option compatibility wrapper for the detailed unification candidate. -/
def unificationDerivationCandidate? (certificate : Certificate) :
    Option CutFreeDerivation :=
  certificate.unificationDerivationCandidate.toOption

/-- Detailed proof-bearing deterministic unification fast path. -/
def unificationReconstruct (certificate : Certificate) :
    Except UnificationError (DerivationVerificationResult certificate) := do
  let tree ← certificate.unificationDerivationCandidate
  match certificate.verifyDerivation? tree with
  | none =>
      throw <| certificate.unificationError .candidateVerificationFailed
        "the completed derivation failed independent verification"
  | some result => pure result

/-- Proof-bearing fast path for deterministic unification. The generated tree
must pass the independent derivation verifier, including formula inference,
desequentialization, and intrinsic proof-net equivalence. -/
def unificationReconstruct? (certificate : Certificate) :
    Option (DerivationVerificationResult certificate) :=
  certificate.unificationReconstruct.toOption

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

/-- Exact switching-free decision procedure with deterministic unification as
its fast path and the previously certified recursive sequentializer as its
completeness fallback.

The fallback is exhaustive in the worst case. Consequently this definition
does not yet constitute the linear-time algorithm from Guerrini's theorem. -/
def unificationCheck (certificate : Certificate) : Bool :=
  certificate.unificationFastCheck || certificate.reconstructsDerivation

/-- The hybrid unification decision is extensionally equal to the reference
all-switchings checker. -/
theorem unificationCheck_eq_check (certificate : Certificate) :
    certificate.unificationCheck = certificate.check := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro accepted
    simp only [unificationCheck, Bool.or_eq_true] at accepted
    rcases accepted with fast | fallback
    · exact certificate.unificationFastCheck_sound fast
    · exact certificate.reconstructsDerivation_eq_true_iff_check.mp fallback
  · intro accepted
    simp only [unificationCheck, Bool.or_eq_true]
    exact Or.inr
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
