import ProofNetIR.LeanPropSchema

namespace ProofNetIR.LeanProp.Schema.Raw

open Schema

/-- Unindexed exchange syntax accepted at the untrusted schema boundary. -/
inductive Permutation where
  | nil
  | cons (formula : Formula) (tail : Permutation)
  | swap (first second : Formula) (rest : List Formula)
  | trans (first second : Permutation)
  deriving Repr, DecidableEq

namespace Permutation

/-- Infer the source and target context of unindexed exchange data. -/
def boundary? : Permutation → Option (List Formula × List Formula)
  | .nil => some ([], [])
  | .cons formula tail =>
      match tail.boundary? with
      | none => none
      | some (source, target) =>
          some (formula :: source, formula :: target)
  | .swap first second rest =>
      some (second :: first :: rest, first :: second :: rest)
  | .trans first second =>
      match first.boundary? with
      | none => none
      | some (firstSource, firstTarget) =>
          match second.boundary? with
          | none => none
          | some (secondSource, secondTarget) =>
              if firstTarget = secondSource then
                some (firstSource, secondTarget)
              else
                none

/-- Erase an indexed schema permutation to untrusted exchange syntax. -/
def ofIndexed {source target : List Formula} :
    Schema.ContextPermutation source target → Permutation
  | .nil => .nil
  | @Schema.ContextPermutation.cons formula _ _ permutation =>
      .cons formula (ofIndexed permutation)
  | .swap first second rest => .swap first second rest
  | .trans first second => .trans (ofIndexed first) (ofIndexed second)

/-- Erasing an indexed exchange preserves its exact source/target boundary. -/
theorem boundary?_ofIndexed {source target : List Formula}
    (permutation : Schema.ContextPermutation source target) :
    (ofIndexed permutation).boundary? = some (source, target) := by
  induction permutation with
  | nil => rfl
  | cons _ inductionHypothesis =>
      simp only [ofIndexed, boundary?]
      rw [inductionHypothesis]
  | swap => rfl
  | trans _ _ firstIH secondIH =>
      simp only [ofIndexed, boundary?]
      rw [firstIH, secondIH]
      dsimp
      rw [if_pos rfl]

end Permutation

/-- First-order, unindexed proof-template syntax for untrusted input. -/
inductive Derivation where
  | persistentAxiom (formula : Formula)
  | linearAxiom (formula : Formula)
  | persistentWeaken (extra : Formula) (premise : Derivation)
  | persistentContract (shared : Formula) (premise : Derivation)
  | persistentExchange (permutation : Permutation) (premise : Derivation)
  | linearExchange (permutation : Permutation) (premise : Derivation)
  | andIntro (left right : Derivation)
  | andElimLeft (premise : Derivation)
  | andElimRight (premise : Derivation)
  | impIntro (antecedent : Formula) (premise : Derivation)
  | impElim (function argument : Derivation)
  deriving Repr, DecidableEq

/-- A checker-inferred schema sequent. -/
structure Sequent where
  persistent : List Formula
  linear : List Formula
  goal : Formula
  deriving Repr, DecidableEq

/-- Stable categories for untrusted-template diagnostics. -/
inductive ErrorCode where
  | invalidPermutation
  | exchangeSourceMismatch
  | contractionContextTooShort
  | contractionFormulaMismatch
  | expectedConjunction
  | implicationContextMissing
  | implicationContextMismatch
  | expectedImplication
  | implicationArgumentMismatch
  deriving Repr, DecidableEq, BEq

/-- Path-aware checker failure. Child zero/one selects premise branches. -/
structure Error where
  path : List Nat
  code : ErrorCode
  detail : String
  deriving Repr, DecidableEq

namespace Error

/-- Human-readable diagnostic retaining the stable error code and path. -/
def render (error : Error) : String :=
  let renderedPath := error.path.foldl (fun value index => s!"{value}/{index}") "$"
  s!"{renderedPath}: {repr error.code}: {error.detail}"

end Error

namespace Derivation

/-- Internal constructor shared by checker branches with stable diagnostics. -/
def failure (path : List Nat) (code : ErrorCode) (detail : String) :
    Except Error α :=
  .error { path, code, detail }

/-- Check and infer a left conjunction projection. -/
def projectLeft (path : List Nat) (result : Sequent) :
    Except Error Sequent :=
  match result.goal with
  | .and left _ => .ok {
      persistent := result.persistent
      linear := result.linear
      goal := left
    }
  | _ => failure path .expectedConjunction
      "left projection requires a conjunction premise"

/-- Check and infer a right conjunction projection. -/
def projectRight (path : List Nat) (result : Sequent) :
    Except Error Sequent :=
  match result.goal with
  | .and _ right => .ok {
      persistent := result.persistent
      linear := result.linear
      goal := right
    }
  | _ => failure path .expectedConjunction
      "right projection requires a conjunction premise"

/-- Check and infer persistent implication introduction. -/
def introduceImplication (path : List Nat) (antecedent : Formula)
    (result : Sequent) : Except Error Sequent :=
  match result.persistent with
  | first :: rest =>
      if first = antecedent then
        .ok {
          persistent := rest
          linear := result.linear
          goal := .imp antecedent result.goal
        }
      else
        failure path .implicationContextMismatch
          "leading persistent formula does not match implication antecedent"
  | [] => failure path .implicationContextMissing
      "implication introduction requires a leading persistent antecedent"

/-- Check and infer implication elimination. -/
def eliminateImplication (path : List Nat) (functionResult : Sequent)
    (argumentResult : Sequent) : Except Error Sequent :=
  match functionResult.goal with
  | .imp antecedent consequent =>
      if argumentResult.goal = antecedent then
        .ok {
          persistent := functionResult.persistent ++ argumentResult.persistent
          linear := functionResult.linear ++ argumentResult.linear
          goal := consequent
        }
      else
        failure path .implicationArgumentMismatch
          "argument goal does not match implication antecedent"
  | _ => failure path .expectedImplication
      "implication elimination requires an implication function"

/-- Infer a raw derivation's contexts and goal, rejecting every ill-typed rule
application with a stable path and category. -/
def inferAt (path : List Nat) : Derivation → Except Error Sequent
  | .persistentAxiom formula =>
      .ok { persistent := [formula], linear := [], goal := formula }
  | .linearAxiom formula =>
      .ok { persistent := [], linear := [formula], goal := formula }
  | .persistentWeaken extra premise =>
      match inferAt (path ++ [0]) premise with
      | .error error => .error error
      | .ok result =>
          .ok { result with persistent := extra :: result.persistent }
  | .persistentContract shared premise =>
      match inferAt (path ++ [0]) premise with
      | .error error => .error error
      | .ok result =>
          match result.persistent with
          | first :: second :: rest =>
              if first = shared ∧ second = shared then
                .ok { result with persistent := shared :: rest }
              else
                failure path .contractionFormulaMismatch
                  "the first two persistent formulas must equal the contracted formula"
          | _ =>
              failure path .contractionContextTooShort
                "persistent contraction requires two leading occurrences"
  | .persistentExchange permutation premise =>
      match permutation.boundary? with
      | none =>
          failure path .invalidPermutation
            "exchange composition has incompatible intermediate contexts"
      | some (source, target) =>
          match inferAt (path ++ [0]) premise with
          | .error error => .error error
          | .ok result =>
              if result.persistent = source then
                .ok { result with persistent := target }
              else
                failure path .exchangeSourceMismatch
                  "persistent premise context does not match exchange source"
  | .linearExchange permutation premise =>
      match permutation.boundary? with
      | none =>
          failure path .invalidPermutation
            "exchange composition has incompatible intermediate contexts"
      | some (source, target) =>
          match inferAt (path ++ [0]) premise with
          | .error error => .error error
          | .ok result =>
              if result.linear = source then
                .ok { result with linear := target }
              else
                failure path .exchangeSourceMismatch
                  "linear premise context does not match exchange source"
  | .andIntro left right =>
      match inferAt (path ++ [0]) left with
      | .error error => .error error
      | .ok leftResult =>
          match inferAt (path ++ [1]) right with
          | .error error => .error error
          | .ok rightResult =>
              .ok {
                persistent := leftResult.persistent ++ rightResult.persistent
                linear := leftResult.linear ++ rightResult.linear
                goal := .and leftResult.goal rightResult.goal
              }
  | .andElimLeft premise =>
      match inferAt (path ++ [0]) premise with
      | .error error => .error error
      | .ok result => projectLeft path result
  | .andElimRight premise =>
      match inferAt (path ++ [0]) premise with
      | .error error => .error error
      | .ok result => projectRight path result
  | .impIntro antecedent premise =>
      match inferAt (path ++ [0]) premise with
      | .error error => .error error
      | .ok result => introduceImplication path antecedent result
  | .impElim function argument =>
      match inferAt (path ++ [0]) function with
      | .error error => .error error
      | .ok functionResult =>
          match inferAt (path ++ [1]) argument with
          | .error error => .error error
          | .ok argumentResult =>
              eliminateImplication path functionResult argumentResult

/-- Public raw-template inference boundary. -/
def infer? (derivation : Derivation) : Except Error Sequent :=
  derivation.inferAt []

/-- Erase an indexed schema derivation to untrusted syntax. -/
def ofIndexed {persistent linear : List Formula} {goal : Formula} :
    Schema.Derivation persistent linear goal → Derivation
  | .persistentAxiom => .persistentAxiom goal
  | .linearAxiom => .linearAxiom goal
  | @Schema.Derivation.persistentWeaken _ _ extra _ premise =>
      .persistentWeaken extra (ofIndexed premise)
  | @Schema.Derivation.persistentContract _ _ shared _ premise =>
      .persistentContract shared (ofIndexed premise)
  | .persistentExchange permutation premise =>
      .persistentExchange (Permutation.ofIndexed permutation)
        (ofIndexed premise)
  | .linearExchange permutation premise =>
      .linearExchange (Permutation.ofIndexed permutation) (ofIndexed premise)
  | .andIntro left right => .andIntro (ofIndexed left) (ofIndexed right)
  | .andElimLeft premise => .andElimLeft (ofIndexed premise)
  | .andElimRight premise => .andElimRight (ofIndexed premise)
  | @Schema.Derivation.impIntro _ _ antecedent _ premise =>
      .impIntro antecedent (ofIndexed premise)
  | .impElim function argument =>
      .impElim (ofIndexed function) (ofIndexed argument)

/-- The raw checker accepts every erased indexed derivation and recovers its
exact persistent context, linear context, and goal. -/
theorem inferAt_ofIndexed {persistent linear : List Formula} {goal : Formula}
    (derivation : Schema.Derivation persistent linear goal) (path : List Nat) :
    (ofIndexed derivation).inferAt path = Except.ok {
      persistent := persistent
      linear := linear
      goal := goal
    } := by
  induction derivation generalizing path with
  | persistentAxiom => rfl
  | linearAxiom => rfl
  | persistentWeaken _ inductionHypothesis =>
      simp only [ofIndexed, inferAt]
      rw [inductionHypothesis]
  | persistentContract _ inductionHypothesis =>
      simp only [ofIndexed, inferAt]
      rw [inductionHypothesis]
      dsimp
      rw [if_pos ⟨rfl, rfl⟩]
  | persistentExchange permutation _ inductionHypothesis =>
      simp only [ofIndexed, inferAt]
      rw [Permutation.boundary?_ofIndexed, inductionHypothesis]
      dsimp
      rw [if_pos rfl]
  | linearExchange permutation _ inductionHypothesis =>
      simp only [ofIndexed, inferAt]
      rw [Permutation.boundary?_ofIndexed, inductionHypothesis]
      dsimp
      rw [if_pos rfl]
  | andIntro _ _ leftIH rightIH =>
      simp only [ofIndexed, inferAt]
      rw [leftIH, rightIH]
  | andElimLeft _ inductionHypothesis =>
      simp only [ofIndexed, inferAt]
      rw [inductionHypothesis]
      rfl
  | andElimRight _ inductionHypothesis =>
      simp only [ofIndexed, inferAt]
      rw [inductionHypothesis]
      rfl
  | impIntro _ inductionHypothesis =>
      simp only [ofIndexed, inferAt]
      rw [inductionHypothesis]
      dsimp [introduceImplication]
      rw [if_pos rfl]
  | impElim _ _ functionIH argumentIH =>
      simp only [ofIndexed, inferAt]
      rw [functionIH, argumentIH]
      dsimp [eliminateImplication]
      rw [if_pos rfl]

/-- Exact public inference theorem for erased indexed derivations. -/
theorem infer?_ofIndexed {persistent linear : List Formula} {goal : Formula}
    (derivation : Schema.Derivation persistent linear goal) :
    (ofIndexed derivation).infer? = Except.ok {
      persistent := persistent
      linear := linear
      goal := goal
    } :=
  inferAt_ofIndexed derivation []

end Derivation

end ProofNetIR.LeanProp.Schema.Raw
