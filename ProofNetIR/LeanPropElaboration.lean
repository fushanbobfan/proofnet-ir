import ProofNetIR.LeanPropRaw

namespace ProofNetIR.LeanProp.Schema.Raw

/-- An unindexed exchange elaborated into proof-relevant indexed data. -/
structure ElaboratedPermutation where
  source : List Formula
  target : List Formula
  permutation : Schema.ContextPermutation source target

namespace Permutation

/-- Elaborate raw exchange syntax, rejecting incompatible transitive steps. -/
def elaborate? : Permutation → Option ElaboratedPermutation
  | .nil => some ⟨[], [], .nil⟩
  | .cons formula tail =>
      match tail.elaborate? with
      | none => none
      | some elaborated => some {
          source := formula :: elaborated.source
          target := formula :: elaborated.target
          permutation := .cons elaborated.permutation
        }
  | .swap first second rest => some {
      source := second :: first :: rest
      target := first :: second :: rest
      permutation := .swap first second rest
    }
  | .trans first second =>
      match first.elaborate?, second.elaborate? with
      | some firstElaborated, some secondElaborated =>
          if equation : firstElaborated.target = secondElaborated.source then
            some {
              source := firstElaborated.source
              target := secondElaborated.target
              permutation := .trans
                (equation ▸ firstElaborated.permutation)
                secondElaborated.permutation
            }
          else
            none
      | _, _ => none

private def elaboratedBoundary : Option ElaboratedPermutation →
    Option (List Formula × List Formula)
  | none => none
  | some elaborated => some (elaborated.source, elaborated.target)

/-- Exchange elaboration succeeds on exactly the same source/target boundary
as the raw boundary checker. -/
theorem boundary?_eq_elaborate? (permutation : Permutation) :
    permutation.boundary? = elaboratedBoundary permutation.elaborate? := by
  induction permutation with
  | nil => rfl
  | cons formula tail inductionHypothesis =>
      simp only [boundary?, elaborate?]
      rw [inductionHypothesis]
      cases tail.elaborate? <;> rfl
  | swap => rfl
  | trans first second firstIH secondIH =>
      simp only [boundary?, elaborate?]
      rw [firstIH, secondIH]
      cases first.elaborate? with
      | none => rfl
      | some firstElaborated =>
          cases second.elaborate? with
          | none => rfl
          | some secondElaborated =>
              cases firstElaborated
              cases secondElaborated
              simp only [elaboratedBoundary]
              split <;> rfl

end Permutation

/-- A raw proof template elaborated into an indexed schema derivation. -/
structure ElaboratedDerivation where
  persistent : List Formula
  linear : List Formula
  goal : Formula
  derivation : Schema.Derivation persistent linear goal

namespace ElaboratedDerivation

/-- Forget the indexed witness while retaining its exact inferred boundary. -/
def sequent (elaborated : ElaboratedDerivation) : Sequent := {
  persistent := elaborated.persistent
  linear := elaborated.linear
  goal := elaborated.goal
}

/-- Package an elaborated derivation for valuation-independent soundness. -/
def toPacked (name : String) (elaborated : ElaboratedDerivation) :
    Schema.PackedDerivation := {
  name
  persistent := elaborated.persistent
  linear := elaborated.linear
  goal := elaborated.goal
  derivation := elaborated.derivation
}

end ElaboratedDerivation

namespace Derivation

private def elaborationFailure (path : List Nat) (code : ErrorCode)
    (detail : String) : Except Error alpha :=
  .error { path, code, detail }

/-- Elaborate raw syntax into a typed schema derivation. The diagnostics and
resource checks intentionally mirror `inferAt`. -/
def elaborateAt (path : List Nat) : Derivation → Except Error ElaboratedDerivation
  | .persistentAxiom formula => .ok {
      persistent := [formula]
      linear := []
      goal := formula
      derivation := .persistentAxiom
    }
  | .linearAxiom formula => .ok {
      persistent := []
      linear := [formula]
      goal := formula
      derivation := .linearAxiom
    }
  | .persistentWeaken extra premise =>
      match elaborateAt (path ++ [0]) premise with
      | .error error => .error error
      | .ok result => .ok {
          persistent := extra :: result.persistent
          linear := result.linear
          goal := result.goal
          derivation := .persistentWeaken result.derivation
        }
  | .persistentContract shared premise =>
      match elaborateAt (path ++ [0]) premise with
      | .error error => .error error
      | .ok ⟨first :: second :: rest, linear, goal, typed⟩ =>
          if matching : first = shared ∧ second = shared then
            .ok {
              persistent := shared :: rest
              linear
              goal
              derivation := .persistentContract (by
                simpa only [matching.1, matching.2] using typed)
            }
          else
            elaborationFailure path .contractionFormulaMismatch
              "the first two persistent formulas must equal the contracted formula"
      | .ok _ =>
          elaborationFailure path .contractionContextTooShort
            "persistent contraction requires two leading occurrences"
  | .persistentExchange permutation premise =>
      match permutation.elaborate? with
      | none => elaborationFailure path .invalidPermutation
          "exchange composition has incompatible intermediate contexts"
      | some exchange =>
          match elaborateAt (path ++ [0]) premise with
          | .error error => .error error
          | .ok result =>
              if equation : result.persistent = exchange.source then
                .ok {
                  persistent := exchange.target
                  linear := result.linear
                  goal := result.goal
                  derivation := .persistentExchange exchange.permutation
                    (equation ▸ result.derivation)
                }
              else
                elaborationFailure path .exchangeSourceMismatch
                  "persistent premise context does not match exchange source"
  | .linearExchange permutation premise =>
      match permutation.elaborate? with
      | none => elaborationFailure path .invalidPermutation
          "exchange composition has incompatible intermediate contexts"
      | some exchange =>
          match elaborateAt (path ++ [0]) premise with
          | .error error => .error error
          | .ok result =>
              if equation : result.linear = exchange.source then
                .ok {
                  persistent := result.persistent
                  linear := exchange.target
                  goal := result.goal
                  derivation := .linearExchange exchange.permutation
                    (equation ▸ result.derivation)
                }
              else
                elaborationFailure path .exchangeSourceMismatch
                  "linear premise context does not match exchange source"
  | .andIntro left right =>
      match elaborateAt (path ++ [0]) left with
      | .error error => .error error
      | .ok leftResult =>
          match elaborateAt (path ++ [1]) right with
          | .error error => .error error
          | .ok rightResult => .ok {
              persistent := leftResult.persistent ++ rightResult.persistent
              linear := leftResult.linear ++ rightResult.linear
              goal := .and leftResult.goal rightResult.goal
              derivation := .andIntro leftResult.derivation
                rightResult.derivation
            }
  | .andElimLeft premise =>
      match elaborateAt (path ++ [0]) premise with
      | .error error => .error error
      | .ok result =>
          match equation : result.goal with
          | .and left right => .ok {
              persistent := result.persistent
              linear := result.linear
              goal := left
              derivation := .andElimLeft (by
                simpa only [equation] using result.derivation)
            }
          | _ => elaborationFailure path .expectedConjunction
              "left projection requires a conjunction premise"
  | .andElimRight premise =>
      match elaborateAt (path ++ [0]) premise with
      | .error error => .error error
      | .ok result =>
          match equation : result.goal with
          | .and left right => .ok {
              persistent := result.persistent
              linear := result.linear
              goal := right
              derivation := .andElimRight (by
                simpa only [equation] using result.derivation)
            }
          | _ => elaborationFailure path .expectedConjunction
              "right projection requires a conjunction premise"
  | .impIntro antecedent premise =>
      match elaborateAt (path ++ [0]) premise with
      | .error error => .error error
      | .ok ⟨first :: rest, linear, goal, typed⟩ =>
          if matching : first = antecedent then
            .ok {
              persistent := rest
              linear
              goal := .imp antecedent goal
              derivation := .impIntro (by
                simpa only [matching] using typed)
            }
          else elaborationFailure path .implicationContextMismatch
              "leading persistent formula does not match implication antecedent"
      | .ok ⟨[], _, _, _⟩ =>
          elaborationFailure path .implicationContextMissing
            "implication introduction requires a leading persistent antecedent"
  | .impElim function argument =>
      match elaborateAt (path ++ [0]) function with
      | .error error => .error error
      | .ok functionResult =>
          match elaborateAt (path ++ [1]) argument with
          | .error error => .error error
          | .ok argumentResult =>
              match functionEquation : functionResult.goal with
              | .imp antecedent consequent =>
                  if argumentEquation : argumentResult.goal = antecedent then
                    .ok {
                      persistent := functionResult.persistent ++
                        argumentResult.persistent
                      linear := functionResult.linear ++ argumentResult.linear
                      goal := consequent
                      derivation := .impElim (by
                        simpa only [functionEquation] using
                          functionResult.derivation)
                        (argumentEquation ▸ argumentResult.derivation)
                    }
                  else elaborationFailure path .implicationArgumentMismatch
                      "argument goal does not match implication antecedent"
              | _ => elaborationFailure path .expectedImplication
                  "implication elimination requires an implication function"

/-- Public executable raw-to-indexed elaboration boundary. -/
def elaborate? (derivation : Derivation) : Except Error ElaboratedDerivation :=
  derivation.elaborateAt []

/-- Forget only the indexed witness in an elaboration result. -/
def sequentResult : Except Error ElaboratedDerivation → Except Error Sequent
  | .error error => .error error
  | .ok elaborated => .ok elaborated.sequent

/-- Elaboration and inference have exactly the same success/failure result and
diagnostics after forgetting the indexed witness. -/
theorem inferAt_eq_elaborateAt (derivation : Derivation) (path : List Nat) :
    derivation.inferAt path = sequentResult (derivation.elaborateAt path) := by
  induction derivation generalizing path with
  | persistentAxiom => rfl
  | linearAxiom => rfl
  | persistentWeaken extra premise premiseIH =>
      simp only [inferAt, elaborateAt]
      generalize childEquation : premise.elaborateAt (path ++ [0]) = childResult
      have childIH := premiseIH (path ++ [0])
      rw [childEquation] at childIH
      cases childResult with
      | error error =>
          dsimp [sequentResult, ElaboratedDerivation.sequent] at childIH
          simp only [childIH]
          rfl
      | ok result =>
          dsimp [sequentResult, ElaboratedDerivation.sequent] at childIH
          simp only [childIH]
          rfl
  | persistentContract shared premise premiseIH =>
      simp only [inferAt, elaborateAt]
      generalize childEquation : premise.elaborateAt (path ++ [0]) = childResult
      have childIH := premiseIH (path ++ [0])
      rw [childEquation] at childIH
      cases childResult with
      | error error =>
          dsimp [sequentResult, ElaboratedDerivation.sequent] at childIH
          simp only [childIH]
          rfl
      | ok result =>
          cases result with
          | mk persistent linear goal typed =>
              dsimp [sequentResult, ElaboratedDerivation.sequent] at childIH
              simp only [childIH]
              cases persistent with
              | nil => simp [sequentResult, elaborationFailure, failure]
              | cons first tail =>
                  cases tail with
                  | nil => simp [sequentResult, elaborationFailure, failure]
                  | cons second rest =>
                      split <;>
                        simp_all [sequentResult, ElaboratedDerivation.sequent,
                          elaborationFailure, failure] <;>
                        split <;>
                        simp_all
  | persistentExchange permutation premise premiseIH =>
      simp only [inferAt, elaborateAt]
      rw [Permutation.boundary?_eq_elaborate?]
      generalize permutationEquation : permutation.elaborate? = permutationResult
      cases permutationResult with
      | none => rfl
      | some exchange =>
          cases exchange with
          | mk source target typedPermutation =>
            simp only [Permutation.elaboratedBoundary]
            generalize childEquation : premise.elaborateAt (path ++ [0]) = childResult
            have childIH := premiseIH (path ++ [0])
            rw [childEquation] at childIH
            cases childResult with
            | error error =>
                dsimp [sequentResult, ElaboratedDerivation.sequent] at childIH
                simp only [childIH]
                rfl
            | ok result =>
                cases result with
                | mk persistent linear goal typed =>
                    dsimp [sequentResult, ElaboratedDerivation.sequent] at childIH
                    simp only [childIH]
                    split <;> rfl
  | linearExchange permutation premise premiseIH =>
      simp only [inferAt, elaborateAt]
      rw [Permutation.boundary?_eq_elaborate?]
      generalize permutationEquation : permutation.elaborate? = permutationResult
      cases permutationResult with
      | none => rfl
      | some exchange =>
          cases exchange with
          | mk source target typedPermutation =>
            simp only [Permutation.elaboratedBoundary]
            generalize childEquation : premise.elaborateAt (path ++ [0]) = childResult
            have childIH := premiseIH (path ++ [0])
            rw [childEquation] at childIH
            cases childResult with
            | error error =>
                dsimp [sequentResult, ElaboratedDerivation.sequent] at childIH
                simp only [childIH]
                rfl
            | ok result =>
                cases result with
                | mk persistent linear goal typed =>
                    dsimp [sequentResult, ElaboratedDerivation.sequent] at childIH
                    simp only [childIH]
                    split <;> rfl
  | andIntro left right leftIH rightIH =>
      simp only [inferAt, elaborateAt]
      generalize leftEquation : left.elaborateAt (path ++ [0]) = leftResult
      have leftResultIH := leftIH (path ++ [0])
      rw [leftEquation] at leftResultIH
      cases leftResult with
      | error error =>
          dsimp [sequentResult, ElaboratedDerivation.sequent] at leftResultIH
          simp only [leftResultIH]
          rfl
      | ok leftElaborated =>
          dsimp [sequentResult, ElaboratedDerivation.sequent] at leftResultIH
          simp only [leftResultIH]
          generalize rightEquation : right.elaborateAt (path ++ [1]) = rightResult
          have rightResultIH := rightIH (path ++ [1])
          rw [rightEquation] at rightResultIH
          cases rightResult with
          | error error =>
              dsimp [sequentResult, ElaboratedDerivation.sequent] at rightResultIH
              simp only [rightResultIH]
              rfl
          | ok rightElaborated =>
              dsimp [sequentResult, ElaboratedDerivation.sequent] at rightResultIH
              simp only [rightResultIH]
              rfl
  | andElimLeft premise premiseIH =>
      simp only [inferAt, elaborateAt]
      generalize childEquation : premise.elaborateAt (path ++ [0]) = childResult
      have childIH := premiseIH (path ++ [0])
      rw [childEquation] at childIH
      cases childResult with
      | error error =>
          dsimp [sequentResult, ElaboratedDerivation.sequent] at childIH
          simp only [childIH]
          rfl
      | ok result =>
          cases result with
          | mk persistent linear goal typed =>
              dsimp [sequentResult, ElaboratedDerivation.sequent] at childIH
              simp only [childIH]
              cases goal <;> rfl
  | andElimRight premise premiseIH =>
      simp only [inferAt, elaborateAt]
      generalize childEquation : premise.elaborateAt (path ++ [0]) = childResult
      have childIH := premiseIH (path ++ [0])
      rw [childEquation] at childIH
      cases childResult with
      | error error =>
          dsimp [sequentResult, ElaboratedDerivation.sequent] at childIH
          simp only [childIH]
          rfl
      | ok result =>
          cases result with
          | mk persistent linear goal typed =>
              dsimp [sequentResult, ElaboratedDerivation.sequent] at childIH
              simp only [childIH]
              cases goal <;> rfl
  | impIntro antecedent premise premiseIH =>
      simp only [inferAt, elaborateAt]
      generalize childEquation : premise.elaborateAt (path ++ [0]) = childResult
      have childIH := premiseIH (path ++ [0])
      rw [childEquation] at childIH
      cases childResult with
      | error error =>
          dsimp [sequentResult, ElaboratedDerivation.sequent] at childIH
          simp only [childIH]
          rfl
      | ok result =>
          cases result with
          | mk persistent linear goal typed =>
              dsimp [sequentResult, ElaboratedDerivation.sequent] at childIH
              simp only [childIH]
              cases persistent with
              | nil =>
                  simp [sequentResult, elaborationFailure, failure,
                    introduceImplication]
              | cons first rest =>
                  split <;>
                    simp_all [sequentResult, ElaboratedDerivation.sequent,
                      elaborationFailure, failure, introduceImplication] <;>
                    split <;>
                    simp_all [sequentResult, ElaboratedDerivation.sequent]
  | impElim function argument functionIH argumentIH =>
      simp only [inferAt, elaborateAt]
      generalize functionEquation : function.elaborateAt (path ++ [0]) = functionResult
      have functionResultIH := functionIH (path ++ [0])
      rw [functionEquation] at functionResultIH
      cases functionResult with
      | error error =>
          dsimp [sequentResult, ElaboratedDerivation.sequent] at functionResultIH
          simp only [functionResultIH]
          rfl
      | ok functionElaborated =>
          cases functionElaborated with
          | mk functionPersistent functionLinear functionGoal functionTyped =>
            dsimp [sequentResult, ElaboratedDerivation.sequent] at functionResultIH
            simp only [functionResultIH]
            generalize argumentEquation : argument.elaborateAt (path ++ [1]) = argumentResult
            have argumentResultIH := argumentIH (path ++ [1])
            rw [argumentEquation] at argumentResultIH
            cases argumentResult with
            | error error =>
                dsimp [sequentResult, ElaboratedDerivation.sequent] at argumentResultIH
                simp only [argumentResultIH]
                rfl
            | ok argumentElaborated =>
                cases argumentElaborated with
                | mk argumentPersistent argumentLinear argumentGoal argumentTyped =>
                  dsimp [sequentResult, ElaboratedDerivation.sequent] at argumentResultIH
                  simp only [argumentResultIH]
                  cases functionGoal <;>
                    simp [sequentResult, elaborationFailure, failure,
                      eliminateImplication] <;>
                    split <;>
                    simp_all [sequentResult, ElaboratedDerivation.sequent]

/-- Every checker-accepted raw schema has an executable indexed elaboration
with exactly the inferred boundary. -/
theorem elaborate?_complete {derivation : Derivation} {sequent : Sequent}
    (accepted : derivation.infer? = .ok sequent) :
    ∃ elaborated, derivation.elaborate? = .ok elaborated ∧
      elaborated.sequent = sequent := by
  rw [infer?, inferAt_eq_elaborateAt] at accepted
  cases equation : derivation.elaborateAt [] with
  | error error => simp [equation, sequentResult] at accepted
  | ok elaborated =>
      refine ⟨elaborated, ?_, ?_⟩
      · simpa only [elaborate?] using equation
      · simpa [equation, sequentResult] using accepted

end Derivation

end ProofNetIR.LeanProp.Schema.Raw
