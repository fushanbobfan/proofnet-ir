import Lean.Elab.Tactic.Omega
import ProofNetIR.LeanPropBridge

namespace ProofNetIR.LeanProp

universe u

namespace Derivation

/-!
# Persistent structural normalization

The persistent calculus deliberately records weakening and contraction as
syntax. A weakening immediately consumed by contraction is redundant:

```text
Γ, P ⊢ A
──────── weaken P
Γ, P, P ⊢ A
────────── contract P
Γ, P ⊢ A
```

This module removes that redex throughout a derivation while preserving the
same indexed judgment. It does not erase arbitrary structural rules or add
linear weakening/contraction.
-/

/-- Detect the one constructor that can form the premise of the cancellable
persistent contraction/weakening redex. -/
def isPersistentWeaken {persistent linear : List Prop} {goal : Prop} :
    Derivation.{u} persistent linear goal → Bool
  | .persistentWeaken _ => true
  | _ => false

/-- A proof-relevant view that either exposes the premise of a persistent
weakening or carries a Boolean certificate that the derivation is not one.
The indexed view avoids unsafe casts when the persistent context is fixed. -/
inductive PersistentWeakenView :
    {persistent linear : List Prop} → {goal : Prop} →
      (derivation : Derivation.{u} persistent linear goal) → Type (u + 1) where
  | weaken {persistent linear : List Prop} {extra goal : Prop}
      (premise : Derivation.{u} persistent linear goal) :
      PersistentWeakenView (.persistentWeaken (extra := extra) premise)
  | other {persistent linear : List Prop} {goal : Prop}
      {derivation : Derivation.{u} persistent linear goal}
      (notWeaken : derivation.isPersistentWeaken = false) :
      PersistentWeakenView derivation

/-- Compute the indexed persistent-weakening view for any derivation. -/
noncomputable def persistentWeakenView
    {persistent linear : List Prop} {goal : Prop}
    (derivation : Derivation.{u} persistent linear goal) :
    PersistentWeakenView derivation := by
  induction derivation with
  | persistentAxiom => exact .other rfl
  | linearAxiom => exact .other rfl
  | persistentWeaken premise _ => exact .weaken premise
  | persistentContract _ _ => exact .other rfl
  | persistentExchange _ _ _ => exact .other rfl
  | linearExchange _ _ _ => exact .other rfl
  | andIntro _ _ _ _ => exact .other rfl
  | andElimLeft _ _ => exact .other rfl
  | andElimRight _ _ => exact .other rfl
  | impIntro _ _ => exact .other rfl
  | impElim _ _ _ _ => exact .other rfl
  | eqRewrite _ _ _ _ => exact .other rfl
  | forallElim _ _ _ => exact .other rfl
  | existsIntro _ _ _ => exact .other rfl

/-- Count persistent weakening and contraction nodes. Exchange and logical
rules do not contribute to this normalization measure. -/
noncomputable def persistentStructuralSize
    {persistent linear : List Prop} {goal : Prop} :
    Derivation.{u} persistent linear goal → Nat := by
  intro derivation
  induction derivation with
  | persistentAxiom => exact 0
  | linearAxiom => exact 0
  | persistentWeaken _ premiseSize => exact premiseSize + 1
  | persistentContract _ premiseSize => exact premiseSize + 1
  | persistentExchange _ _ premiseSize => exact premiseSize
  | linearExchange _ _ premiseSize => exact premiseSize
  | andIntro _ _ leftSize rightSize => exact leftSize + rightSize
  | andElimLeft _ premiseSize => exact premiseSize
  | andElimRight _ premiseSize => exact premiseSize
  | impIntro _ premiseSize => exact premiseSize
  | impElim _ _ functionSize argumentSize =>
      exact functionSize + argumentSize
  | eqRewrite _ _ equalitySize motiveSize =>
      exact equalitySize + motiveSize
  | forallElim _ _ premiseSize => exact premiseSize
  | existsIntro _ _ premiseSize => exact premiseSize

/-- A derivation contains no contraction whose immediate premise is a
persistent weakening, and all of its subderivations have the same property. -/
def PersistentStructurallyReduced
    {persistent linear : List Prop} {goal : Prop} :
    Derivation.{u} persistent linear goal → Prop := by
  intro derivation
  induction derivation with
  | persistentAxiom => exact True
  | linearAxiom => exact True
  | persistentWeaken _ premiseReduced => exact premiseReduced
  | persistentContract premise premiseReduced =>
      exact premise.isPersistentWeaken = false ∧ premiseReduced
  | persistentExchange _ _ premiseReduced => exact premiseReduced
  | linearExchange _ _ premiseReduced => exact premiseReduced
  | andIntro _ _ leftReduced rightReduced =>
      exact leftReduced ∧ rightReduced
  | andElimLeft _ premiseReduced => exact premiseReduced
  | andElimRight _ premiseReduced => exact premiseReduced
  | impIntro _ premiseReduced => exact premiseReduced
  | impElim _ _ functionReduced argumentReduced =>
      exact functionReduced ∧ argumentReduced
  | eqRewrite _ _ equalityReduced motiveReduced =>
      exact equalityReduced ∧ motiveReduced
  | forallElim _ _ premiseReduced => exact premiseReduced
  | existsIntro _ _ premiseReduced => exact premiseReduced

/-- Normalize one contraction from an already computed indexed weakening view.
The positive branch safely exposes the weakened premise without casts. -/
noncomputable def normalizePersistentContractFromView
    {persistent linear : List Prop} {shared goal : Prop}
    (derivation :
      Derivation.{u} (shared :: shared :: persistent) linear goal) :
    PersistentWeakenView derivation →
      Derivation.{u} (shared :: persistent) linear goal
  | .weaken premise => premise
  | .other _ => .persistentContract derivation

/-- View-directed smart contraction preserves structural reducedness. -/
theorem normalizePersistentContractFromView_reduced
    {persistent linear : List Prop} {shared goal : Prop}
    (derivation :
      Derivation.{u} (shared :: shared :: persistent) linear goal)
    (view : PersistentWeakenView derivation)
    (reduced : derivation.PersistentStructurallyReduced) :
    PersistentStructurallyReduced
      (normalizePersistentContractFromView derivation view) :=
  match view with
  | .weaken _ => reduced
  | .other notWeaken => ⟨notWeaken, reduced⟩

/-- A view-directed contraction remains a contraction when the premise is not
a persistent weakening. -/
theorem normalizePersistentContractFromView_eq_contract_of_notWeaken
    {persistent linear : List Prop} {shared goal : Prop}
    (derivation :
      Derivation.{u} (shared :: shared :: persistent) linear goal)
    (view : PersistentWeakenView derivation)
    (notWeaken : derivation.isPersistentWeaken = false) :
    normalizePersistentContractFromView derivation view =
      .persistentContract derivation :=
  match view with
  | .weaken _ => False.elim (by
      simp [isPersistentWeaken] at notWeaken)
  | .other _ => rfl

/-- Smart contraction never exceeds the cost of retaining the contraction
around its already-normalized premise. -/
theorem normalizePersistentContractFromView_size_le
    {persistent linear : List Prop} {shared goal : Prop}
    (derivation :
      Derivation.{u} (shared :: shared :: persistent) linear goal)
    (view : PersistentWeakenView derivation) :
    persistentStructuralSize
        (normalizePersistentContractFromView derivation view) ≤
      derivation.persistentStructuralSize + 1 :=
  match view with
  | .weaken premise => by
      change premise.persistentStructuralSize ≤
        premise.persistentStructuralSize + 2
      omega
  | .other _ => by
      change derivation.persistentStructuralSize + 1 ≤
        derivation.persistentStructuralSize + 1
      exact Nat.le_refl _

/-- Normalize one contraction after its premise has already been normalized. -/
noncomputable def normalizePersistentContract
    {persistent linear : List Prop} {shared goal : Prop}
    (derivation :
      Derivation.{u} (shared :: shared :: persistent) linear goal) :
    Derivation.{u} (shared :: persistent) linear goal :=
  normalizePersistentContractFromView derivation
    derivation.persistentWeakenView

/-- The smart contraction constructor preserves the structural-normal-form
predicate when its premise is already reduced. -/
theorem normalizePersistentContract_reduced
    {persistent linear : List Prop} {shared goal : Prop}
    (derivation :
      Derivation.{u} (shared :: shared :: persistent) linear goal)
    (reduced : derivation.PersistentStructurallyReduced) :
    derivation.normalizePersistentContract.PersistentStructurallyReduced := by
  unfold normalizePersistentContract
  exact normalizePersistentContractFromView_reduced derivation
    derivation.persistentWeakenView reduced

/-- The smart contraction is definitionally unchanged when its premise is
certified not to be a persistent weakening. -/
theorem normalizePersistentContract_eq_contract_of_notWeaken
    {persistent linear : List Prop} {shared goal : Prop}
    (derivation :
      Derivation.{u} (shared :: shared :: persistent) linear goal)
    (notWeaken : derivation.isPersistentWeaken = false) :
    derivation.normalizePersistentContract = .persistentContract derivation := by
  unfold normalizePersistentContract
  exact normalizePersistentContractFromView_eq_contract_of_notWeaken
    derivation derivation.persistentWeakenView notWeaken

/-- Smart contraction does not increase the persistent structural measure. -/
theorem normalizePersistentContract_size_le
    {persistent linear : List Prop} {shared goal : Prop}
    (derivation :
      Derivation.{u} (shared :: shared :: persistent) linear goal) :
    derivation.normalizePersistentContract.persistentStructuralSize ≤
      derivation.persistentStructuralSize + 1 := by
  unfold normalizePersistentContract
  exact normalizePersistentContractFromView_size_le derivation
    derivation.persistentWeakenView

/-- Recursively cancel every immediate persistent contraction/weakening pair.
The dependent result type makes preservation of persistent context, linear
context, and goal part of the normalizer's kernel-checked type. -/
noncomputable def normalizePersistentStructural
    {persistent linear : List Prop} {goal : Prop} :
    Derivation.{u} persistent linear goal →
      Derivation.{u} persistent linear goal := by
  intro derivation
  induction derivation with
  | persistentAxiom => exact .persistentAxiom
  | linearAxiom => exact .linearAxiom
  | persistentWeaken _ normalized =>
      exact .persistentWeaken normalized
  | persistentContract _ normalized =>
      exact normalized.normalizePersistentContract
  | persistentExchange permutation _ normalized =>
      exact .persistentExchange permutation normalized
  | linearExchange permutation _ normalized =>
      exact .linearExchange permutation normalized
  | andIntro _ _ leftNormalized rightNormalized =>
      exact .andIntro leftNormalized rightNormalized
  | andElimLeft _ normalized => exact .andElimLeft normalized
  | andElimRight _ normalized => exact .andElimRight normalized
  | impIntro _ normalized => exact .impIntro normalized
  | impElim _ _ functionNormalized argumentNormalized =>
      exact .impElim functionNormalized argumentNormalized
  | eqRewrite _ _ equalityNormalized motiveNormalized =>
      exact .eqRewrite equalityNormalized motiveNormalized
  | forallElim term _ normalized => exact .forallElim term normalized
  | existsIntro witness _ normalized => exact .existsIntro witness normalized

/-- Normalization removes every persistent contraction/weakening redex,
including redexes nested below logical and exchange rules. -/
theorem normalizePersistentStructural_reduced
    {persistent linear : List Prop} {goal : Prop}
    (derivation : Derivation.{u} persistent linear goal) :
    derivation.normalizePersistentStructural.PersistentStructurallyReduced := by
  induction derivation with
  | persistentAxiom =>
      simp [normalizePersistentStructural, PersistentStructurallyReduced]
  | linearAxiom =>
      simp [normalizePersistentStructural, PersistentStructurallyReduced]
  | persistentWeaken premise inductionHypothesis =>
      simpa [normalizePersistentStructural, PersistentStructurallyReduced]
        using inductionHypothesis
  | persistentContract premise inductionHypothesis =>
      exact normalizePersistentContract_reduced
        premise.normalizePersistentStructural inductionHypothesis
  | persistentExchange _ premise inductionHypothesis =>
      simpa [normalizePersistentStructural, PersistentStructurallyReduced]
        using inductionHypothesis
  | linearExchange _ premise inductionHypothesis =>
      simpa [normalizePersistentStructural, PersistentStructurallyReduced]
        using inductionHypothesis
  | andIntro left right leftIH rightIH =>
      simpa [normalizePersistentStructural, PersistentStructurallyReduced]
        using And.intro leftIH rightIH
  | andElimLeft premise inductionHypothesis =>
      simpa [normalizePersistentStructural, PersistentStructurallyReduced]
        using inductionHypothesis
  | andElimRight premise inductionHypothesis =>
      simpa [normalizePersistentStructural, PersistentStructurallyReduced]
        using inductionHypothesis
  | impIntro premise inductionHypothesis =>
      simpa [normalizePersistentStructural, PersistentStructurallyReduced]
        using inductionHypothesis
  | impElim function argument functionIH argumentIH =>
      simpa [normalizePersistentStructural, PersistentStructurallyReduced]
        using And.intro functionIH argumentIH
  | eqRewrite equality motive equalityIH motiveIH =>
      simpa [normalizePersistentStructural, PersistentStructurallyReduced]
        using And.intro equalityIH motiveIH
  | forallElim _ premise inductionHypothesis =>
      simpa [normalizePersistentStructural, PersistentStructurallyReduced]
        using inductionHypothesis
  | existsIntro _ premise inductionHypothesis =>
      simpa [normalizePersistentStructural, PersistentStructurallyReduced]
        using inductionHypothesis

/-- A reduced derivation is a fixed point of persistent structural
normalization. -/
theorem normalizePersistentStructural_eq_self_of_reduced
    {persistent linear : List Prop} {goal : Prop}
    (derivation : Derivation.{u} persistent linear goal)
    (reduced : derivation.PersistentStructurallyReduced) :
    derivation.normalizePersistentStructural = derivation := by
  induction derivation with
  | persistentAxiom => rfl
  | linearAxiom => rfl
  | persistentWeaken premise inductionHypothesis =>
      change persistentWeaken premise.normalizePersistentStructural =
        persistentWeaken premise
      rw [inductionHypothesis reduced]
  | persistentContract premise inductionHypothesis =>
      rcases reduced with ⟨notWeaken, premiseReduced⟩
      change premise.normalizePersistentStructural.normalizePersistentContract =
        .persistentContract premise
      rw [inductionHypothesis premiseReduced]
      exact normalizePersistentContract_eq_contract_of_notWeaken
        premise notWeaken
  | persistentExchange permutation premise inductionHypothesis =>
      change persistentExchange permutation
          premise.normalizePersistentStructural =
        persistentExchange permutation premise
      rw [inductionHypothesis reduced]
  | linearExchange permutation premise inductionHypothesis =>
      change linearExchange permutation
          premise.normalizePersistentStructural =
        linearExchange permutation premise
      rw [inductionHypothesis reduced]
  | andIntro left right leftIH rightIH =>
      rcases reduced with ⟨leftReduced, rightReduced⟩
      change andIntro left.normalizePersistentStructural
          right.normalizePersistentStructural =
        andIntro left right
      rw [leftIH leftReduced, rightIH rightReduced]
  | andElimLeft premise inductionHypothesis =>
      change andElimLeft premise.normalizePersistentStructural =
        andElimLeft premise
      rw [inductionHypothesis reduced]
  | andElimRight premise inductionHypothesis =>
      change andElimRight premise.normalizePersistentStructural =
        andElimRight premise
      rw [inductionHypothesis reduced]
  | impIntro premise inductionHypothesis =>
      change impIntro premise.normalizePersistentStructural =
        impIntro premise
      rw [inductionHypothesis reduced]
  | impElim function argument functionIH argumentIH =>
      rcases reduced with ⟨functionReduced, argumentReduced⟩
      change impElim function.normalizePersistentStructural
          argument.normalizePersistentStructural =
        impElim function argument
      rw [functionIH functionReduced, argumentIH argumentReduced]
  | eqRewrite equality motive equalityIH motiveIH =>
      rcases reduced with ⟨equalityReduced, motiveReduced⟩
      change eqRewrite equality.normalizePersistentStructural
          motive.normalizePersistentStructural =
        eqRewrite equality motive
      rw [equalityIH equalityReduced, motiveIH motiveReduced]
  | forallElim term premise inductionHypothesis =>
      change forallElim term premise.normalizePersistentStructural =
        forallElim term premise
      rw [inductionHypothesis reduced]
  | existsIntro witness premise inductionHypothesis =>
      change existsIntro witness premise.normalizePersistentStructural =
        existsIntro witness premise
      rw [inductionHypothesis reduced]

/-- Persistent structural normalization is idempotent on every derivation. -/
theorem normalizePersistentStructural_idempotent
    {persistent linear : List Prop} {goal : Prop}
    (derivation : Derivation.{u} persistent linear goal) :
    derivation.normalizePersistentStructural.normalizePersistentStructural =
      derivation.normalizePersistentStructural :=
  normalizePersistentStructural_eq_self_of_reduced
    derivation.normalizePersistentStructural
    derivation.normalizePersistentStructural_reduced

/-- Persistent structural normalization never increases the number of
weakening/contraction nodes. -/
theorem normalizePersistentStructural_size_le
    {persistent linear : List Prop} {goal : Prop}
    (derivation : Derivation.{u} persistent linear goal) :
    derivation.normalizePersistentStructural.persistentStructuralSize ≤
      derivation.persistentStructuralSize := by
  induction derivation with
  | persistentAxiom => exact Nat.le_refl 0
  | linearAxiom => exact Nat.le_refl 0
  | persistentWeaken premise inductionHypothesis =>
      change premise.normalizePersistentStructural.persistentStructuralSize +
          1 ≤ premise.persistentStructuralSize + 1
      omega
  | persistentContract premise inductionHypothesis =>
      change persistentStructuralSize
          premise.normalizePersistentStructural.normalizePersistentContract ≤
        premise.persistentStructuralSize + 1
      have smart := normalizePersistentContract_size_le
        premise.normalizePersistentStructural
      omega
  | persistentExchange _ premise inductionHypothesis =>
      exact inductionHypothesis
  | linearExchange _ premise inductionHypothesis =>
      exact inductionHypothesis
  | andIntro left right leftIH rightIH =>
      change left.normalizePersistentStructural.persistentStructuralSize +
          right.normalizePersistentStructural.persistentStructuralSize ≤
        left.persistentStructuralSize + right.persistentStructuralSize
      omega
  | andElimLeft premise inductionHypothesis =>
      exact inductionHypothesis
  | andElimRight premise inductionHypothesis =>
      exact inductionHypothesis
  | impIntro premise inductionHypothesis =>
      exact inductionHypothesis
  | impElim function argument functionIH argumentIH =>
      change function.normalizePersistentStructural.persistentStructuralSize +
          argument.normalizePersistentStructural.persistentStructuralSize ≤
        function.persistentStructuralSize +
          argument.persistentStructuralSize
      omega
  | eqRewrite equality motive equalityIH motiveIH =>
      change equality.normalizePersistentStructural.persistentStructuralSize +
          motive.normalizePersistentStructural.persistentStructuralSize ≤
        equality.persistentStructuralSize + motive.persistentStructuralSize
      omega
  | forallElim _ premise inductionHypothesis =>
      exact inductionHypothesis
  | existsIntro _ premise inductionHypothesis =>
      exact inductionHypothesis

/-- The typed normalizer cancels the persistent contraction/weakening
redex after recursively normalizing its premise. -/
theorem normalizePersistentStructural_contract_weaken
    {persistent linear : List Prop} {shared goal : Prop}
    (derivation : Derivation.{u} (shared :: persistent) linear goal) :
    normalizePersistentStructural
        (.persistentContract (.persistentWeaken derivation)) =
      derivation.normalizePersistentStructural := by
  rfl

/-- The cancellable pair contributes exactly two persistent structural nodes
before normalization. -/
theorem persistentStructuralSize_contract_weaken
    {persistent linear : List Prop} {shared goal : Prop}
    (derivation : Derivation.{u} (shared :: persistent) linear goal) :
    persistentStructuralSize
        (.persistentContract (.persistentWeaken derivation)) =
      derivation.persistentStructuralSize + 2 := by
  rfl

/-- Normalization commutes with an unmatched persistent weakening. -/
theorem normalizePersistentStructural_weaken
    {persistent linear : List Prop} {extra goal : Prop}
    (derivation : Derivation.{u} persistent linear goal) :
    normalizePersistentStructural (.persistentWeaken (extra := extra) derivation) =
      .persistentWeaken derivation.normalizePersistentStructural := by
  rfl

/-- Typed normalization preserves the exact linear-resource count. -/
theorem normalizePersistentStructural_linearAxiomCount
    {persistent linear : List Prop} {goal : Prop}
    (derivation : Derivation.{u} persistent linear goal) :
    derivation.normalizePersistentStructural.linearAxiomCount =
      derivation.linearAxiomCount := by
  rw [linearAxiomCount_eq_length, linearAxiomCount_eq_length]

/-- Interpreting a normalized derivation yields the same proof proposition.
The theorem is pointwise so it does not require function extensionality. -/
theorem normalizePersistentStructural_toProof
    {persistent linear : List Prop} {goal : Prop}
    (derivation : Derivation.{u} persistent linear goal)
    (persistentValues : Assumptions persistent)
    (linearValues : Assumptions linear) :
    derivation.normalizePersistentStructural.toProof
        persistentValues linearValues =
      derivation.toProof persistentValues linearValues :=
  Subsingleton.elim _ _

end Derivation

end ProofNetIR.LeanProp
