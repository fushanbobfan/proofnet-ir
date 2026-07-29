import ProofNetIR

open ProofNetIR

namespace ProofNetIRTutorialSmoke

universe u

def p : Formula := .atom "p" true
def pDual : Formula := .atom "p" false

def axiomCertificate : Certificate where
  formulas := #[p, pDual]
  links := [.axiom 0 1]
  conclusions := [0, 1]

example : axiomCertificate.check = true := by native_decide

example : axiomCertificate.DeclarativelyCorrect :=
  axiomCertificate.check_iff_declarativelyCorrect.mp (by native_decide)

/- The Figure-7 consumer views are ordinary public dependency APIs.  An
explicit axiom conclusion has an empty consumer bucket, while the generic
connective view rejects it. -/

example : (axiomCertificate.conclusionBelow? 0).isSome = true := by
  native_decide

example : (axiomCertificate.connectiveBelow? 0).isNone = true := by
  native_decide

def figure7Initial :=
  SequentialSchedulerBridge.initializeReservation? axiomCertificate 0

theorem figure7Initial_invariant
    {before : SequentialSchedulerBridge.ReservationState}
    (equation : figure7Initial = some before) :
    SequentialSchedulerBridge.ReservationInvariant
      axiomCertificate before := by
  rcases
      SequentialSchedulerBridge.initializeReservation?_some_iff.mp
        (by simpa [figure7Initial] using equation) with
    ⟨step⟩
  exact step.reservationInvariant

def figure7ConclTransition :
    Option SequentialSchedulerBridge.ReservationState :=
  match equation : figure7Initial with
  | none => none
  | some before =>
      SequentialFigure7.concl? axiomCertificate before
        (figure7Initial_invariant equation)

example : figure7ConclTransition.isSome = true := by native_decide

def q : Formula := .atom "q" true
def qDual : Formula := .atom "q" false

def figure7ParCertificate : Certificate where
  formulas := #[p, pDual, q, qDual, .tensor p q, .par pDual qDual]
  links := [
    .axiom 0 1,
    .axiom 2 3,
    .tensor 0 2 4,
    .par 1 3 5
  ]
  conclusions := [4, 5]

def figure7ParInitial :=
  SequentialSchedulerBridge.initializeReservation? figure7ParCertificate 5

theorem figure7ParInitial_invariant
    {before : SequentialSchedulerBridge.ReservationState}
    (equation : figure7ParInitial = some before) :
    SequentialSchedulerBridge.ReservationInvariant
      figure7ParCertificate before := by
  rcases
      SequentialSchedulerBridge.initializeReservation?_some_iff.mp
        (by simpa [figure7ParInitial] using equation) with
    ⟨step⟩
  exact step.reservationInvariant

def figure7NopTransition :
    Option SequentialSchedulerBridge.ReservationState :=
  match equation : figure7ParInitial with
  | none => none
  | some before =>
      SequentialFigure7.nop? figure7ParCertificate before
        (figure7ParInitial_invariant equation)

example : figure7NopTransition.isSome = true := by native_decide

def checkedAxiomCertificate : CutFreeDerivation.CheckedCertificate :=
  ⟨axiomCertificate, by native_decide⟩

example : checkedAxiomCertificate.sameProofNet? checkedAxiomCertificate = true := by
  native_decide

example : checkedAxiomCertificate.certificate.ProofNetEquivalent
    checkedAxiomCertificate.certificate :=
  CutFreeDerivation.CheckedCertificate.sameProofNet?_eq_true_iff.mp
    (by native_decide)

example : ∃ fingerprint,
    axiomCertificate.proofNetCanonicalFingerprint? = some fingerprint :=
  axiomCertificate.proofNetCanonicalFingerprint?_exists

def swapAxiomVertices : VertexRenaming axiomCertificate.formulas.size :=
  VertexRenaming.swap axiomCertificate.formulas.size 0 1
    (by decide) (by decide)

example :
    axiomCertificate.proofNetCanonicalFingerprint? =
      (axiomCertificate.reindex
        swapAxiomVertices).proofNetCanonicalFingerprint? :=
  (show axiomCertificate.ProofNetEquivalent
      (axiomCertificate.reindex swapAxiomVertices) from
    (show axiomCertificate.ReindexEquivalent
        (axiomCertificate.reindex swapAxiomVertices) from
      ⟨swapAxiomVertices, rfl⟩).toProofNetEquivalent)
    |>.proofNetCanonicalFingerprint?_eq

/- The compact JSON fingerprint above remains a forward-only convenience API.
The typed structural code below has a kernel-checked converse on accepted
certificates. -/

example :
    axiomCertificate.ProofNetEquivalent
        (axiomCertificate.reindex swapAxiomVertices) ↔
      axiomCertificate.proofNetCanonicalCode? =
        (axiomCertificate.reindex swapAxiomVertices).proofNetCanonicalCode? :=
  Certificate.proofNetEquivalent_iff_canonicalCode_of_check
    (by native_decide) (by native_decide)

def axiomCanonicalKey : CanonicalKey :=
  axiomCertificate.proofNetCanonicalKey?.get (by native_decide)

example : axiomCanonicalKey.isWireAdmissible = true := by native_decide
example :
    axiomCertificate.proofNetCanonicalKeyWithinLimit?.isSome = true := by
  native_decide

example :
    axiomCertificate.ProofNetEquivalent axiomCertificate ↔
      axiomCertificate.proofNetCanonicalKeyWithinLimit? =
        axiomCertificate.proofNetCanonicalKeyWithinLimit? :=
  Certificate.proofNetEquivalent_iff_canonicalKeyWithinLimit_of_check
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

def parsedCanonicalKey :=
  CanonicalKey.fromString axiomCanonicalKey.toString

def parsedCanonicalKeyMatches : Bool :=
  match parsedCanonicalKey with
  | .ok parsed => parsed == axiomCanonicalKey
  | .error _ => false

example : parsedCanonicalKeyMatches = true := by native_decide

def parsed := Certificate.checkedFromString axiomCertificate.canonicalString

example : parsed.isOk = true := by native_decide

def reconstructed := axiomCertificate.sequentialize

example : reconstructed.isOk = true := by native_decide

example : ∃ result : ExecutableSequentializationResult axiomCertificate,
    axiomCertificate.sequentialize = .ok result :=
  axiomCertificate.sequentialize_complete (by native_decide)

def tree : CutFreeDerivation := .axiom "p" true

example : tree.infer? = some [p, pDual] := by native_decide
example : tree.desequentializeChecked?.isSome = true := by native_decide
example : tree.elaborate?.isSome = true := by native_decide

example : ∃ result : CutFreeDerivation.CheckedCertificate,
    tree.desequentializeChecked? = some result :=
  tree.desequentializeChecked?_exists_of_infer?
    (show tree.infer? = some [p, pDual] by native_decide)

example : ∃ result : CutFreeDerivation.ElaboratedCertificate,
    tree.elaborate? = some result :=
  tree.elaborate?_exists_of_infer?
    (show tree.infer? = some [p, pDual] by native_decide)

example (proposition : Prop) : proposition → proposition ∧ proposition :=
  LeanProp.Templates.duplicate_proof proposition

example (antecedent consequent : Prop)
    (functionProof : antecedent → consequent) (argumentProof : antecedent) :
    consequent :=
  LeanProp.Templates.linearModusPonens_proof antecedent consequent
    functionProof argumentProof

namespace ContextExchange

example {left right : List Prop} :
    Nonempty (LeanProp.ContextPermutation left right) ↔ left.Perm right :=
  LeanProp.ContextPermutation.nonempty_iff_listPerm

example {left right : List Prop}
    (permutation : LeanProp.ContextPermutation left right)
    (values : LeanProp.Assumptions right) :
    LeanProp.Assumptions.permute permutation
        (LeanProp.Assumptions.permute permutation.symm values) = values :=
  LeanProp.Assumptions.permute_symm_right permutation values

example {source target linear : List Prop} {goal : Prop}
    (permutation : source.Perm target)
    (derivation : LeanProp.Derivation.{u} source linear goal) :
    Nonempty (LeanProp.Derivation.{u} target linear goal) :=
  LeanProp.Derivation.persistentExchange_nonempty_of_listPerm
    permutation derivation

end ContextExchange

namespace PersistentNormalization

def redundantIdentity (proposition : Prop) :
    LeanProp.Derivation [proposition] [] proposition :=
  .persistentContract (.persistentWeaken (.persistentAxiom))

example (proposition : Prop) :
    (redundantIdentity proposition).normalizePersistentStructural =
      LeanProp.Derivation.persistentAxiom := by
  rfl

example {persistent linear : List Prop} {goal : Prop}
    (derivation : LeanProp.Derivation.{u} persistent linear goal) :
    derivation.normalizePersistentStructural.PersistentStructurallyReduced :=
  derivation.normalizePersistentStructural_reduced

example {persistent linear : List Prop} {goal : Prop}
    (derivation : LeanProp.Derivation.{u} persistent linear goal) :
    derivation.normalizePersistentStructural.normalizePersistentStructural =
      derivation.normalizePersistentStructural :=
  derivation.normalizePersistentStructural_idempotent

example {persistent linear : List Prop} {goal : Prop}
    (derivation : LeanProp.Derivation.{u} persistent linear goal) :
    derivation.normalizePersistentStructural.persistentStructuralSize ≤
      derivation.persistentStructuralSize :=
  derivation.normalizePersistentStructural_size_le

end PersistentNormalization

namespace RawSchema

open LeanProp.Schema

def proposition : LeanProp.Schema.Formula := .atom "consumer-p"

def valid : Raw.Derivation :=
  .impIntro proposition (.persistentAxiom proposition)

example : valid.infer? = .ok {
    persistent := []
    linear := []
    goal := .imp proposition proposition
  } := by rfl

def invalid : Raw.Derivation :=
  .andElimLeft (.persistentAxiom proposition)

example : invalid.infer? = .error {
    path := []
    code := .expectedConjunction
    detail := "left projection requires a conjunction premise"
  } := by rfl

example : (Raw.Derivation.checkedFromString valid.canonicalString).isOk =
    true := by native_decide

example : (Raw.Derivation.checkedFromString invalid.canonicalString).isOk =
    false := by native_decide

example (checked : Raw.CheckedDerivation) :
    checked.derivation.infer? = .ok checked.sequent :=
  checked.inferred

example (checked : Raw.CheckedDerivation) : PackedDerivation :=
  checked.toPacked "consumer-checked-wire"

example (checked : Raw.CheckedDerivation) (valuation : String → Prop)
    (persistentValues : LeanProp.Assumptions
      (checked.elaborated.persistent.map (Formula.evaluate valuation)))
    (linearValues : LeanProp.Assumptions
      (checked.elaborated.linear.map (Formula.evaluate valuation))) :
    checked.elaborated.goal.evaluate valuation :=
  checked.sound valuation persistentValues linearValues

end RawSchema

end ProofNetIRTutorialSmoke
