import ProofNetIR.Certificate
import Std

namespace ProofNetIR

/-!
# Injective structural code

This module defines a small, explicitly versioned structural encoding used as
the equality-reflecting payload of the broader proof-net canonical key.  It is
not the JSON wire format.  Its result is a list of string tokens, so list
boundaries are preserved before a future wire codec is chosen.

Every nested list is length-framed.  Natural numbers are represented by unary
strings because that representation has a short kernel proof of injectivity;
this first reference code favors a transparent proof boundary over density.
-/

namespace StructuralCode

/-- Unary natural-number token used by the reference structural code. -/
def unaryNat (value : Nat) : String :=
  String.ofList (List.replicate value 'x')

@[simp] theorem unaryNat_length (value : Nat) :
    (unaryNat value).length = value := by
  simp [unaryNat]

/-- The unary reference token reflects equality of natural numbers. -/
theorem unaryNat_injective : Function.Injective unaryNat := by
  intro left right same
  simpa using congrArg String.length same

@[simp] theorem unaryNat_inj {left right : Nat} :
    unaryNat left = unaryNat right ↔ left = right :=
  ⟨fun same => unaryNat_injective same, congrArg unaryNat⟩

/-- Length-frame a list of token lists.  Each segment is preceded by one unary
token carrying its token count. -/
def frame : List (List String) → List String
  | [] => []
  | head :: tail =>
      unaryNat head.length :: head ++ frame tail

/-- Length framing is injective even when payload tokens contain arbitrary
strings equal to tags or unary tokens. -/
theorem frame_injective : Function.Injective frame := by
  intro left
  induction left with
  | nil =>
      intro right same
      cases right with
      | nil => rfl
      | cons head tail =>
          simp [frame] at same
  | cons head tail ih =>
      intro right same
      cases right with
      | nil =>
          simp [frame] at same
      | cons other others =>
          simp only [frame] at same
          have sameCons := List.cons.inj same
          have lengthEquation :
              head.length = other.length :=
            unaryNat_injective sameCons.1
          have split := List.append_inj sameCons.2 lengthEquation
          have headEquation : head = other := split.1
          have tailEquation : tail = others := ih split.2
          simp [headEquation, tailEquation]

end StructuralCode

namespace Formula

/-- Explicit structural token code for one unit-free MLL formula. -/
def structuralCode : Formula → List String
  | .atom name positive =>
      StructuralCode.frame [
        ["atom"],
        [if positive then "positive" else "negative"],
        [name]]
  | .tensor left right =>
      StructuralCode.frame [
        ["tensor"], structuralCode left, structuralCode right]
  | .par left right =>
      StructuralCode.frame [
        ["par"], structuralCode left, structuralCode right]

/-- Formula structural codes reflect literal formula equality. -/
theorem structuralCode_injective : Function.Injective structuralCode := by
  intro left
  induction left with
  | atom name positive =>
      intro right same
      cases right with
      | atom otherName otherPositive =>
          have segments := StructuralCode.frame_injective same
          cases positive <;> cases otherPositive <;>
            simp_all [structuralCode]
      | tensor otherLeft otherRight =>
          have segments := StructuralCode.frame_injective same
          simp at segments
      | par otherLeft otherRight =>
          have segments := StructuralCode.frame_injective same
          simp at segments
  | tensor left right leftIH rightIH =>
      intro other same
      cases other with
      | atom name positive =>
          have segments := StructuralCode.frame_injective same
          simp at segments
      | tensor otherLeft otherRight =>
          have segments := StructuralCode.frame_injective same
          simp at segments
          have leftEquation := leftIH segments.1
          have rightEquation := rightIH segments.2
          simp [leftEquation, rightEquation]
      | par otherLeft otherRight =>
          have segments := StructuralCode.frame_injective same
          simp at segments
  | par left right leftIH rightIH =>
      intro other same
      cases other with
      | atom name positive =>
          have segments := StructuralCode.frame_injective same
          simp at segments
      | tensor otherLeft otherRight =>
          have segments := StructuralCode.frame_injective same
          simp at segments
      | par otherLeft otherRight =>
          have segments := StructuralCode.frame_injective same
          simp at segments
          have leftEquation := leftIH segments.1
          have rightEquation := rightIH segments.2
          simp [leftEquation, rightEquation]

end Formula

namespace Link

/-- Explicit structural token code for one local proof-net link. -/
def structuralCode : Link → List String
  | .axiom left right =>
      StructuralCode.frame [
        ["axiom"],
        [StructuralCode.unaryNat left],
        [StructuralCode.unaryNat right]]
  | .tensor left right conclusion =>
      StructuralCode.frame [
        ["tensor"],
        [StructuralCode.unaryNat left],
        [StructuralCode.unaryNat right],
        [StructuralCode.unaryNat conclusion]]
  | .par left right conclusion =>
      StructuralCode.frame [
        ["par"],
        [StructuralCode.unaryNat left],
        [StructuralCode.unaryNat right],
        [StructuralCode.unaryNat conclusion]]

/-- Link structural codes reflect literal link equality. -/
theorem structuralCode_injective : Function.Injective structuralCode := by
  intro left right same
  cases left <;> cases right <;>
    simp only [structuralCode] at same <;>
    have segments := StructuralCode.frame_injective same <;>
    simp at segments <;>
    simp_all

end Link

namespace Certificate

/-- Versioned, equality-reflecting token code for the literal certificate
fields.  This code does not normalize vertices or link order by itself. -/
def structuralCode (certificate : Certificate) : List String :=
  StructuralCode.frame [
    ["proofnet-structural-code-0.1"],
    StructuralCode.frame
      (certificate.formulas.toList.map Formula.structuralCode),
    StructuralCode.frame
      (certificate.links.map Link.structuralCode),
    StructuralCode.frame
      (certificate.conclusions.map fun vertex =>
        [StructuralCode.unaryNat vertex])
  ]

/-- The versioned structural code reflects literal certificate equality. -/
theorem structuralCode_injective : Function.Injective structuralCode := by
  intro left right same
  have fields := StructuralCode.frame_injective same
  simp at fields
  have formulaFrames :=
    StructuralCode.frame_injective fields.1
  have formulaLists :
      left.formulas.toList = right.formulas.toList :=
    (List.map_inj_right fun _ _ equation =>
      Formula.structuralCode_injective equation).mp formulaFrames
  have linkFrames :=
    StructuralCode.frame_injective fields.2.1
  have linkLists :
      left.links = right.links :=
    (List.map_inj_right fun _ _ equation =>
      Link.structuralCode_injective equation).mp linkFrames
  have conclusionFrames :=
    StructuralCode.frame_injective fields.2.2
  have conclusionLists :
      left.conclusions = right.conclusions :=
    (List.map_inj_right fun _ _ equation =>
      StructuralCode.unaryNat_injective
        (List.cons.inj equation).1).mp conclusionFrames
  cases left
  cases right
  simp_all

end Certificate

end ProofNetIR
