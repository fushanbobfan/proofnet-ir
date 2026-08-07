import ProofNetIR.SequentialFreshSourceBlocker

namespace ProofNetIRFreshSourceBlockerTests

open ProofNetIR
open ProofNetIR.SequentialUnification

def p : Formula := .atom "p" true

def pDual : Formula := p.dual

def axiomCertificate : Certificate where
  formulas := #[p, pDual]
  links := [.axiom 0 1]
  conclusions := [0, 1]

theorem axiomCertificate_structural :
    axiomCertificate.StructurallyWellFormed :=
  axiomCertificate.wellFormed_iff_structurallyWellFormed.mp (by decide)

def axiomState : UnificationState :=
  axiomCertificate.initialUnificationState

def startBlockedTags : Array Bool := #[false, true]

def partnerBlockedTags : Array Bool := #[true, false]

/- The starting endpoint itself is part of the exact source-left region. -/
def startTagBlocker :
    FreshSourceBlocker axiomCertificate axiomState startBlockedTags 1 where
  vertex := 1
  region := .visited (.refl 1)
  unavailable := Or.inl (by decide)

/- The other endpoint of the terminal submitted axiom is also part of the
region, even though it is not a recursively visited trace vertex. -/
def partnerTagBlocker :
    FreshSourceBlocker axiomCertificate axiomState partnerBlockedTags 1 where
  vertex := 0
  region := .terminalPartner (linkIndex := 0) (.refl 1) (Or.inr rfl)
  unavailable := Or.inl (by decide)

def q : Formula := .atom "q" true

def qDual : Formula := q.dual

/- A structurally valid recursive route starts at tensor conclusion 4, follows
the stored left premise 1, and terminates at the stored-right endpoint of
axiom (0, 1). -/
def recursiveCertificate : Certificate where
  formulas := #[p, pDual, q, qDual, .tensor pDual q]
  links := [.axiom 0 1, .axiom 2 3, .tensor 1 2 4]
  conclusions := [4, 0, 3]

theorem recursiveCertificate_structural :
    recursiveCertificate.StructurallyWellFormed :=
  recursiveCertificate.wellFormed_iff_structurallyWellFormed.mp
    (by native_decide)

def recursiveState : UnificationState where
  marks := Array.replicate recursiveCertificate.formulas.size none
  parents := #[]
  components := #[]
  startedAxioms := 0
  firedConnectives := 0

def recursiveTags : Array Bool :=
  Array.replicate recursiveCertificate.formulas.size false

theorem recursiveTensorStep : SourceLeftStep recursiveCertificate 4 1 :=
  .tensor (linkIndex := 2) (left := 1) (right := 2)
    (conclusion := 4) (by native_decide)

def recursiveRoute :
    SequentialFigure7.FreshSourceLeftRoute recursiveCertificate
      recursiveState recursiveTags 4 where
  trace := [4, 1]
  reached := 1
  partner := 0
  linkIndex := 0
  traceNonempty := by simp
  traceHead := by simp
  traceLast := by simp
  chain := .cons recursiveTensorStep (.singleton 1)
  reachable := .step recursiveTensorStep (.refl 1)
  exactAxiom := Or.inr (by native_decide)
  traceLength := by native_decide
  traceNodup := by decide
  traceFresh := by
    intro vertex membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl <;> native_decide
  traceReady := by
    intro vertex membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl <;> native_decide
  reachedReady := by native_decide
  partnerReady := by native_decide
  partnerFresh := by native_decide

/- The recursive stored-left route reconstructs the exact expected trace at
the complete formula-carrier fuel budget. -/
example :
    Nonempty
      (FreshSourceLeftRun recursiveCertificate recursiveState
        recursiveCertificate.formulas.size recursiveTags 4 [4, 1] 1 0 0) :=
  recursiveRoute.toFreshSourceLeftRun recursiveCertificate_structural

/- Region availability eliminates the blocker branch of the new public
classification theorem without assuming scheduler history or execution. -/
example :
    ∃ trace reached partner linkIndex,
      Nonempty
        (FreshSourceLeftRun recursiveCertificate recursiveState
          recursiveCertificate.formulas.size recursiveTags 4 trace reached
          partner linkIndex) := by
  refine
    ProofNetIR.Certificate.StructurallyWellFormed.freshSourceLeftRun_of_regionAvailable
      recursiveCertificate_structural (by native_decide) ?_
  intro vertex region
  have bound := region.inBounds recursiveCertificate_structural
    (by native_decide)
  constructor <;> simp [recursiveTags, recursiveState, bound]

def recursiveBlockedTags : Array Bool :=
  #[false, true, false, false, false]

def recursiveVisitedTagBlocker :
    FreshSourceBlocker recursiveCertificate recursiveState
      recursiveBlockedTags 4 where
  vertex := 1
  region := .visited (.step recursiveTensorStep (.refl 1))
  unavailable := Or.inl (by decide)

def partnerRawMarkedState : UnificationState :=
  { recursiveState with
    marks := recursiveState.marks.setIfInBounds 0 (some 0) }

def recursivePartnerRawBlocker :
    FreshSourceBlocker recursiveCertificate partnerRawMarkedState
      recursiveTags 4 where
  vertex := 0
  region := .terminalPartner (linkIndex := 0)
    (.step recursiveTensorStep (.refl 1)) (Or.inr (by native_decide))
  unavailable := Or.inr (by native_decide)

/- Region and blocker witnesses transport through one exact stored-left
source step without consulting an executor. -/
example {certificate : Certificate} {source next vertex : Vertex}
    (step : SourceLeftStep certificate source next)
    (region : SourceLeftRegionVertex certificate next vertex) :
    SourceLeftRegionVertex certificate source vertex :=
  region.prepend step

example {certificate : Certificate} {state : UnificationState}
    {tags : Array Bool} {source next : Vertex}
    (step : SourceLeftStep certificate source next)
    (blocker : FreshSourceBlocker certificate state tags next) :
    FreshSourceBlocker certificate state tags source :=
  blocker.prepend step

/- Compile-only public consumer: structural well-formedness and an in-bounds
start classify the exact formula-budget search as a fresh run or one explicit
dynamic source-region blocker.  No progress or enabledness premise appears. -/
example {certificate : Certificate} {state : UnificationState}
    {tags : Array Bool} {start : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (startBound : start < certificate.formulas.size) :
    (∃ trace reached partner linkIndex,
      Nonempty
        (FreshSourceLeftRun certificate state certificate.formulas.size tags
          start trace reached partner linkIndex)) ∨
      Nonempty (FreshSourceBlocker certificate state tags start) :=
  ProofNetIR.Certificate.StructurallyWellFormed.freshSourceLeftRun_or_blocker
    structural startBound

end ProofNetIRFreshSourceBlockerTests

def main : IO Unit :=
  IO.println "Fresh source-left run/blocker consumer fixtures passed"
