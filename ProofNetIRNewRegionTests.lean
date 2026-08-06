import ProofNetIR.SequentialFigure7NewRegion

namespace ProofNetIRNewRegionTests

open ProofNetIR
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialUnification

def p : Formula := .atom "p" true

def pDual : Formula := p.dual

def q : Formula := .atom "q" true

def qDual : Formula := q.dual

/-- A structurally valid stored-right route: the source-left search starts at
the tensor conclusion `4`, follows the stored left premise `1`, and reaches
the right endpoint of the submitted axiom `(0, 1)`. -/
def validCertificate : Certificate where
  formulas := #[p, pDual, q, qDual, .tensor pDual q]
  links := [.axiom 0 1, .axiom 2 3, .tensor 1 2 4]
  conclusions := [4, 0, 3]

def validState : UnificationState where
  marks := Array.replicate validCertificate.formulas.size none
  parents := #[]
  components := #[]
  startedAxioms := 0
  firedConnectives := 0

def validTags : Array Bool :=
  Array.replicate validCertificate.formulas.size false

def validRoute :
    SequentialFigure7.FreshSourceLeftRoute validCertificate validState
      validTags 4 where
  trace := [4, 1]
  reached := 1
  partner := 0
  linkIndex := 0
  traceNonempty := by simp
  traceHead := by simp
  traceLast := by simp
  chain := .cons
    (SourceLeftStep.tensor (linkIndex := 2) (left := 1) (right := 2)
      (conclusion := 4) (by native_decide))
    (.singleton 1)
  reachable := .step
    (SourceLeftStep.tensor (linkIndex := 2) (left := 1) (right := 2)
      (conclusion := 4) (by native_decide))
    (.refl 1)
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

example : validCertificate.StructurallyWellFormed :=
  validCertificate.wellFormed_iff_structurallyWellFormed.mp (by native_decide)

example : validRoute.partner ∉ validRoute.trace := by
  exact validRoute.partner_not_mem_trace_of_structural
    (validCertificate.wellFormed_iff_structurallyWellFormed.mp
      (by native_decide))

/-- The bridge reconstructs the exact proof-relevant run at the complete
formula-carrier fuel budget without assuming an executable equation. -/
example :
    Nonempty
      (FreshSourceLeftRun validCertificate validState
        validCertificate.formulas.size validTags 4 [4, 1] 1 0 0) := by
  exact validRoute.toFreshSourceLeftRun
    (validCertificate.wellFormed_iff_structurallyWellFormed.mp
      (by native_decide))

/-- A deliberately malformed certificate can satisfy the older route record
while putting the terminal partner at the route head.  This isolates why the
partner-outside condition is logically required by the local reconstruction
when structural well-formedness is not available. -/
def forgedCertificate : Certificate where
  formulas := #[p, pDual, q]
  links := [.axiom 0 1, .tensor 1 2 0]
  conclusions := [0]

def forgedState : UnificationState where
  marks := Array.replicate forgedCertificate.formulas.size none
  parents := #[]
  components := #[]
  startedAxioms := 0
  firedConnectives := 0

def forgedTags : Array Bool :=
  Array.replicate forgedCertificate.formulas.size false

def forgedRoute :
    SequentialFigure7.FreshSourceLeftRoute forgedCertificate forgedState
      forgedTags 0 where
  trace := [0, 1]
  reached := 1
  partner := 0
  linkIndex := 0
  traceNonempty := by simp
  traceHead := by simp
  traceLast := by simp
  chain := .cons
    (SourceLeftStep.tensor (linkIndex := 1) (left := 1) (right := 2)
      (conclusion := 0) (by native_decide))
    (.singleton 1)
  reachable := .step
    (SourceLeftStep.tensor (linkIndex := 1) (left := 1) (right := 2)
      (conclusion := 0) (by native_decide))
    (.refl 1)
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

example : forgedCertificate.wellFormed = false := by
  native_decide

example : forgedRoute.partner ∈ forgedRoute.trace := by
  simp [forgedRoute]

/-- The forged route cannot be reinterpreted as an exact run: every run
kernel-proves that its terminal partner is absent from its recursive trace. -/
example :
    ¬ Nonempty
      (FreshSourceLeftRun forgedCertificate forgedState
        forgedCertificate.formulas.size forgedTags 0 [0, 1] 1 0 0) := by
  rintro ⟨run⟩
  exact run.partner_not_mem_trace (by simp)

/-- The source-region API derives precisely the operational enqueue guard
from the complete scheduler invariant and future-cell invariant. -/
example {certificate : Certificate}
    {before : ProofNetIR.SequentialSchedulerBridge.ReservationState}
    (input : ProofNetIR.SequentialFigure7.NewSourceRegionInput
      certificate before)
    (invariant : ProofNetIR.SequentialSchedulerBridge.SchedulerInvariant
      certificate before)
    (future : ProofNetIR.SequentialFigure7.FutureWaitingUndefined before) :
    ProofNetIR.SequentialSchedulerState.SequentialStackState.OperationalNewReadyAt
      input.guard.head.markedStack
      input.guard.head.rawAge input.reached input.partner :=
  input.operationalNewReadyAt invariant future

/-- The same source-region witness packages into the existing input-only
enabledness predicate without assuming an executor result or reachability. -/
example {certificate : Certificate}
    {before : ProofNetIR.SequentialSchedulerBridge.ReservationState}
    (input : ProofNetIR.SequentialFigure7.NewSourceRegionInput
      certificate before)
    (invariant : ProofNetIR.SequentialSchedulerBridge.SchedulerInvariant
      certificate before)
    (future : ProofNetIR.SequentialFigure7.FutureWaitingUndefined before) :
    ProofNetIR.SequentialFigure7.NewEnabled certificate before :=
  input.newEnabled invariant future

end ProofNetIRNewRegionTests

def main : IO Unit :=
  IO.println "Figure-7 new source-region regressions passed"
