import ProofNetIR.SequentialFigure7QueueHistory

namespace ProofNetIRQueueHistoryTests

open ProofNetIR
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialUnification

def p : Formula := .atom "p" true

def pDual : Formula := p.dual

/-- The smallest structurally valid certificate, used with the submitted right
endpoint as the initial search start. -/
def storedRightCertificate : Certificate where
  formulas := #[p, pDual]
  links := [.axiom 0 1]
  conclusions := [0, 1]

theorem storedRightCertificate_structural :
    storedRightCertificate.StructurallyWellFormed :=
  storedRightCertificate.wellFormed_iff_structurallyWellFormed.mp (by decide)

def storedRightState : UnificationState :=
  storedRightCertificate.initialUnificationState

def storedRightTags : Array Bool :=
  Array.replicate storedRightCertificate.formulas.size false

def storedRightSource : SourceIncidence where
  linkIndex := 0
  link := .axiom 0 1

/-- Concrete proof-relevant terminal orientation: the run starts at the
submitted right endpoint `1`, reaches `1`, and returns stored-left partner `0`.
All fields are checked directly by the kernel. -/
def storedRightRun :
    FreshSourceLeftRun storedRightCertificate storedRightState 1
      storedRightTags 1 [1] 1 0 0 :=
  .axiomRight (certificate := storedRightCertificate)
    (state := storedRightState) (fuel := 0) (tags := storedRightTags)
    (linkIndex := 0) (left := 0) (right := 1)
    storedRightSource (by decide) rfl rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide)

example : storedRightTags[0]? = some false :=
  storedRightRun.partnerFresh

/-- The exact right axiom endpoint in that initialized queue is accounted for
by the canonical touch history. -/
example {after : ReservationState}
    (equation :
      initializeReservation? storedRightCertificate 1 = some after)
    (queued : 1 ∈ after.stack.queuedVertices) :
    ∃ step : InitialReservationStep storedRightCertificate after 1,
      (CanonicalTagHistory.init step).Touched 1 := by
  rcases initializeReservation?_some_iff.mp equation with ⟨step⟩
  refine ⟨step, ?_⟩
  exact (CanonicalTagHistory.init step).queued_axiom_endpoint_touched
    (axiomIndex := 0) (left := 0) (right := 1) (endpoint := 1)
    storedRightCertificate_structural rfl (Or.inr rfl) queued

/- The principal history-indexed bridge is consumable without a separately
supplied `FutureWaitingUndefined` hypothesis. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state) :
    NewEnabled certificate state ↔ NewInputNecessary certificate state :=
  tagHistory.newEnabled_iff_inputNecessary invariant

/- The reachable facade retains the exact-route premise and therefore does not
state `NewGuard` sufficiency or dispatcher progress. -/
example {certificate : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate state)
    (structural : certificate.StructurallyWellFormed) :
    NewEnabled certificate state ↔ NewInputNecessary certificate state :=
  reachable.newEnabled_iff_inputNecessary structural

end ProofNetIRQueueHistoryTests

def main : IO Unit :=
  IO.println "Figure-7 exact axiom-endpoint queue history regressions passed"
