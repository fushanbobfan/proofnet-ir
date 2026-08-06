import ProofNetIR

namespace ProofNetIR

open SequentialSchedulerState
open SequentialSchedulerBridge

namespace TensorAdjacencyTests

private def p : Formula := .atom "p" true
private def pDual : Formula := .atom "p" false

/-- A single axiom whose two endpoints are also the premises of one tensor.

The certificate is structurally well formed but rejected by the proof-net
checker: retaining both tensor premises closes a cycle through the axiom.  It
is deliberately outside the correct-certificate and certified-reachability
claims used by the sequentialization pipeline. -/
private def singletonSigmaCertificate : Certificate where
  formulas := #[p, pDual, .tensor p pDual]
  links := [
    .axiom 0 1,
    .tensor 0 1 2
  ]
  conclusions := [2]

private theorem singletonSigmaCertificate_structural :
    singletonSigmaCertificate.StructurallyWellFormed := by
  exact
    (Certificate.wellFormed_iff_structurallyWellFormed
      singletonSigmaCertificate).mp (by decide)

example : singletonSigmaCertificate.check = false := by
  decide

/-- Exact successful initialization of the sole submitted axiom.  The closed
equation below is discharged by `native_decide`, so this fixture is an
executable regression outside the public three-axiom theorem boundary. -/
private def singletonSigmaInitial : ReservationState where
  stack := {
    marks := #[none, none, none]
    nextAge := 1
    sigma := [0]
    ready := [[0, 1]]
    waiting := Array.replicate 3 .undefined }
  core := {
    marks := #[none, none, none]
    parents := #[0]
    components := #[some {
      tree := .axiom "p" true
      frontier := [0, 1] }]
    startedAxioms := 1
    firedConnectives := 0 }
  tags := #[true, true, false]

private theorem singletonSigmaInitial_equation :
    initializeReservation? singletonSigmaCertificate 0 =
      some singletonSigmaInitial := by
  native_decide

private theorem singletonSigmaInitial_schedulerInvariant :
    SchedulerInvariant singletonSigmaCertificate singletonSigmaInitial := by
  rcases initializeReservation?_some_iff.mp
      singletonSigmaInitial_equation with ⟨step⟩
  exact step.schedulerInvariant singletonSigmaCertificate_structural

/-- Select the first axiom endpoint for the shared pop/raw-mark prefix. -/
private def singletonSigmaInitialHead :
    SequentialFigure7.ReadyHeadInput singletonSigmaInitial where
  vertex := 0
  readyTail := [1]
  rawAge := 0
  top_ready := by decide
  sigma_top := by decide

private def singletonSigmaPrepared :
    SequentialFigure7.PreparedStep singletonSigmaInitial where
  stackResult := singletonSigmaInitialHead.stackResult
  coreMarked := singletonSigmaInitialHead.markedCore
  stack_eq :=
    singletonSigmaInitialHead.stack_pop_eq
      singletonSigmaInitial_schedulerInvariant
  core_mark_eq :=
    singletonSigmaInitialHead.core_mark_eq
      singletonSigmaInitial_schedulerInvariant

/-- The common prefix marks occurrence `0` at raw age `0` and leaves
occurrence `1` at the head of the sole ready bucket. -/
private def singletonSigmaState : ReservationState :=
  singletonSigmaPrepared.after

private theorem singletonSigmaState_schedulerInvariant :
    SchedulerInvariant singletonSigmaCertificate singletonSigmaState := by
  exact singletonSigmaPrepared.schedulerInvariant
    singletonSigmaInitial_schedulerInvariant

private def singletonSigmaHead :
    SequentialFigure7.ReadyHeadInput singletonSigmaState where
  vertex := 1
  readyTail := []
  rawAge := 0
  top_ready := by decide
  sigma_top := by decide

private def singletonSigmaTensor :
    ConnectiveBelow singletonSigmaCertificate singletonSigmaHead.vertex where
  linkIndex := 1
  kind := .tensor
  storedLeft := 0
  storedRight := 1
  conclusion := 2
  side := .storedRight
  consumer_eq := by decide
  link_eq := by decide
  wellFormed := by
    exact
      (singletonSigmaCertificate.linkLocallyWellFormed_iff
        (.tensor 0 1 2)).mp (by decide)
  premise_eq := rfl

private theorem singletonSigmaTensor_marked :
    singletonSigmaState.core.marks[singletonSigmaTensor.mate]? =
      some (some 0) := by
  decide

/-- The predecessor witness fails exactly because `[0].dropLast = []`. -/
private theorem singletonSigma_no_predecessor :
    ¬ ∃ previousBoundary,
      Nonempty
        (SequentialFigure7.SigmaPredecessorInput [0] 0 0
          previousBoundary) := by
  rintro ⟨previousBoundary, ⟨adjacency⟩⟩
  simpa using adjacency.previous_top

/-- A singleton sigma stack cannot satisfy the two-level input shape of
arbitrary-payload unification, independently of executor behavior. -/
private theorem singletonSigma_not_unifyPayloadEnabled :
    ¬ SequentialFigure7.UnifyPayloadEnabled
      singletonSigmaCertificate singletonSigmaState := by
  rintro ⟨input⟩
  have lengthEquation := congrArg List.length input.sigma_two_levels
  simp [singletonSigmaState, singletonSigmaPrepared, singletonSigmaInitial,
    SequentialFigure7.PreparedStep.after,
    SequentialFigure7.ReadyHeadInput.stackResult,
    SequentialFigure7.ReadyHeadInput.markedStack] at lengthEquation

/-- The complete state-only invariant plus a ready tensor occurrence and a
marked mate do not by themselves imply unification enabledness.  The missing
fact is precisely the predecessor-boundary relation supplied by
`SigmaPredecessorInput`. -/
private theorem bareMarkedTensor_not_sufficient :
    ¬ (∀ {certificate : Certificate} {before : ReservationState},
      SchedulerInvariant certificate before →
      ∀ (head : SequentialFigure7.ReadyHeadInput before)
        (consumer : ConnectiveBelow certificate head.vertex)
        (mateRawAge : RawTokenAge),
        consumer.kind = .tensor →
        before.core.marks[consumer.mate]? = some (some mateRawAge) →
        SequentialFigure7.UnifyPayloadEnabled certificate before) := by
  intro proposed
  exact singletonSigma_not_unifyPayloadEnabled
    (proposed singletonSigmaState_schedulerInvariant singletonSigmaHead
      singletonSigmaTensor 0 rfl singletonSigmaTensor_marked)

/-- Compile-lock the native-computed counterexample boundary: full state-only
`SchedulerInvariant`, checker rejection, a ready tensor occurrence, and its
marked mate coexist with singleton sigma and failed unification enabledness.
No certified dispatcher reachability or correct-certificate claim is made. -/
example :
    SchedulerInvariant singletonSigmaCertificate singletonSigmaState ∧
      singletonSigmaCertificate.check = false ∧
      Nonempty
        (SequentialFigure7.ReadyHeadInput singletonSigmaState) ∧
      singletonSigmaTensor.kind = .tensor ∧
      singletonSigmaState.core.marks[singletonSigmaTensor.mate]? =
        some (some 0) ∧
      (¬ ∃ previousBoundary,
        Nonempty
          (SequentialFigure7.SigmaPredecessorInput [0] 0 0
            previousBoundary)) ∧
      ¬ SequentialFigure7.UnifyPayloadEnabled
        singletonSigmaCertificate singletonSigmaState := by
  exact ⟨singletonSigmaState_schedulerInvariant, by decide,
    ⟨singletonSigmaHead⟩, rfl, singletonSigmaTensor_marked,
    singletonSigma_no_predecessor,
    singletonSigma_not_unifyPayloadEnabled⟩

#check SequentialFigure7.SigmaPredecessorInput
#check SequentialFigure7.SigmaPredecessorInput.sigma_two_levels
#check SequentialFigure7.markedTensor_unifyPayloadEnabled
#check bareMarkedTensor_not_sufficient

end TensorAdjacencyTests

end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 marked-tensor adjacency regressions passed"
