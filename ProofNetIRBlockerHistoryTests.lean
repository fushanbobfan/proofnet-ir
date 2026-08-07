import ProofNetIR.SequentialFigure7TerminalPartnerGeometry
import ProofNetIR.AcyclicDecision

namespace ProofNetIRBlockerHistoryTests

open ProofNetIR
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialUnification

/- The complete component forest exposes a proof-relevant live owner for
every concrete raw-marked occurrence. -/
example {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {vertex rawAge : Nat}
    (marked : state.core.marks[vertex]? = some (some rawAge)) :
    ExactMarkedOccurrenceOwner certificate state.core vertex :=
  SchedulerInvariant.exactMarkedOccurrenceOwner invariant marked

/- Pointwise tag failures retain their exact region witness and classify as a
prior canonical touch. -/
example {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {vertex : Vertex}
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex)
    (blocked : before.tags[vertex]? ≠ some false) :
    tagHistory.Touched vertex :=
  tagHistory.classifyFreshTagBlocker invariant guard region blocked

/- Pointwise raw failures distinguish the pure selected-head update from an
old occurrence-exact live-component owner. -/
example {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {vertex : Vertex}
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex)
    (blocked : guard.head.markedCore.marks[vertex]? ≠ some none) :
    vertex = guard.head.vertex ∨
      ExactMarkedOccurrenceOwner certificate before.core vertex :=
  CanonicalTagHistory.classifyFreshRawBlocker
    invariant guard region blocked

/- Exact source-left reachability cannot return from the tensor mate to the
selected ready head on structurally well-formed input. -/
example {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before) :
    ¬ SourceLeftReachable certificate guard.tensor.mate
        guard.head.vertex :=
  guard.not_sourceLeftReachable_mate_head invariant.structural

/- Consequently the selected-head raw-mark branch disappears for recursively
visited region occurrences, leaving exact old component ownership. -/
example {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {vertex : Vertex}
    (reachable :
      SourceLeftReachable certificate guard.tensor.mate vertex)
    (blocked : guard.head.markedCore.marks[vertex]? ≠ some none) :
    ExactMarkedOccurrenceOwner certificate before.core vertex :=
  CanonicalTagHistory.classifyVisitedFreshRawBlocker
    invariant guard reachable blocked

/- The complete dynamic failure classification on a visited occurrence now
has only canonical prior-touch or exact old-owner branches. -/
example {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {vertex : Vertex}
    (reachable :
      SourceLeftReachable certificate guard.tensor.mate vertex)
    (unavailable :
      before.tags[vertex]? ≠ some false ∨
        guard.head.markedCore.marks[vertex]? ≠ some none) :
    tagHistory.Touched vertex ∨
      ExactMarkedOccurrenceOwner certificate before.core vertex :=
  tagHistory.classifyVisitedFreshBlocker invariant guard reachable unavailable

/- The acyclicity premise below is mathematically necessary.  This certificate
is structurally well formed, but its axiom and tensor form a triangle in the
all-left reference switching.  After initializing the axiom, the tensor mate
terminates at an axiom whose partner is exactly the selected ready head. -/
private def terminalTriangleAtom : Formula := .atom "p" true

private def terminalTriangleCertificate : Certificate where
  formulas := #[terminalTriangleAtom, terminalTriangleAtom.dual,
    .tensor terminalTriangleAtom terminalTriangleAtom.dual]
  links := [.axiom 0 1, .tensor 0 1 2]
  conclusions := [2]

private theorem terminalTriangleCertificate_structural :
    terminalTriangleCertificate.StructurallyWellFormed :=
  terminalTriangleCertificate.wellFormed_iff_structurallyWellFormed.mp
    (by native_decide)

private theorem terminalTriangleCertificate_not_referenceAcyclic :
    ¬ terminalTriangleCertificate.referenceSwitchingGraph.Acyclic := by
  intro acyclic
  have accepted :
      terminalTriangleCertificate.referenceSwitchingGraph.isAcyclic = true :=
    (Graph.isAcyclic_eq_true_iff _).mpr acyclic
  have rejected :
      terminalTriangleCertificate.referenceSwitchingGraph.isAcyclic ≠ true := by
    native_decide
  exact rejected accepted

private def terminalTriangleInitial : Option ReservationState :=
  initializeReservation? terminalTriangleCertificate 0

private def terminalTriangleState : ReservationState :=
  match terminalTriangleInitial with
  | some state => state
  | none => ReservationState.empty terminalTriangleCertificate

private theorem terminalTriangleState_eq :
    terminalTriangleInitial = some terminalTriangleState := by
  native_decide

private def terminalTriangleHead : ReadyHeadInput terminalTriangleState where
  vertex := 0
  readyTail := [1]
  rawAge := 0
  top_ready := by native_decide
  sigma_top := by native_decide

private def terminalTriangleTensor : TensorBelow where
  linkIndex := 1
  storedLeft := 0
  storedRight := 1
  conclusion := 2
  side := .storedLeft

private theorem terminalTriangleTensor_eq :
    terminalTriangleCertificate.tensorBelow? terminalTriangleHead.vertex =
      some terminalTriangleTensor := by
  native_decide

private def terminalTriangleGuard :
    NewGuard terminalTriangleCertificate terminalTriangleState where
  head := terminalTriangleHead
  tensor := terminalTriangleTensor
  tensor_valid :=
    Certificate.tensorBelow?_eq_some_iff.mp terminalTriangleTensor_eq
  mate_unmarked := by native_decide

private theorem terminalTriangle_partner_eq_head :
    ∃ (reached partner : Vertex) (linkIndex : Nat),
      SourceLeftReachable terminalTriangleCertificate
          terminalTriangleGuard.tensor.mate reached ∧
        (terminalTriangleCertificate.links[linkIndex]? =
            some (Link.axiom reached partner) ∨
          terminalTriangleCertificate.links[linkIndex]? =
            some (Link.axiom partner reached)) ∧
        partner = terminalTriangleGuard.head.vertex := by
  refine ⟨1, 0, 0, .refl 1, ?_, ?_⟩
  · exact Or.inr (by native_decide)
  · native_decide

/- Keep every part of the negative boundary compile-checked. -/
example :
    terminalTriangleCertificate.StructurallyWellFormed ∧
      ¬ terminalTriangleCertificate.referenceSwitchingGraph.Acyclic ∧
      ∃ (reached partner : Vertex) (linkIndex : Nat),
        SourceLeftReachable terminalTriangleCertificate
            terminalTriangleGuard.tensor.mate reached ∧
          (terminalTriangleCertificate.links[linkIndex]? =
              some (Link.axiom reached partner) ∨
            terminalTriangleCertificate.links[linkIndex]? =
              some (Link.axiom partner reached)) ∧
          partner = terminalTriangleGuard.head.vertex :=
  ⟨terminalTriangleCertificate_structural,
    terminalTriangleCertificate_not_referenceAcyclic,
    terminalTriangle_partner_eq_head⟩

/- Reference-switching acyclicity eliminates the remaining selected-head
alternative for a terminal axiom partner. -/
example {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (acyclic : certificate.referenceSwitchingGraph.Acyclic)
    (guard : NewGuard certificate before)
    {reached partner : Vertex} {linkIndex : Nat}
    (reachable :
      SourceLeftReachable certificate guard.tensor.mate reached)
    (exactAxiom :
      certificate.links[linkIndex]? = some (.axiom reached partner) ∨
        certificate.links[linkIndex]? = some (.axiom partner reached)) :
    partner ≠ guard.head.vertex :=
  guard.terminalPartner_ne_head invariant.structural acyclic
    reachable exactAxiom

/- Declarative correctness packages the same terminal-partner exclusion. -/
example {certificate : Certificate} {before : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    (guard : NewGuard certificate before)
    {reached partner : Vertex} {linkIndex : Nat}
    (reachable :
      SourceLeftReachable certificate guard.tensor.mate reached)
    (exactAxiom :
      certificate.links[linkIndex]? = some (.axiom reached partner) ∨
        certificate.links[linkIndex]? = some (.axiom partner reached)) :
    partner ≠ guard.head.vertex :=
  guard.terminalPartner_ne_head_of_declarativelyCorrect correct
    reachable exactAxiom

/- Under switching acyclicity, the full raw-blocker classifier has no
selected-head branch for either visited or terminal-partner occurrences. -/
example {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (acyclic : certificate.referenceSwitchingGraph.Acyclic)
    (guard : NewGuard certificate before)
    {vertex : Vertex}
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex)
    (blocked : guard.head.markedCore.marks[vertex]? ≠ some none) :
    ExactMarkedOccurrenceOwner certificate before.core vertex :=
  CanonicalTagHistory.classifyFreshRawBlocker_of_referenceAcyclic
    invariant acyclic guard region blocked

/- Declarative correctness reduces every complete dynamic blocker to prior
canonical touch or exact old live-component ownership. -/
example {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (blocker :
      FreshSourceBlocker certificate guard.head.markedCore before.tags
        guard.tensor.mate) :
    tagHistory.Touched blocker.vertex ∨
      ExactMarkedOccurrenceOwner certificate before.core blocker.vertex :=
  tagHistory.classifyFreshSourceBlocker_of_declarativelyCorrect correct
    invariant guard blocker

/- A combined dynamic blocker classifies into the exact three-way canonical
history obstruction without assuming another search or executor success. -/
example {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (blocker :
      FreshSourceBlocker certificate guard.head.markedCore before.tags
        guard.tensor.mate) :
    CanonicalSourceLeftObstruction tagHistory guard blocker.vertex :=
  tagHistory.classifyFreshSourceBlocker invariant guard blocker

/- Structural classification plus canonical history sharpens failure to a
region-indexed historical/component obstruction. -/
example {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before) :
    (∃ trace reached partner linkIndex,
      Nonempty
        (FreshSourceLeftRun certificate guard.head.markedCore
          certificate.formulas.size before.tags guard.tensor.mate trace
          reached partner linkIndex)) ∨
      ∃ vertex,
        SourceLeftRegionVertex certificate guard.tensor.mate vertex ∧
          CanonicalSourceLeftObstruction tagHistory guard vertex :=
  tagHistory.freshSourceLeftRun_or_obstruction invariant guard

/- Once all three exact obstruction forms are excluded, the existing
input-only `NewEnabled` predicate follows.  The exclusion remains explicit. -/
example {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (clear :
      ∀ {vertex : Vertex},
        SourceLeftRegionVertex certificate guard.tensor.mate vertex →
          ¬ CanonicalSourceLeftObstruction tagHistory guard vertex) :
    NewEnabled certificate before :=
  tagHistory.newEnabled_of_no_sourceLeftObstruction invariant guard clear

end ProofNetIRBlockerHistoryTests

def main : IO Unit :=
  IO.println "Figure-7 canonical blocker-history consumers passed"
