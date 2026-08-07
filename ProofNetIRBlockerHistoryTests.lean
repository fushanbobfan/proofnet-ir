import ProofNetIR.SequentialFigure7BlockerHistory

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
