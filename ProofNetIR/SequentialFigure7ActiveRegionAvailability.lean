import ProofNetIR.SequentialFigure7ActiveRegionTouchOrder

namespace ProofNetIR

/-!
# Figure-7 active-region availability reduction

This module reduces the remaining dynamic availability question for an active
`NewGuard` source-left region to one occurrence-exact old-owner obstruction.
Under declarative correctness, the scheduler invariant, and older-event touch
separation, structural search either supplies an exact source-left run or a
dynamic blocker.  The active-region tag theorem excludes the prior-touch
blocker; exact old component ownership is the only remaining alternative.

The successful branch packages the existing route/run readiness, endpoint
queue absence, and waiting capacity into `NewSourceRegionInput`.  The exact
history separately supplies the future-cell invariant used to obtain
`NewEnabled`.  The module does not exclude the old-owner alternative,
establish older-event touch separation for every history, discharge any
created-region preservation premise, or prove dispatcher progress, totality,
worklist completeness, fallback removal, or whole-program linearity.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

/-- For an active `NewGuard`, exact source-region availability fails only at
an occurrence with an old proof-relevant live-component owner.

The left branch includes the exact run, endpoint readiness, endpoint queue
absence, and fresh waiting capacity.  The right branch is not excluded here.
-/
theorem CanonicalTagHistory.active_newSourceRegionInput_or_exactMarkedOwner
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (separated : OlderEventTouchSeparated tagHistory) :
    Nonempty (NewSourceRegionInput certificate before) ∨
      ∃ vertex,
        SourceLeftRegionVertex certificate guard.tensor.mate vertex ∧
          ExactMarkedOccurrenceOwner certificate before.core vertex := by
  rcases invariant.structural.freshSourceLeftRun_or_blocker
      guard.mate_bound with run | blocker
  · rcases run with ⟨trace, reached, partner, linkIndex, run⟩
    rcases run with ⟨run⟩
    exact Or.inl
      ⟨tagHistory.newSourceRegionInputOfRun invariant guard run⟩
  · rcases blocker with ⟨blocker⟩
    rcases
        tagHistory.classifyFreshSourceBlocker_of_declarativelyCorrect
          correct invariant guard blocker with touched | owner
    · have fresh :=
        tagHistory.active_sourceLeftRegion_tagFresh_of_olderEventTouchSeparated
          correct invariant guard separated blocker.region
      have tagged : before.tags[blocker.vertex]? = some true :=
        tagHistory.tagged_iff_touched.2 touched
      rw [tagged] at fresh
      simp at fresh
    · exact Or.inr ⟨blocker.vertex, blocker.region, owner⟩

/-- Under the same active-region assumptions, input-only `new` enabledness
fails only at an exact old marked occurrence owner.

This theorem is a dichotomy, not an unconditional enabledness result.
-/
theorem CanonicalTagHistory.active_newEnabled_or_exactMarkedOwner
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (separated : OlderEventTouchSeparated tagHistory) :
    NewEnabled certificate before ∨
      ∃ vertex,
        SourceLeftRegionVertex certificate guard.tensor.mate vertex ∧
          ExactMarkedOccurrenceOwner certificate before.core vertex := by
  rcases
      tagHistory.active_newSourceRegionInput_or_exactMarkedOwner
        correct invariant guard separated with input | owner
  · rcases input with ⟨input⟩
    exact Or.inl (input.newEnabled invariant history.futureWaitingUndefined)
  · exact Or.inr owner

/-- If the active source-left region has no exact old marked owner, the
history-indexed active guard is input-only `NewEnabled`.

The explicit owner-clear premise is the remaining mathematical gate; this
corollary does not derive it from touch separation or the scheduler invariant.
-/
theorem CanonicalTagHistory.active_newEnabled_of_no_exactMarkedOwner
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (separated : OlderEventTouchSeparated tagHistory)
    (clearOwner :
      ∀ {vertex},
        SourceLeftRegionVertex certificate guard.tensor.mate vertex →
          ¬ ExactMarkedOccurrenceOwner certificate before.core vertex) :
    NewEnabled certificate before := by
  rcases
      tagHistory.active_newEnabled_or_exactMarkedOwner
        correct invariant guard separated with enabled | owner
  · exact enabled
  · rcases owner with ⟨vertex, region, owner⟩
    exact (clearOwner region owner).elim

end SequentialFigure7

end ProofNetIR
