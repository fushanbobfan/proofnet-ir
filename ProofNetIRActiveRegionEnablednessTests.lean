/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveRegionEnabledness

/-!
# Figure-7 active-region enabledness consumer

Exercises every public layer of the local active-region enabledness API.
-/

namespace ProofNetIR

open SequentialFigure7
open SequentialSchedulerBridge
open SequentialUnification

#check CanonicalTagHistory.active_sourceLeftRegion_no_rawMark
#check CanonicalTagHistory.active_sourceLeftRegion_no_exactMarkedOwner
#check CanonicalTagHistory.active_sourceLeftRegion_tagFresh
#check CanonicalTagHistory.active_newSourceRegionInput
#check CanonicalTagHistory.active_newEnabled

example {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before) :
    (∀ {vertex},
      SourceLeftRegionVertex certificate guard.tensor.mate vertex →
        ¬ ∃ rawAge, before.core.marks[vertex]? = some (some rawAge)) ∧
      (∀ {vertex},
        SourceLeftRegionVertex certificate guard.tensor.mate vertex →
          ¬ ExactMarkedOccurrenceOwner certificate before.core vertex) ∧
      (∀ {vertex},
        SourceLeftRegionVertex certificate guard.tensor.mate vertex →
          before.tags[vertex]? = some false) ∧
      Nonempty (NewSourceRegionInput certificate before) ∧
      NewEnabled certificate before := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro vertex region
    exact tagHistory.active_sourceLeftRegion_no_rawMark
      correct invariant guard region
  · intro vertex region
    exact tagHistory.active_sourceLeftRegion_no_exactMarkedOwner
      correct invariant guard region
  · intro vertex region
    exact tagHistory.active_sourceLeftRegion_tagFresh
      correct invariant guard region
  · exact tagHistory.active_newSourceRegionInput correct invariant guard
  · exact tagHistory.active_newEnabled correct invariant guard

end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 active-region enabledness API consumer passed."
