/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderRawMarkedRegionNewPreservation

namespace ProofNetIR

/-!
# API consumer for Figure-7 new raw-marked region preservation

The examples below use every public declaration added by the imported module.
They exercise the exact retained-mark side condition and do not assume that it
follows from scheduler reachability or canonical tag history.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge
open SequentialUnification

#check NewRetainedRawMarksSeparated
#check NewStep.created_sourceRegion_not_selected_of_structural_acyclic
#check NewStep.created_sourceRegion_not_selected
#check NewStep.no_middle_futureWork_at_fresh
#check NewStep.retained_mark_strictly_older_than_fresh
#check NewStep.created_rawMarksSeparatedFrom_of_retained
#check NewStep.olderRawMarkedRegionSeparated

example
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (clear :
      ∀ (created : NewCreatedCandidate certificate step) rawAge vertex,
        before.core.marks[vertex]? = some (some rawAge) →
          ¬ SourceLeftRegionVertex certificate created.tensor.mate vertex) :
    NewRetainedRawMarksSeparated step := by
  intro created rawAge vertex marked _older
  exact clear created rawAge vertex marked

example
    {certificate : Certificate} {before after : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (acyclic : certificate.referenceSwitchingGraph.Acyclic)
    (step : NewStep certificate before after)
    (created : NewCreatedCandidate certificate step) :
    ¬ SourceLeftRegionVertex certificate created.tensor.mate
      step.stackResult.vertex :=
  step.created_sourceRegion_not_selected_of_structural_acyclic
    structural acyclic created

example
    {certificate : Certificate} {before after : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    (step : NewStep certificate before after)
    (created : NewCreatedCandidate certificate step) :
    ¬ SourceLeftRegionVertex certificate created.tensor.mate
      step.stackResult.vertex :=
  step.created_sourceRegion_not_selected correct created

example
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex} :
    ¬ FutureWorkAt step.markedMiddle (ReservationEvent.new step).rawAge
      vertex :=
  step.no_middle_futureWork_at_fresh invariant

example
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (marked : before.core.marks[vertex]? = some (some rawAge)) :
    step.markedMiddle.core.representative rawAge <
      step.markedMiddle.core.representative
        (ReservationEvent.new step).rawAge :=
  step.retained_mark_strictly_older_than_fresh invariant marked

example
    {certificate : Certificate} {before after : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    (step : NewStep certificate before after)
    (retained : NewRetainedRawMarksSeparated step)
    (created : NewCreatedCandidate certificate step) :
    OlderRawMarksSeparatedFrom certificate step.markedMiddle
      (ReservationEvent.new step).rawAge created.tensor.mate :=
  step.created_rawMarksSeparatedFrom_of_retained correct retained created

example
    {certificate : Certificate} {before after : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (separated : OlderRawMarkedRegionSeparated certificate before)
    (createdSeparated : NewRetainedRawMarksSeparated step) :
    OlderRawMarkedRegionSeparated certificate after :=
  step.olderRawMarkedRegionSeparated correct invariant separated
    createdSeparated

end SequentialFigure7

end ProofNetIR

/-- Run the standalone API consumer smoke test. -/
def main : IO Unit :=
  IO.println "Figure-7 new raw-marked region preservation consumer passed."
