/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderRawMarkedRegionWaitPreservation

namespace ProofNetIR

/-!
# API consumer for Figure-7 wait raw-marked region preservation

The examples below check and invoke every public declaration added by the
imported module.  They keep the retained-mark side condition explicit.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge
open SequentialUnification

#check WaitRetainedRawMarksSeparated
#check WaitStep.destination_representative_lt_selected
#check WaitStep.created_rawMarksSeparatedFrom_of_retained
#check WaitStep.olderRawMarkedRegionSeparated

example
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (clear :
      ∀ created : WaitCreatedCandidate certificate step,
        OlderRawMarksSeparatedFrom certificate before
          step.destination.boundary created.tensor.mate) :
    WaitRetainedRawMarksSeparated step :=
  clear

example
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after) :
    step.prepared.after.core.representative step.destination.boundary <
      step.prepared.after.core.representative
        step.prepared.stackResult.rawAge :=
  step.destination_representative_lt_selected

example
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (retained : WaitRetainedRawMarksSeparated step)
    (created : WaitCreatedCandidate certificate step) :
    OlderRawMarksSeparatedFrom certificate step.prepared.after
      step.destination.boundary created.tensor.mate :=
  step.created_rawMarksSeparatedFrom_of_retained retained created

example
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (separated : OlderRawMarkedRegionSeparated certificate before)
    (retained : WaitRetainedRawMarksSeparated step) :
    OlderRawMarkedRegionSeparated certificate after :=
  step.olderRawMarkedRegionSeparated invariant separated retained

end SequentialFigure7

end ProofNetIR

/-- Run the standalone API consumer smoke test. -/
def main : IO Unit :=
  IO.println "Figure-7 Wait raw-marked region preservation consumer passed."
