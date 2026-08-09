/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderRawMarkedRegionForwardPreservation

namespace ProofNetIR

/-!
# API consumer for Figure-7 forward raw-marked region preservation

The examples below check and invoke every public declaration added by the
imported module. They keep the retained-mark side condition explicit.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge
open SequentialUnification

#check ForwardRetainedRawMarksSeparated
#check ForwardStep.created_rawMarksSeparatedFrom_of_retained
#check ForwardStep.olderRawMarkedRegionSeparated

example
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (clear :
      ∀ created : ForwardCreatedCandidate certificate step,
        OlderRawMarksSeparatedFrom certificate before
          step.prepared.stackResult.rawAge created.tensor.mate) :
    ForwardRetainedRawMarksSeparated step :=
  clear

example
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (retained : ForwardRetainedRawMarksSeparated step)
    (created : ForwardCreatedCandidate certificate step) :
    OlderRawMarksSeparatedFrom certificate step.prepared.after
      step.prepared.stackResult.rawAge created.tensor.mate :=
  step.created_rawMarksSeparatedFrom_of_retained retained created

example
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (separated : OlderRawMarkedRegionSeparated certificate before)
    (retained : ForwardRetainedRawMarksSeparated step) :
    OlderRawMarkedRegionSeparated certificate after :=
  step.olderRawMarkedRegionSeparated invariant separated retained

end SequentialFigure7

end ProofNetIR

/-- Run the standalone API consumer smoke test. -/
def main : IO Unit :=
  IO.println "Figure-7 Forward raw-marked region preservation consumer passed."
