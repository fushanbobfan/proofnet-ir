/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderRawMarkedRegionUnifyPayloadPreservation

namespace ProofNetIR

/-!
# API consumer for Figure-7 UnifyPayload raw-marked region preservation

The examples below check and invoke both public declarations added by the
imported module. The created-candidate residual premise remains explicit.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge
open SequentialUnification

#check UnifyPayloadCreatedRawMarksSeparated
#check UnifyPayloadStep.olderRawMarkedRegionSeparated

example
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (contract :
      ∀ created : UnifyPayloadCreatedCandidate certificate step,
        OlderRawMarksSeparatedFrom certificate step.prepared.after
          step.previousBoundary created.tensor.mate) :
    UnifyPayloadCreatedRawMarksSeparated step :=
  contract

example
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (separated : OlderRawMarkedRegionSeparated certificate before)
    (createdSeparated : UnifyPayloadCreatedRawMarksSeparated step) :
    OlderRawMarkedRegionSeparated certificate after :=
  step.olderRawMarkedRegionSeparated invariant separated createdSeparated

end SequentialFigure7

end ProofNetIR

/-- Run the standalone API consumer smoke test. -/
def main : IO Unit :=
  IO.println "Figure-7 UnifyPayload raw-marked region preservation consumer passed."
