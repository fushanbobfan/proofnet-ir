/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7EndpointLocalityObstruction

/-!
# Consumer for the wait-output endpoint-locality obstruction

This consumer applies the public theorem to turn an assumed output-locality receipt into `False`,
audits its trusted dependencies, and provides a runnable smoke-test entry point.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

private theorem consumeWaitOutputObstruction
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (localized : ActiveTopContinuationExitLocalized certificate after) : False :=
  step.not_activeTopContinuationExitLocalized invariant localized

#print axioms WaitStep.not_activeTopContinuationExitLocalized

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 wait-output endpoint-locality obstruction: kernel-green"
