import ProofNetIR.SequentialFigure7PriorityEnabled
import ProofNetIR.SequentialFigure7NewInputCore

namespace ProofNetIR

/-!
# Compatibility facade for Figure-7 `new` input conditions

The lower-layer declarations live in `SequentialFigure7NewInputCore` so that
the input-only `NewEnabled` predicate can feed the priority classifier without
an import cycle.  This module retains the historical import surface and the
priority-to-necessary projection.
-/

namespace SequentialFigure7

open SequentialSchedulerBridge

/-- A priority-selected `new` branch contains the complete input-only
enabledness witness, and therefore also the deliberately weaker necessary
input projection. -/
theorem PriorityEnabled.newInputNecessary
    {certificate : Certificate} {before : ReservationState}
    {invariant : SchedulerInvariant certificate before}
    (enabled : PriorityEnabled certificate before invariant .new) :
    NewInputNecessary certificate before :=
  enabled.newEnabled.inputNecessary

end SequentialFigure7

end ProofNetIR
