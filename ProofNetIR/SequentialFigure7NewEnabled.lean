import ProofNetIR.SequentialFigure7NewEnabledCore
import ProofNetIR.SequentialFigure7NewInputNecessary

/-!
# Compatibility facade for Figure-7 `new` enabledness

The declarations implemented by this historical module now live in
`SequentialFigure7NewEnabledCore`, which the priority classifier can import
without a cycle.  Importing `SequentialFigure7NewEnabled` deliberately retains
the pre-migration transitive surface: it exposes the input-only enabledness
API, `PriorityEnabled`, and `PriorityEnabled.newInputNecessary`.
-/
