import ProofNetIR.SequentialFigure7PriorityEnabled

/-!
This compile-only sentinel protects the narrow priority-module import surface.
It ensures the acyclic core retains compatibility helpers that historically
arrived with the enabledness implementation, without relying on the umbrella
module or the wider `SequentialFigure7NewEnabled` facade.
-/

#check ProofNetIR.SequentialFigure7.NewExecutableEnabled.inputNecessary
#check ProofNetIR.SequentialFigure7.new?_exists_schedulerInvariant_of_enabled

def main : IO Unit :=
  IO.println "Figure-7 priority-enabled direct-import compatibility passed"
