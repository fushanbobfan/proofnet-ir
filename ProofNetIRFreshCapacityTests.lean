import ProofNetIR.SequentialFigure7FreshCapacity

namespace ProofNetIRFreshCapacityTests

open ProofNetIR
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialUnification

/- Compile-only consumer fixture: structural well-formedness publicly bounds
the submitted-link carrier by the formula-occurrence carrier. -/
example {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) :
    certificate.links.length ≤ certificate.formulas.size :=
  structural.links_length_le_formulas_size

/- The capacity theorem consumes only an already-successful canonical tag
history, structural well-formedness, and an exact run over the final state's
input tags.  It does not request a reachability or progress hypothesis. -/
example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed)
    {fuel : Nat} {start reached partner : Vertex}
    {trace : List Vertex} {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate state.core fuel state.tags start
      trace reached partner linkIndex) :
    state.stack.nextAge < certificate.formulas.size :=
  tagHistory.fresh_terminal_capacity structural run

end ProofNetIRFreshCapacityTests

def main : IO Unit :=
  IO.println "Figure-7 fresh terminal capacity consumer fixture passed"
