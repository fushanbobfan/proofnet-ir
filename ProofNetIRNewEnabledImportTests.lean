import ProofNetIR.SequentialFigure7NewEnabled

/-!
This compile-only sentinel protects the historical direct-import surface of
`SequentialFigure7NewEnabled`.  In particular, callers that imported only that
module before the input-only priority migration could also name the priority
classifier and its necessary-input projection.
-/

#check ProofNetIR.SequentialFigure7.NewEnabled
#check ProofNetIR.SequentialFigure7.NewExecutableEnabled
#check ProofNetIR.SequentialFigure7.PriorityEnabled
#check ProofNetIR.SequentialFigure7.PriorityEnabled.newInputNecessary

def main : IO Unit :=
  IO.println "Figure-7 new-enabled direct-import compatibility passed"
