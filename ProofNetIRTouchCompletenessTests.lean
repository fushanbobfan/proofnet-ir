import ProofNetIR.SequentialFigure7TouchCompleteness

namespace ProofNetIR.SequentialFigure7

open SequentialUnification

#check FreshSourceLeftRun.sourceLeftRegion_touched
#check ReservationEvent.sourceLeftRegion_touched
#check ReservationEvent.touched_iff_sourceLeftRegion

example
    {certificate : Certificate} {state : UnificationState}
    {fuel : Nat} {tags : Array Bool}
    {start reached partner vertex : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (structural : certificate.StructurallyWellFormed)
    (run : FreshSourceLeftRun certificate state fuel tags start trace
      reached partner linkIndex)
    (region : SourceLeftRegionVertex certificate start vertex) :
    vertex ∈ trace ∨ vertex = partner :=
  FreshSourceLeftRun.sourceLeftRegion_touched structural run region

example
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (event : ReservationEvent certificate)
    {vertex : Vertex}
    (region : SourceLeftRegionVertex certificate event.start vertex) :
    event.Touched vertex :=
  ReservationEvent.sourceLeftRegion_touched structural event region

example
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (event : ReservationEvent certificate)
    {vertex : Vertex} :
    event.Touched vertex ↔
      SourceLeftRegionVertex certificate event.start vertex :=
  ReservationEvent.touched_iff_sourceLeftRegion structural event

end ProofNetIR.SequentialFigure7

def main : IO Unit :=
  IO.println "Figure-7 touch-completeness API consumer passed"
