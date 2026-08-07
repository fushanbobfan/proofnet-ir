import ProofNetIR.SequentialFigure7TouchOrigin

namespace ProofNetIRTouchOriginTests

open ProofNetIR
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialUnification

/- Every trace member is exposed as an exact source-left reachable vertex. -/
example {certificate : Certificate} {trace : List Vertex}
    {source vertex : Vertex}
    (chain : SourceLeftChain certificate trace)
    (head : trace.head? = some source)
    (membership : vertex ∈ trace) :
    SourceLeftReachable certificate source vertex :=
  chain.reachable_of_head_mem head membership

/- One exact search route covers trace vertices and both returned axiom
endpoints in its complete source-left region. -/
example {certificate : Certificate} {state : UnificationState} {fuel : Nat}
    {inputTags : Array Bool} {start reached partner vertex : Vertex}
    {result : NextAxiomResult certificate state fuel inputTags}
    (route : NextAxiomRoute start result reached partner)
    (touched : result.Touched vertex) :
    SourceLeftRegionVertex certificate start vertex :=
  route.touched_sourceLeftRegion touched

/- Global canonical touch membership recovers an exact historical search
event, without selecting a current component owner. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {vertex : Vertex}
    (touched : tagHistory.Touched vertex) :
    Nonempty (CanonicalTouchOrigin certificate tagHistory vertex) :=
  tagHistory.touched_nonempty_origin touched

/- Every exact origin exposes a submitted historical reservation and its
complete old source-left region. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {vertex : Vertex}
    (origin : CanonicalTouchOrigin certificate tagHistory vertex) :
    ∃ start reached partner linkIndex,
      linkIndex ∈ tagHistory.linkIndices ∧
        SourceLeftRegionVertex certificate start vertex ∧
        SourceLeftReachable certificate start reached ∧
        (certificate.links[linkIndex]? =
            some (.axiom reached partner) ∨
          certificate.links[linkIndex]? =
            some (.axiom partner reached)) :=
  origin.reservationRegion

end ProofNetIRTouchOriginTests

def main : IO Unit :=
  IO.println "Figure-7 canonical touch-origin consumers passed"
