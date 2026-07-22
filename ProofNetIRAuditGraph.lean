import ProofNetIR

open ProofNetIR

namespace ProofNetIRAuditGraph

def candidateEdges (vertexCount : Nat) : List Edge :=
  (List.range vertexCount).flatMap fun first =>
    (List.range vertexCount).filterMap fun second =>
      if first < second then some { first, second } else none

def edgesForMask (candidates : List Edge) (mask : Nat) : List Edge :=
  candidates.zipIdx.filterMap fun (edge, index) =>
    if mask.testBit index then some edge else none

def run : IO Unit := do
  for vertexCount in List.range 7 do
    let candidates := candidateEdges vertexCount
    let caseCount := 2 ^ candidates.length
    for mask in List.range caseCount do
      let graph : Graph :=
        { vertexCount
          edges := edgesForMask candidates mask }
      IO.println s!"{vertexCount}\t{mask}\t{if graph.isTree then 1 else 0}"

end ProofNetIRAuditGraph

def main : IO Unit := ProofNetIRAuditGraph.run
