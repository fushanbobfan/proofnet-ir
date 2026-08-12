/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialComponentSourceLeftGeometry

/-! Runnable API checks for occurrence-derivation source-left ownership geometry. -/

namespace ProofNetIR

open SequentialUnification

#check Certificate.OccurrenceDerivation.sourceLeftRegion_owned

example
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      certificate.OccurrenceDerivation tree frontier usedLinks owned)
    {source vertex : Vertex}
    (sourceOwned : source ∈ owned)
    (region : SourceLeftRegionVertex certificate source vertex) :
    vertex ∈ owned :=
  witness.sourceLeftRegion_owned structural sourceOwned region

example
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      certificate.OccurrenceDerivation tree frontier usedLinks owned)
    {source vertex : Vertex}
    (sourceOwned : source ∈ owned)
    (region : SourceLeftRegionVertex certificate source vertex) :
    ∃ carrier, carrier = owned ∧ vertex ∈ carrier := by
  refine ⟨owned, rfl, ?_⟩
  exact witness.sourceLeftRegion_owned structural sourceOwned region

end ProofNetIR

def main : IO Unit :=
  IO.println "Sequential source-left geometry consumer passed."
