import ProofNetIR

open Lean ProofNetIR

namespace ProofNetIRSearchCorpus

/-- Held-out bases for the equal-information matched search: fresh seeds
disjoint from every committed corpus, forty per depth at depths 2, 3, and 4
(8, 16, and 32 atom occurrences). The Python builder collapses labels and
derives the certified negatives. -/
def basesPerDepth : Nat := 40

def seedOffset : Nat := 20_000

def run : IO Unit := do
  let mut index := 0
  for depth in [2, 3, 4] do
    for offset in List.range basesPerDepth do
      let seed := seedOffset + index
      let tree := CutFreeDerivation.generate seed depth
      let some elaborated := tree.elaborate?
        | throw <| IO.userError s!"invalid generated base at seed {seed}"
      IO.println (Json.mkObj [
        ("id", s!"search-base-{index}"),
        ("seed", seed),
        ("depth", depth),
        ("offset", offset),
        ("sequent", .arr (elaborated.sequent.toArray.map Certificate.formulaJson))]).compress
      index := index + 1

end ProofNetIRSearchCorpus

def main : IO Unit := ProofNetIRSearchCorpus.run
