import ProofNetIR

open ProofNetIR

namespace ProofNetIRBenchmark

def benchmarkTrees : List CutFreeDerivation :=
  ((List.range 250).map fun seed => CutFreeDerivation.generate seed 2) ++
  ((List.range 40).map fun seed => CutFreeDerivation.generate (1_000 + seed) 3) ++
  [CutFreeDerivation.generate 2_000 4]

def budgetMs : Nat := 45_000

def run : IO Unit := do
  let start ← IO.monoMsNow
  let mut checksum := 0
  let mut completed := 0
  let mut checkMs := 0
  let mut sequentializeMs := 0
  let mut equivalenceMs := 0
  for tree in benchmarkTrees do
    let certificate ← match tree.desequentialize? with
      | none => throw <| IO.userError "benchmark tree failed to desequentialize"
      | some value => pure value
    let checkStart ← IO.monoMsNow
    let checked := certificate.check
    checkMs := checkMs + ((← IO.monoMsNow) - checkStart)
    if !checked then
      throw <| IO.userError "benchmark generated a rejected certificate"
    let input := if completed % 2 == 0 then
      { certificate with links := certificate.links.reverse }
    else
      certificate
    let sequentializeStart ← IO.monoMsNow
    let result ← match input.sequentialize with
      | .error error => throw <| IO.userError s!"benchmark sequentialization failed: {error.render}"
      | .ok value => pure value
    sequentializeMs := sequentializeMs + ((← IO.monoMsNow) - sequentializeStart)
    let equivalenceStart ← IO.monoMsNow
    let equivalent := Certificate.proofNetEquivalent? result.output input
    equivalenceMs := equivalenceMs + ((← IO.monoMsNow) - equivalenceStart)
    if !equivalent then
      throw <| IO.userError "benchmark equivalence decision rejected a sequentialization result"
    checksum := checksum + result.output.formulas.size + result.output.links.length +
      result.sequent.length
    completed := completed + 1
  let elapsed := (← IO.monoMsNow) - start
  if elapsed > budgetMs then
    throw <| IO.userError s!"performance budget exceeded: {elapsed}ms > {budgetMs}ms"
  IO.println s!"performance-budget-ok cases={completed} checksum={checksum} elapsed_ms={elapsed} check_ms={checkMs} sequentialize_ms={sequentializeMs} equivalence_ms={equivalenceMs} budget_ms={budgetMs}"

end ProofNetIRBenchmark

def main : IO Unit := ProofNetIRBenchmark.run
