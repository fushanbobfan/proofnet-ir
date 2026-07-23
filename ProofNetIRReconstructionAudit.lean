import ProofNetIR

open ProofNetIR

namespace ProofNetIRReconstructionAudit

def casesForCertificate (certificate : Certificate) :
    List Certificate :=
  [ certificate,
    Mutation.dropFirstLink.apply certificate,
    Mutation.duplicateFirstLink.apply certificate,
    (Mutation.replaceFirstAxiomRight 0).apply certificate ]

def budgetMs : Nat := 15_000

/-- Differential runtime qualification for the theorem-level equality between
checker-free reconstruction and the reference checker. The 1,000 cases match
the deterministic v0.2 dataset's 250 positives and 750 mutations. -/
def run : IO Unit := do
  let start ← IO.monoMsNow
  let mut total := 0
  let mut positives := 0
  let mut negatives := 0
  let mut checksum := 0
  for seed in List.range 250 do
    let tree := CutFreeDerivation.generate seed 2
    let certificate ← match tree.desequentialize? with
      | none =>
          throw <| IO.userError
            s!"reconstruction audit generator failed at seed {seed}"
      | some value => pure value
    for candidate in casesForCertificate certificate do
      let reference := candidate.check
      let reconstruction := candidate.reconstructDerivation?
      let reconstructed := reconstruction.isSome
      if reconstructed != reference then
        throw <| IO.userError
          s!"reconstruction/reference mismatch at seed {seed}, case {total}"
      if reference then
        positives := positives + 1
        match reconstruction with
        | none =>
            throw <| IO.userError
              "accepted reconstruction disappeared after Boolean agreement"
        | some result =>
            checksum := checksum + result.output.formulas.size +
              result.output.links.length + result.sequent.length
      else
        negatives := negatives + 1
      total := total + 1
  let elapsed := (← IO.monoMsNow) - start
  if total != 1_000 || positives != 250 || negatives != 750 then
    throw <| IO.userError
      s!"unexpected reconstruction audit counts: total={total}, positives={positives}, negatives={negatives}"
  if elapsed > budgetMs then
    throw <| IO.userError
      s!"reconstruction audit budget exceeded: {elapsed}ms > {budgetMs}ms"
  IO.println
    s!"checker-free-reconstruction-audit-ok cases={total} positives={positives} negatives={negatives} checksum={checksum} elapsed_ms={elapsed} budget_ms={budgetMs}"

end ProofNetIRReconstructionAudit

def main : IO Unit := ProofNetIRReconstructionAudit.run
