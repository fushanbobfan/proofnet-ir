import ProofNetIR

open ProofNetIR

namespace ProofNetIRUnificationCompletenessSearch

structure PositiveVariant where
  name : String
  certificate : Certificate

def rotateList (values : List α) (offset : Nat) : List α :=
  let pivot := if values.isEmpty then 0 else offset % values.length
  values.drop pivot ++ values.take pivot

def parityPermutation (values : List α) (oddFirst : Bool) : List α :=
  let indexed := values.zipIdx
  let even := indexed.filterMap fun (value, index) =>
    if index % 2 == 0 then some value else none
  let odd := indexed.filterMap fun (value, index) =>
    if index % 2 == 1 then some value else none
  if oddFirst then odd ++ even else even ++ odd

def positiveVariants (certificate : Certificate) (seed : Nat) :
    List PositiveVariant :=
  [ { name := "original", certificate },
    { name := "reverse-links",
      certificate := { certificate with links := certificate.links.reverse } },
    { name := "reverse-boundary",
      certificate :=
        { certificate with conclusions := certificate.conclusions.reverse } },
    { name := "rotate-links",
      certificate :=
        { certificate with
          links := rotateList certificate.links (seed * 17 + 5) } },
    { name := "parity-links",
      certificate :=
        { certificate with
          links := parityPermutation certificate.links (seed.testBit 3) } },
    { name := "mixed-links-boundary",
      certificate :=
        { certificate with
          links := parityPermutation certificate.links (seed.testBit 4)
          conclusions :=
            rotateList certificate.conclusions (seed * 31 + 11) } } ]

def seeds : Nat := 1_000
def variantsPerSeed : Nat := 6
def expectedCases : Nat := seeds * variantsPerSeed
def budgetMs : Nat := 30_000

/-- Adversarial positive-corpus search for a deterministic-unification miss.

Every base certificate is emitted by `CutFreeDerivation.desequentialize?`, whose
acceptance is proved by `CutFreeDerivation.desequentialize?_check`. The search
varies depth from zero through five and changes link and boundary order without
changing proof-net identity. It is deliberately described as empirical search:
success does not replace the missing universal completeness theorem. -/
def run : IO Unit := do
  let start ← IO.monoMsNow
  let mut total := 0
  let mut checksum := 0
  let mut maxFormulas := 0
  let mut maxLinks := 0
  for seed in List.range seeds do
    let depth := seed % 6
    let tree := CutFreeDerivation.generate seed depth
    let certificate ← match tree.desequentialize? with
      | none =>
          throw <| IO.userError
            s!"positive generator failed at seed={seed}, depth={depth}"
      | some value => pure value
    for variant in positiveVariants certificate seed do
      let candidate := variant.certificate
      if !candidate.wellFormed then
        throw <| IO.userError
          s!"positive reorder became malformed at seed={seed}, depth={depth}, variant={variant.name}"
      match candidate.unificationReconstruct with
      | .error error =>
          throw <| IO.userError
            s!"fast-path miss at seed={seed}, depth={depth}, variant={variant.name}: {error.render}"
      | .ok result =>
          checksum := checksum + result.output.formulas.size +
            result.output.links.length + result.sequent.length
          maxFormulas := max maxFormulas candidate.formulas.size
          maxLinks := max maxLinks candidate.links.length
      total := total + 1
  let elapsed := (← IO.monoMsNow) - start
  if total != expectedCases then
    throw <| IO.userError
      s!"unexpected completeness-search count: total={total}, expected={expectedCases}"
  if elapsed > budgetMs then
    throw <| IO.userError
      s!"unification completeness-search budget exceeded: {elapsed}ms > {budgetMs}ms"
  IO.println
    s!"unification-completeness-search-ok cases={total} seeds={seeds} depths=0..5 variants_per_seed={variantsPerSeed} max_formulas={maxFormulas} max_links={maxLinks} checksum={checksum} elapsed_ms={elapsed} budget_ms={budgetMs}"

end ProofNetIRUnificationCompletenessSearch

def main : IO Unit := ProofNetIRUnificationCompletenessSearch.run
