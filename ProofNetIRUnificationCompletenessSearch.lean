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

def seeds : Nat := 1_200
def depthCount : Nat := 8
def variantsPerSeed : Nat := 6
def expectedCases : Nat := seeds * variantsPerSeed
def budgetMs : Nat := 120_000

/-- Adversarial positive-corpus search for a deterministic-unification miss.

Every base certificate is emitted by `CutFreeDerivation.desequentialize?`, whose
acceptance is proved by `CutFreeDerivation.desequentialize?_check`. The search
varies depth from zero through seven, including deeper nested tensor/par
families than the original gate, and changes link and boundary order without
changing proof-net identity. For the eager and worklist candidates this is
empirical search, since their completeness is not a theorem. -/
def run : IO Unit := do
  let start ← IO.monoMsNow
  let mut total := 0
  let mut checksum := 0
  let mut maxFormulas := 0
  let mut maxLinks := 0
  let mut maxPasses := 0
  let mut maxLinkVisits := 0
  let mut maxWorklistAttempts := 0
  let mut maxWorklistWaitingRequeues := 0
  for seed in List.range seeds do
    let depth := seed % depthCount
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
      match candidate.unificationReconstructWithStats with
      | .error error =>
          throw <| IO.userError
            s!"fast-path miss at seed={seed}, depth={depth}, variant={variant.name}: {error.render}"
      | .ok result =>
          let stats := result.candidate.stats
          if stats.linkVisits >
              candidate.links.length * candidate.links.length then
            throw <| IO.userError
              s!"proved link-visit bound failed at seed={seed}, variant={variant.name}"
          checksum := checksum +
            result.verification.output.formulas.size +
            result.verification.output.links.length +
            result.verification.sequent.length
          maxFormulas := max maxFormulas candidate.formulas.size
          maxLinks := max maxLinks candidate.links.length
          maxPasses := max maxPasses stats.passes
          maxLinkVisits := max maxLinkVisits stats.linkVisits
      match candidate.unificationWorklistReconstructWithStats with
      | .error error =>
          throw <| IO.userError
            s!"worklist fast-path miss at seed={seed}, depth={depth}, variant={variant.name}: {error.render}"
      | .ok result =>
          if result.candidate.stats.linkAttempts >
              UnificationWorklistStats.attemptBudget
                candidate.links.length then
            throw <| IO.userError
              s!"proved worklist attempt bound failed at seed={seed}, variant={variant.name}"
          maxWorklistAttempts :=
            max maxWorklistAttempts result.candidate.stats.linkAttempts
          maxWorklistWaitingRequeues :=
            max maxWorklistWaitingRequeues
              result.candidate.stats.waitingRequeues
          checksum := checksum +
            result.verification.output.formulas.size +
            result.verification.output.links.length +
            result.verification.sequent.length
      total := total + 1
  let elapsed := (← IO.monoMsNow) - start
  if total != expectedCases then
    throw <| IO.userError
      s!"unexpected completeness-search count: total={total}, expected={expectedCases}"
  if elapsed > budgetMs then
    throw <| IO.userError
      s!"unification completeness-search budget exceeded: {elapsed}ms > {budgetMs}ms"
  IO.println
    s!"unification-completeness-search-ok cases={total} seeds={seeds} depths=0..7 variants_per_seed={variantsPerSeed} max_formulas={maxFormulas} max_links={maxLinks} max_passes={maxPasses} max_link_visits={maxLinkVisits} max_worklist_attempts={maxWorklistAttempts} max_worklist_waiting_requeues={maxWorklistWaitingRequeues} checksum={checksum} elapsed_ms={elapsed} budget_ms={budgetMs}"

/-- Budget of the sequential mode, which runs the public decision on every case
and its slower instrumented twin on the original variant of every seed. -/
def sequentialBudgetMs : Nat := 240_000

/-- The same positive corpus against the public decision `unificationCheck`.
Acceptance is a theorem (`unificationCheck_eq_check`); this mode checks the
compiled executable against it on every case. On the original variant of
every seed it also runs the instrumented twin `sequentialDecisionWithStats`,
checks the proved dispatcher-call bound `formulas.size + 1` and cost bound
`152 * (formulas.size + 1) * submittedSize`, and records how much of the cost
bound the runs use. -/
def runSequential : IO Unit := do
  let start ← IO.monoMsNow
  let mut total := 0
  let mut instrumented := 0
  let mut checksum := 0
  let mut maxFormulas := 0
  let mut maxLinks := 0
  let mut maxCalls := 0
  let mut maxTotal := 0
  let mut maxPermille := 0
  for seed in List.range seeds do
    let depth := seed % depthCount
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
      if !candidate.unificationCheck then
        throw <| IO.userError
          s!"sequential decision miss at seed={seed}, depth={depth}, variant={variant.name}"
      maxFormulas := max maxFormulas candidate.formulas.size
      maxLinks := max maxLinks candidate.links.length
      total := total + 1
      if variant.name == "original" then
        let run := candidate.sequentialDecisionWithStats
        if !run.accepted then
          throw <| IO.userError
            s!"instrumented decision miss at seed={seed}, depth={depth}"
        if run.stats.dispatchCalls > candidate.formulas.size + 1 then
          throw <| IO.userError
            s!"proved dispatcher-call bound failed at seed={seed}, depth={depth}"
        let bound := 152 * (candidate.formulas.size + 1) *
          SequentialCost.submittedSize candidate
        if run.stats.total > bound then
          throw <| IO.userError
            s!"proved sequential cost bound failed at seed={seed}, depth={depth}"
        checksum := checksum + run.stats.total
        maxCalls := max maxCalls run.stats.dispatchCalls
        maxTotal := max maxTotal run.stats.total
        maxPermille := max maxPermille (run.stats.total * 1000 / bound)
        instrumented := instrumented + 1
  let elapsed := (← IO.monoMsNow) - start
  if total != expectedCases || instrumented != seeds then
    throw <| IO.userError
      s!"unexpected sequential-search count: total={total}, instrumented={instrumented}, expected={expectedCases}/{seeds}"
  if elapsed > sequentialBudgetMs then
    throw <| IO.userError
      s!"sequential decision search budget exceeded: {elapsed}ms > {sequentialBudgetMs}ms"
  IO.println
    s!"sequential-decision-search-ok cases={total} seeds={seeds} depths=0..7 variants_per_seed={variantsPerSeed} max_formulas={maxFormulas} max_links={maxLinks} instrumented={instrumented} max_dispatch_calls={maxCalls} max_total={maxTotal} max_bound_permille={maxPermille} checksum={checksum} elapsed_ms={elapsed} budget_ms={sequentialBudgetMs}"

end ProofNetIRUnificationCompletenessSearch

def main (args : List String) : IO Unit :=
  match args with
  | ["--sequential"] => ProofNetIRUnificationCompletenessSearch.runSequential
  | _ => ProofNetIRUnificationCompletenessSearch.run
