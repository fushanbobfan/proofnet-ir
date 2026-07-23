import ProofNetIR

open ProofNetIR

namespace ProofNetIRUnificationAudit

def casesForCertificate (certificate : Certificate) :
    List Certificate :=
  [ certificate,
    { certificate with links := certificate.links.reverse },
    { certificate with conclusions := certificate.conclusions.reverse },
    Mutation.dropFirstLink.apply certificate,
    Mutation.duplicateFirstLink.apply certificate,
    (Mutation.replaceFirstAxiomRight 0).apply certificate ]

def seeds : Nat := 250
def expectedCases : Nat := seeds * 6
def budgetMs : Nat := 15_000

def structuralNegative : Certificate where
  formulas := #[
    .atom "audit-left" true,
    .atom "audit-left" false,
    .atom "audit-right" true,
    .atom "audit-right" false]
  links := [.axiom 0 1, .axiom 2 3]
  conclusions := [0, 1, 2, 3]

/-- Differential audit for the deterministic Guerrini-style fast path and its
exact hybrid wrapper. The audit intentionally records fast-path misses
separately: the theorem for `unificationCheck` is unconditional, whereas full
completeness of `unificationFastCheck` remains a distinct proof obligation. -/
def run : IO Unit := do
  let start ← IO.monoMsNow
  let mut total := 0
  let mut referencePositive := 0
  let mut referenceNegative := 0
  let mut fastPositiveHits := 0
  let mut fastPositiveMisses := 0
  let mut fastFalsePositives := 0
  let mut maxPasses := 0
  let mut maxLinkVisits := 0
  let mut worklistPositiveHits := 0
  let mut worklistPositiveMisses := 0
  let mut worklistFalsePositives := 0
  let mut maxWorklistAttempts := 0
  let mut maxWorklistWaitingRequeues := 0
  let mut checksum := 0
  if !structuralNegative.wellFormed || structuralNegative.check ||
      structuralNegative.unificationFastCheck ||
      structuralNegative.unificationCheck then
    throw <| IO.userError
      "structurally well-formed disconnected sentinel was misclassified"
  match structuralNegative.unificationReconstruct with
  | .error error =>
      if error.code != .nonUniqueThread then
        throw <| IO.userError
          s!"unexpected disconnected sentinel diagnostic: {error.render}"
  | .ok _ =>
      throw <| IO.userError
        "disconnected sentinel unexpectedly produced a unification result"
  for seed in List.range seeds do
    let tree := CutFreeDerivation.generate seed 2
    let certificate ← match tree.desequentialize? with
      | none =>
          throw <| IO.userError
            s!"unification audit generator failed at seed {seed}"
      | some value => pure value
    for candidate in casesForCertificate certificate do
      let reference := candidate.check
      let fastResult := candidate.unificationReconstructWithStats
      let fast := fastResult.isOk
      let worklistResult :=
        candidate.unificationWorklistReconstructWithStats
      let worklistFast := worklistResult.isOk
      let hybrid := candidate.unificationCheck
      let worklistHybrid := candidate.unificationWorklistCheck
      if hybrid != reference then
        throw <| IO.userError
          s!"hybrid/reference mismatch at seed {seed}, case {total}"
      if worklistHybrid != reference then
        throw <| IO.userError
          s!"worklist hybrid/reference mismatch at seed {seed}, case {total}"
      if reference then
        referencePositive := referencePositive + 1
        if fast then
          fastPositiveHits := fastPositiveHits + 1
          match fastResult with
          | .error _ =>
              throw <| IO.userError
                "unification result disappeared after Boolean agreement"
          | .ok result =>
              let stats := result.candidate.stats
              if stats.linkVisits >
                  candidate.links.length * candidate.links.length then
                throw <| IO.userError
                  "proved unification link-visit bound failed at runtime"
              maxPasses := max maxPasses stats.passes
              maxLinkVisits := max maxLinkVisits stats.linkVisits
              checksum := checksum +
                result.verification.output.formulas.size +
                result.verification.output.links.length +
                result.verification.sequent.length
        else
          fastPositiveMisses := fastPositiveMisses + 1
        if worklistFast then
          worklistPositiveHits := worklistPositiveHits + 1
          match worklistResult with
          | .error _ =>
              throw <| IO.userError
                "worklist result disappeared after Boolean agreement"
          | .ok result =>
              if result.candidate.stats.linkAttempts >
                  UnificationWorklistStats.attemptBudget
                    candidate.links.length then
                throw <| IO.userError
                  "proved worklist attempt bound failed at runtime"
              maxWorklistAttempts :=
                max maxWorklistAttempts result.candidate.stats.linkAttempts
              maxWorklistWaitingRequeues :=
                max maxWorklistWaitingRequeues
                  result.candidate.stats.waitingRequeues
        else
          worklistPositiveMisses := worklistPositiveMisses + 1
      else
        referenceNegative := referenceNegative + 1
        if fast then
          fastFalsePositives := fastFalsePositives + 1
        if worklistFast then
          worklistFalsePositives := worklistFalsePositives + 1
      total := total + 1
  let elapsed := (← IO.monoMsNow) - start
  if total != expectedCases then
    throw <| IO.userError
      s!"unexpected unification audit count: total={total}, expected={expectedCases}"
  if fastFalsePositives != 0 then
    throw <| IO.userError
      s!"deterministic unification produced {fastFalsePositives} false positives"
  if worklistFalsePositives != 0 then
    throw <| IO.userError
      s!"worklist unification produced {worklistFalsePositives} false positives"
  if elapsed > budgetMs then
    throw <| IO.userError
      s!"unification audit budget exceeded: {elapsed}ms > {budgetMs}ms"
  IO.println
    s!"unification-audit-ok cases={total} structural_negative_sentinels=1 reference_positives={referencePositive} reference_negatives={referenceNegative} fast_positive_hits={fastPositiveHits} fast_positive_misses={fastPositiveMisses} fast_false_positives={fastFalsePositives} max_passes={maxPasses} max_link_visits={maxLinkVisits} worklist_positive_hits={worklistPositiveHits} worklist_positive_misses={worklistPositiveMisses} worklist_false_positives={worklistFalsePositives} max_worklist_attempts={maxWorklistAttempts} max_worklist_waiting_requeues={maxWorklistWaitingRequeues} checksum={checksum} elapsed_ms={elapsed} budget_ms={budgetMs}"

end ProofNetIRUnificationAudit

def main : IO Unit := ProofNetIRUnificationAudit.run
