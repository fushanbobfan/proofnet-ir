import ProofNetIR.SequentialFigure7ActiveTopDebtHistoryTail
import ProofNetIR.Serialization
import ProofNetIR.Unification
import ProofNetIR.Generate

/-!
# Finite search for the canonical history-tail hypothesis

Every candidate is checked by `unificationCheck`, with the existing equivalence
transporting acceptance to declarative correctness. Every accepted initialization
start is replayed by the actual canonical dispatcher. The Boolean below follows
`CanonicalTagHistory.ActiveTopDebtTailLaw`, including its reset branches; every
prefix is checked, so a later reset cannot conceal an earlier violation.

Exhaustive *shape* depth is the number of logical constructors, as in the earlier
`ExhaustiveDebtSearch` experiment. Exchange nodes and focus choices are omitted
from shape enumeration. Eight deterministic label/polarity decorations and the
six link/boundary variants from NewProgressAudit are applied to every shape.
Equal labelled variants are counted separately. Random coverage uses the existing
`CutFreeDerivation.generate` depth parameter and is reported separately.

`--wait-focus` instead uses depth-three trees whose every internal par joins
the unconsumed frontiers of two independently axiom-started tensor children.
It checks all accepted starts after prioritizing one per distinct initial axiom
region, and measures the exact mate-age classes that limit wait applicability.

`--invariant-probe` runs both certificate sets and measures C1 at every nop,
C2 at every wait, and C3--C5 separately at both rules, before the popped head
receives its raw mark. C4 counts submitted pars with exactly one premise whose
raw mark resolves to the active component, including marks created at older
raw ages. First failures include the submitted occurrence numbering.

The ten-minute limit is checked between complete histories. Exhausting replay
fuel or missing the requested coverage fails closed and never prints `-ok`.
There is no theorem here, including no Boolean-reflection or completeness theorem.
-/

open ProofNetIR
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialSchedulerState

namespace ProofNetIRTailLawSearch

private def hasNonconclusion (certificate : Certificate) (bucket : List Vertex) : Bool :=
  bucket.any fun vertex ↦ !certificate.conclusions.contains vertex

-- The existential in ActiveTopMarkedNonconclusionPresent, including raw marks.
private def activeTopPresent (certificate : Certificate) (state : ReservationState) : Bool :=
  match state.stack.sigma.getLast? with
  | none => false
  | some age =>
      match state.core.components[age]? with
      | some (some component) =>
          component.frontier.any fun vertex ↦
            !certificate.conclusions.contains vertex &&
              match state.core.marks[vertex]? with
              | some (some _) => true
              | _ => false
      | _ => false

private structure TailObservation where
  holds : Bool
  bucket : List Vertex := []
  created : Option Vertex := none

-- Recompute the common typed prefix to read its exact remainingTop. For created
-- heads, decode the exact primitive inputs and verify their resulting ready top.
-- Decoder disagreement is an audit error, never a successful/vacuous law check.
private def tailLawStep (certificate : Certificate) (before : ReservationState)
    (result : Figure7DispatchResult) (prior : Bool) : Except String TailObservation := do
  match result.kind with
  | .concl => return { holds := prior }
  | .new => return { holds := true }
  | .nop | .wait =>
      let some prepared := prepare? before | throw "missing prepared nop/wait prefix"
      let bucket := prepared.stackResult.remainingTop
      return { holds := hasNonconclusion certificate bucket && prior, bucket }
  | .forward | .unifyPayload =>
      let some prepared := prepare? before | throw "missing prepared created-head prefix"
      let some consumer := certificate.connectiveBelow? prepared.stackResult.vertex
        | throw "missing created-head consumer"
      let bucket ← if result.kind == .forward then do
          let some active := prepared.stackResult.after.ready.getLast?
            | throw "missing forward activeReady"
          pure active
        else do
          let some previous := prepared.stackResult.after.ready.dropLast.getLast?
            | throw "missing unify previousReady"
          let some active := prepared.stackResult.after.ready.getLast?
            | throw "missing unify activeReady"
          let some boundary := prepared.stackResult.after.sigma.dropLast.getLast?
            | throw "missing unify previous boundary"
          let some (.initialized payload) := prepared.stackResult.after.waiting[boundary]?
            | throw "missing unify payload"
          pure (payload ++ previous ++ active)
      unless result.after.stack.ready.getLast? == some (consumer.conclusion :: bucket) do
        throw "created-head bucket disagrees with dispatcher output"
      return {
        holds := !certificate.conclusions.contains consumer.conclusion ||
          !activeTopPresent certificate result.after || hasNonconclusion certificate bucket
        bucket
        created := some consumer.conclusion }

private structure ProbeCount where
  holds : Nat := 0
  fails : Nat := 0
  deriving Repr, Inhabited

private def probeLabels : Array String :=
  #["C1 rule=nop", "C2 rule=wait", "C3 rule=nop", "C3 rule=wait",
    "C4 rule=nop", "C4 rule=wait", "C5 rule=nop", "C5 rule=wait"]

private structure Stats where
  cases : Nat := 0
  shapes : Nat := 0
  acceptedStarts : Nat := 0
  skippedStarts : Nat := 0
  firstMarkedRegions : Nat := 0
  histories : Nat := 0
  steps : Nat := 0
  stops : Nat := 0
  kinds : Array Nat := #[0, 0, 0, 0, 0, 0]
  waitCertificates : Nat := 0
  waitPairs : Nat := 0
  parPremisePops : Nat := 0
  parMateUnmarked : Nat := 0
  parMateOlder : Nat := 0
  parMateNotOlder : Nat := 0
  parMateMissing : Nat := 0
  invariantProbe : Bool := false
  probes : Array ProbeCount := Array.replicate 8 {}
  deriving Repr

private def kindIndex : Figure7RuleKind → Nat
  | .concl => 0
  | .nop => 1
  | .new => 2
  | .wait => 3
  | .forward => 4
  | .unifyPayload => 5

-- Measure the exact local age geometry that can reach the wait branch. This is
-- diagnostic coverage, not a second dispatcher: the canonical result below
-- remains the only transition that is replayed.
private def observeWaitGuard (certificate : Certificate)
    (state : ReservationState) (stats : Stats) : Stats :=
  match prepare? state with
  | none => stats
  | some prepared =>
      match certificate.connectiveBelow? prepared.stackResult.vertex with
      | some consumer =>
          if consumer.kind == .par then
            let stats := { stats with parPremisePops := stats.parPremisePops + 1 }
            match prepared.coreMarked.marks[consumer.mate]? with
            | some none =>
                { stats with parMateUnmarked := stats.parMateUnmarked + 1 }
            | some (some mateRawAge) =>
                if mateRawAge < prepared.stackResult.rawAge then
                  { stats with parMateOlder := stats.parMateOlder + 1 }
                else
                  { stats with parMateNotOlder := stats.parMateNotOlder + 1 }
            | none =>
                { stats with parMateMissing := stats.parMateMissing + 1 }
          else
            stats
      | none => stats

-- Existing JSON serializers normalize orders. Include the submitted occurrence
-- arrays using the same formulaJson/linkJson functions for exact replay as well.
private def submittedJson (certificate : Certificate) : Lean.Json :=
  Lean.Json.mkObj [
    ("formulas", .arr (certificate.formulas.map Certificate.formulaJson)),
    ("links", .arr (certificate.links.toArray.map Certificate.linkJson)),
    ("conclusions", Lean.toJson certificate.conclusions)]

-- All observations use the pre-state, never coreMarked from prepare?. C1/C2
-- have their requested rule-specific domains; the other candidates cover both.
private def observeInvariants (certificate : Certificate) (state : ReservationState)
    (context : String) (start step : Nat) (result : Figure7DispatchResult)
    (stats : Stats) : IO Stats := do
  if !stats.invariantProbe || !(result.kind == .nop || result.kind == .wait) then
    return stats
  let some prepared := prepare? state
    | throw (IO.userError "invariant-probe-ERROR missing prepared prefix")
  let head := prepared.stackResult.vertex
  let age := prepared.stackResult.rawAge
  let some consumer := certificate.connectiveBelow? head
    | throw (IO.userError "invariant-probe-ERROR missing par consumer")
  unless consumer.kind == .par do
    throw (IO.userError "invariant-probe-ERROR nop/wait consumer is not par")
  let some (some component) := state.core.components[age]?
    | throw (IO.userError "invariant-probe-ERROR missing active component")
  let unmarked := fun vertex ↦ state.core.marks[vertex]? == some none
  let marked := fun vertex ↦ match state.core.marks[vertex]? with
    | some (some _) => true
    | _ => false
  let activeMarked := fun vertex ↦ match state.core.marks[vertex]? with
    | some (some rawAge) => state.core.representative rawAge == age
    | _ => false
  let nonconclusion := fun vertex ↦ !certificate.conclusions.contains vertex
  let payers := component.frontier.filter fun vertex ↦ unmarked vertex && nonconclusion vertex
  let debt := component.frontier.any fun vertex ↦ marked vertex && nonconclusion vertex
  let singleMarkedPars := certificate.links.countP fun link ↦ match link with
    | .par left right _ => activeMarked left != activeMarked right
    | _ => false
  let p := payers.any (· != head)
  unless p == hasNonconclusion certificate prepared.stackResult.remainingTop do
    throw (IO.userError "invariant-probe-ERROR frontier P disagrees with remainingTop")
  let isWait := result.kind == .wait
  let offset := if isWait then 1 else 0
  let localCandidate := if isWait then marked consumer.mate && p
    else unmarked consumer.mate && component.frontier.contains consumer.mate
  let observations := [(offset, localCandidate), (2 + offset, !debt || payers.length ≥ 2),
    (4 + offset, payers.length ≥ singleMarkedPars), (6 + offset, p)]
  let mut stats := stats
  for (index, holds) in observations do
    let prior := stats.probes[index]!
    if !holds && prior.fails == 0 then
      IO.println s!"invariant-probe-first-failure {probeLabels[index]!}"
      IO.println s!"certificate={certificate.canonicalString}"
      IO.println s!"submitted={submittedJson certificate |>.compress}"
      IO.println (s!"{context} start={start} step={step} rule={repr result.kind} " ++
        s!"head={head} mate={consumer.mate} active={age}")
      let frontierMarks := Lean.toJson (component.frontier.map fun vertex ↦
        (vertex, state.core.marks[vertex]?))
      IO.println (s!"frontier_marks={frontierMarks.compress} payers={repr payers} " ++
        s!"single_marked_pars={singleMarkedPars}")
    let next := if holds then { prior with holds := prior.holds + 1 }
      else { prior with fails := prior.fails + 1 }
    stats := { stats with probes := stats.probes.set! index next }
  return stats

private def printProbe (setName : String) (stats : Stats) : IO Unit := do
  if stats.invariantProbe then
    for index in List.range probeLabels.size do
      let count := stats.probes[index]!
      let steps := stats.kinds[if index % 2 == 0 then 1 else 3]!
      unless count.holds + count.fails == steps do
        throw (IO.userError s!"invariant-probe-ERROR incomplete counts {probeLabels[index]!}")
      IO.println (s!"invariant-probe set={setName} {probeLabels[index]!} " ++
        s!"holds={count.holds} fails={count.fails}")

private def failViolation (certificate : Certificate) (context : String) (start step : Nat)
    (kinds : List Figure7RuleKind) (result : Figure7DispatchResult)
    (observation : TailObservation) : IO α := do
  IO.println "tail-law-search-VIOLATION"
  IO.println s!"certificate={certificate.equivalenceCanonicalString}"
  IO.println s!"submitted={submittedJson certificate |>.compress}"
  IO.println s!"{context} start={start} step={step} rule={repr result.kind}"
  IO.println s!"bucket={repr observation.bucket} created={repr observation.created}"
  IO.println s!"history={repr (result.kind :: kinds).reverse}"
  throw (IO.userError "tail-law violation (step indices are zero-based after initialization)")

-- Reachability retains the exact ExecutedHistory in Prop; its canonical tag
-- augmentation exists by hasCanonicalTagHistory. No classical data is executed.
private def replay (certificate : Certificate) (correct : certificate.DeclarativelyCorrect)
    (context : String) (start : Vertex) (deadline : Nat) (measureWaitGuard : Bool) :
    (state : ReservationState) → ReachableByImplementedDispatcher certificate state →
    List Figure7RuleKind → Bool → Nat → Nat → Stats → IO Stats
  | state, reachable, kinds, prior, step, fuel, stats => do
      if (← IO.monoMsNow) > deadline then
        throw (IO.userError (s!"tail-law-search-INCOMPLETE budget {context} start={start} " ++
          s!"step={step} cases={stats.cases} histories={stats.histories} steps={stats.steps}"))
      let stats := if measureWaitGuard then observeWaitGuard certificate state stats else stats
      let invariant := reachable.schedulerInvariant correct.1
      match equation : dispatch? certificate state invariant with
      | none => return { stats with stops := stats.stops + 1 }
      | some result =>
          match fuel with
          | 0 => throw (IO.userError s!"tail-law-search-INCOMPLETE replay fuel {context}")
          | fuel + 1 =>
              let stats ← observeInvariants certificate state context start step result stats
              let observation ← match tailLawStep certificate state result prior with
                | .ok observation => pure observation
                | .error message => throw (IO.userError s!"tail-law-search-ERROR {message}")
              if !observation.holds then
                failViolation certificate context start step kinds result observation
              else
                let index := kindIndex result.kind
                let stats := { stats with
                  steps := stats.steps + 1
                  kinds := stats.kinds.modify index (· + 1) }
                replay certificate correct context start deadline measureWaitGuard result.after
                  (reachable.dispatch invariant equation) (result.kind :: kinds)
                  observation.holds (step + 1) fuel stats

-- Kept identical to the six ordering families in ProofNetIRNewProgressAudit.
-- That executable has a global main, so importing it would collide with main here.
private def rotateList (values : List α) (offset : Nat) : List α :=
  let pivot := if values.isEmpty then 0 else offset % values.length
  values.drop pivot ++ values.take pivot

private def parityPermutation (values : List α) (oddFirst : Bool) : List α :=
  let indexed := values.zipIdx
  let even := indexed.filterMap fun (value, index) ↦
    if index % 2 == 0 then some value else none
  let odd := indexed.filterMap fun (value, index) ↦
    if index % 2 == 1 then some value else none
  if oddFirst then odd ++ even else even ++ odd

private def positiveVariants (certificate : Certificate) (seed : Nat) :
    List (String × Certificate) :=
  [ ("original", certificate),
    ("reverse-links", { certificate with links := certificate.links.reverse }),
    ("reverse-boundary", { certificate with conclusions := certificate.conclusions.reverse }),
    ("rotate-links", { certificate with links := rotateList certificate.links (seed * 17 + 5) }),
    ("parity-links", { certificate with
      links := parityPermutation certificate.links (seed.testBit 3) }),
    ("mixed-links-boundary", { certificate with
      links := parityPermutation certificate.links (seed.testBit 4)
      conclusions := rotateList certificate.conclusions (seed * 31 + 11) }) ]

private structure AcceptedStart where
  start : Vertex
  region : Vertex × Vertex

private structure StartPriority where
  seen : List (Vertex × Vertex) := []
  first : List AcceptedStart := []
  rest : List AcceptedStart := []

private def initialRegion? (state : ReservationState) : Option (Vertex × Vertex) := do
  let ready ← state.stack.ready.getLast?
  match ready with
  | [left, right] => some (min left right, max left right)
  | _ => none

private def prioritizeDistinctRegions (starts : List AcceptedStart) : List AcceptedStart :=
  let priority := starts.foldl (init := ({} : StartPriority)) fun priority entry ↦
    if priority.seen.contains entry.region then
      { priority with rest := entry :: priority.rest }
    else
      { seen := entry.region :: priority.seen
        first := entry :: priority.first
        rest := priority.rest }
  priority.first.reverse ++ priority.rest.reverse

private def distinctRegionCount (starts : List AcceptedStart) : Nat :=
  starts.foldl (init := ([] : List (Vertex × Vertex))) (fun regions entry ↦
    if regions.contains entry.region then regions else entry.region :: regions) |>.length

private def collectAcceptedStarts (certificate : Certificate)
    (context : String) : IO (List AcceptedStart) := do
  let mut starts := []
  for start in List.range certificate.formulas.size do
    match initializeReservation? certificate start with
    | none => pure ()
    | some state =>
        let some region := initialRegion? state
          | throw (IO.userError s!"tail-law-search-ERROR malformed initial region {context}")
        starts := { start, region } :: starts
  return starts.reverse

private def inspectCertificate (certificate : Certificate) (context : String)
    (startCeiling deadline : Nat) (prioritizeStarts : Bool) (stats : Stats) : IO Stats := do
  if accepted : certificate.unificationCheck = true then
    let correct : certificate.DeclarativelyCorrect :=
      certificate.check_iff_declarativelyCorrect.mp
        (certificate.unificationCheck_eq_check ▸ accepted)
    let waitBeforeCertificate := stats.kinds[3]!
    let mut stats := { stats with cases := stats.cases + 1 }
    if prioritizeStarts then
      let acceptedStarts ← collectAcceptedStarts certificate context
      let ordered := prioritizeDistinctRegions acceptedStarts
      let selected := ordered.take startCeiling
      stats := { stats with
        acceptedStarts := stats.acceptedStarts + acceptedStarts.length
        skippedStarts := stats.skippedStarts + acceptedStarts.length - selected.length
        firstMarkedRegions := stats.firstMarkedRegions + distinctRegionCount acceptedStarts }
      for entry in selected do
        match equation : initializeReservation? certificate entry.start with
        | none =>
            throw (IO.userError s!"tail-law-search-ERROR unstable accepted start {context}")
        | some state =>
            let waitBeforeHistory := stats.kinds[3]!
            stats ← replay certificate correct context entry.start deadline true state
              (dispatcher_reachable_of_initializeReservation?_eq_some equation) [] true 0
              (16 * (certificate.formulas.size + certificate.links.length + 1))
              { stats with histories := stats.histories + 1 }
            if stats.kinds[3]! > waitBeforeHistory then
              stats := { stats with waitPairs := stats.waitPairs + 1 }
    else
      let mut selected := 0
      -- Probe every vertex so the summary reports the complete accepted-start
      -- population. Replay the first `startCeiling` successes in vertex order.
      for start in List.range certificate.formulas.size do
        match equation : initializeReservation? certificate start with
        | none => pure ()
        | some state =>
            stats := { stats with acceptedStarts := stats.acceptedStarts + 1 }
            if selected < startCeiling then
              selected := selected + 1
              stats ← replay certificate correct context start deadline false state
                (dispatcher_reachable_of_initializeReservation?_eq_some equation) [] true 0
                (16 * (certificate.formulas.size + certificate.links.length + 1))
                { stats with histories := stats.histories + 1 }
            else
              stats := { stats with skippedStarts := stats.skippedStarts + 1 }
    if stats.kinds[3]! > waitBeforeCertificate then
      stats := { stats with waitCertificates := stats.waitCertificates + 1 }
    return stats
  else
    throw (IO.userError s!"tail-law-search-ERROR rejected generated certificate {context}")

private def inspectTree (tree : CutFreeDerivation) (seed : Nat) (context : String)
    (startCeiling deadline : Nat) (prioritizeStarts : Bool) (stats : Stats) : IO Stats := do
  let some certificate := tree.desequentialize?
    | throw (IO.userError s!"tail-law-search-ERROR malformed derivation {context}")
  let mut stats := stats
  for (name, variant) in positiveVariants certificate seed do
    stats ← inspectCertificate variant s!"{context} variant={name}" startCeiling deadline
      prioritizeStarts stats
  return stats

private structure Shape where
  tree : CutFreeDerivation
  boundary : Nat

private def axiomShape : Shape := ⟨.axiom "p" true, 2⟩

private def parShape (child : Shape) : Shape :=
  ⟨.par 0 0 child.tree, child.boundary - 1⟩

private def tensorShape (left right : Shape) : Shape :=
  ⟨.tensor 0 0 left.tree right.tree, left.boundary + right.boundary - 1⟩

-- Every recursive child has exactly two boundary occurrences. Tensor consumes
-- one from each independent axiom region; the immediately enclosing par joins
-- the two remaining regional occurrences. Thus every internal par is directly
-- above a cross-region tensor, and depth three contains eight axiom regions.
private def waitFocusedTree (seed : Nat) : Nat → CutFreeDerivation
  | 0 => .axiom s!"p{seed % 11}" (seed.testBit 0)
  | depth + 1 =>
      let left := waitFocusedTree (seed * 2 + 1) depth
      let right := waitFocusedTree (seed * 2 + 2) depth
      .par 1 1 (.tensor (seed % 2) ((seed / 2) % 2) left right)

private def relabelTree (seed : Nat) : CutFreeDerivation → CutFreeDerivation
  | .axiom _ _ => .axiom s!"p{seed % 11}" (seed.testBit 0)
  | .par left right child => .par left right (relabelTree (seed * 2 + 1) child)
  | .tensor leftFocus rightFocus left right =>
      .tensor leftFocus rightFocus (relabelTree (seed * 2 + 1) left)
        (relabelTree (seed * 2 + 2) right)
  | .exchange order child => .exchange order (relabelTree (seed * 2 + 1) child)

private def enumerateDepth (levels : Array (Array Shape)) (depth : Nat)
    (visit : Shape → IO Unit) : IO Unit := do
  if depth == 0 then
    visit axiomShape
  else
    for child in levels[depth - 1]! do
      if child.boundary ≥ 2 then visit (parShape child)
    for leftDepth in List.range depth do
      let rightDepth := depth - 1 - leftDepth
      for left in levels[leftDepth]! do
        for right in levels[rightDepth]! do
          visit (tensorShape left right)

private def summary (stats : Stats) (depth labelVariants orderVariants startCap
    randomSeeds elapsed : Nat) : String :=
  s!"cases={stats.cases} histories={stats.histories} steps={stats.steps} " ++
    s!"depths=0..{depth} shapes={stats.shapes} label_variants={labelVariants} " ++
    s!"order_variants={orderVariants} starts_cap={startCap} " ++
    s!"accepted_starts={stats.acceptedStarts} skipped_starts={stats.skippedStarts} " ++
    s!"random_depths=6..7 seeds={randomSeeds} dispatch_none={stats.stops} " ++
    s!"rules={repr stats.kinds} elapsed_ms={elapsed}"

private def run (smoke : Bool) (invariantProbe : Bool := false) : IO Unit := do
  let started ← IO.monoMsNow
  let deadline := started + 600000
  let statsRef ← IO.mkRef ({ invariantProbe } : Stats)
  let randomSeeds := if smoke then 0 else 4
  let labelVariants := if smoke then 1 else 8
  let orderVariants := 6
  let startCap := if smoke then 2 else 4
  -- Run the deep seeded families first so an interrupted exhaustive layer does
  -- not silently erase the promised random-depth coverage.
  for depth in [6, 7] do
    for seed in List.range randomSeeds do
      let stats ← inspectTree (CutFreeDerivation.generate seed depth) seed
        s!"random_depth={depth} seed={seed}" startCap deadline false (← statsRef.get)
      statsRef.set stats
  let mut levels : Array (Array Shape) := #[]
  let target := if smoke then 2 else 5
  let mut completed := 0
  for depth in List.range (target + 1) do
    let layerRef ← IO.mkRef (#[] : Array Shape)
    let countRef ← IO.mkRef 0
    try
      enumerateDepth levels depth fun shape ↦ do
        let index ← countRef.get
        let priorStats ← statsRef.get
        let mut stats := { priorStats with shapes := priorStats.shapes + 1 }
        for labelSeed in List.range labelVariants do
          stats ← inspectTree (relabelTree labelSeed shape.tree)
            (index * labelVariants + labelSeed)
            s!"depth={depth} shape={index} label={labelSeed}"
            startCap deadline false stats
        statsRef.set stats
        countRef.set (index + 1)
        layerRef.modify (·.push shape)
    catch error =>
      IO.println (s!"tail-law-search-coverage {summary (← statsRef.get) completed
        labelVariants orderVariants startCap randomSeeds ((← IO.monoMsNow) - started)} " ++
          s!"partial_depth={depth} partial_shapes={← countRef.get}")
      throw error
    levels := levels.push (← layerRef.get)
    completed := depth
  let stats ← statsRef.get
  unless smoke || (stats.cases ≥ 20000 && completed ≥ 5 && stats.stops == stats.histories) do
    throw (IO.userError s!"tail-law-search-INCOMPLETE coverage {repr stats}")
  let label := if smoke then "tail-law-search-smoke-ok" else "tail-law-search-ok"
  IO.println s!"{label} {summary stats completed labelVariants orderVariants startCap
    randomSeeds ((← IO.monoMsNow) - started)}"
  printProbe (if smoke then "smoke" else "default") stats

private def waitFocusSummary (stats : Stats) (baseTrees labelVariants orderVariants
    startCeiling elapsed : Nat) : String :=
  s!"cases={stats.cases} histories={stats.histories} steps={stats.steps} " ++
    s!"base_trees={baseTrees} axiom_regions=8 label_variants={labelVariants} " ++
    s!"order_variants={orderVariants} start_ceiling={startCeiling} " ++
    s!"accepted_starts={stats.acceptedStarts} skipped_starts={stats.skippedStarts} " ++
    s!"first_marked_regions={stats.firstMarkedRegions} dispatch_none={stats.stops} " ++
    s!"wait_certificates={stats.waitCertificates} wait_steps={stats.kinds[3]!} " ++
    s!"wait_pairs={stats.waitPairs} rules={repr stats.kinds} " ++
    s!"wait_guard_par={stats.parPremisePops} " ++
    s!"mate_unmarked={stats.parMateUnmarked} mate_older={stats.parMateOlder} " ++
    s!"mate_not_older={stats.parMateNotOlder} mate_missing={stats.parMateMissing} " ++
    s!"eligible_not_wait={stats.parMateOlder - stats.kinds[3]!} " ++
    s!"elapsed_ms={elapsed} budget_ms=600000"

private def runWaitFocus (invariantProbe : Bool := false) : IO Unit := do
  let started ← IO.monoMsNow
  let deadline := started + 600000
  let statsRef ← IO.mkRef ({ invariantProbe } : Stats)
  let baseTrees := 24
  let labelVariants := 8
  let orderVariants := 6
  let startCeiling := 64
  try
    for seed in List.range baseTrees do
      let prior := ← statsRef.get
      let mut stats := { prior with shapes := prior.shapes + 1 }
      for labelSeed in List.range labelVariants do
        stats ← inspectTree (relabelTree labelSeed (waitFocusedTree seed 3))
          (seed * labelVariants + labelSeed)
          s!"wait_focus tree={seed} label={labelSeed}" startCeiling deadline true stats
      statsRef.set stats
  catch error =>
    let elapsed := (← IO.monoMsNow) - started
    IO.println s!"tail-law-wait-focus-coverage {waitFocusSummary (← statsRef.get)
      baseTrees labelVariants orderVariants startCeiling elapsed}"
    throw error
  let stats ← statsRef.get
  let elapsed := (← IO.monoMsNow) - started
  IO.println s!"tail-law-wait-focus-coverage {waitFocusSummary stats baseTrees
    labelVariants orderVariants startCeiling elapsed}"
  unless stats.cases == baseTrees * labelVariants * orderVariants &&
      stats.skippedStarts == 0 && stats.stops == stats.histories &&
      stats.waitCertificates ≥ 500 && stats.kinds[3]! ≥ 5000 && elapsed ≤ 600000 do
    throw (IO.userError
      (s!"tail-law-search-INCOMPLETE wait coverage " ++
        s!"wait_certificates={stats.waitCertificates}/500 " ++
        s!"wait_steps={stats.kinds[3]!}/5000 wait_pairs={stats.waitPairs}; " ++
        s!"measured dispatcher geometry: par={stats.parPremisePops}, " ++
        s!"mate_unmarked={stats.parMateUnmarked}, mate_older={stats.parMateOlder}, " ++
        s!"mate_not_older={stats.parMateNotOlder}, mate_missing={stats.parMateMissing}, " ++
        s!"eligible_not_wait={stats.parMateOlder - stats.kinds[3]!}"))
  IO.println s!"tail-law-search-wait-focus-ok {waitFocusSummary stats baseTrees
    labelVariants orderVariants startCeiling elapsed}"
  printProbe "wait-focus" stats

end ProofNetIRTailLawSearch

def main (args : List String) : IO Unit := do
  match args with
  | [] => ProofNetIRTailLawSearch.run false
  | ["--smoke"] => ProofNetIRTailLawSearch.run true
  | ["--wait-focus"] => ProofNetIRTailLawSearch.runWaitFocus
  | ["--invariant-probe"] =>
      ProofNetIRTailLawSearch.run false true
      ProofNetIRTailLawSearch.runWaitFocus true
  | ["--invariant-probe", "--smoke"] => ProofNetIRTailLawSearch.run true true
  | ["--invariant-probe", "--wait-focus"] => ProofNetIRTailLawSearch.runWaitFocus true
  | _ => throw (IO.userError
      "usage: proofnet_ir_tail_law_search [--invariant-probe] [--smoke | --wait-focus]")
