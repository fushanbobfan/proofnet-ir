import ProofNetIR

open ProofNetIR

namespace ProofNetIRNewProgressAudit

open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerState

/-!
# Finite reachable-state audit for the shallow Figure-7 `new` guard

This executable searches only states produced by a successful
`initializeReservation?` followed by zero or more successful canonical
`dispatch?` calls. It looks for the finite counterexample shape

`certificate.check = true ∧ ReachableByImplementedDispatcher certificate state ∧
  Nonempty (NewGuard certificate state) ∧ new? certificate state invariant = none`.

The search is deterministic and finite. Absence of a witness is regression
evidence over the constants below, not a progress theorem or a proof that the
shallow guard is sufficient. Labelled variants may denote equal certificates;
the reported count is a count of labelled audit cases, not a uniqueness claim.
Default CI covers depths zero through four; `--extended` adds depth five and
`--profile-depth N` prints every initialization/replay phase. Candidate
acceptance uses `unificationCheck`, then the kernel theorem
`unificationCheck_eq_check` transports that fact to the exact proposition
stored in each witness. Depths zero through two also execute the direct
all-switchings checker as a bounded differential sentinel.
-/

structure PositiveVariant where
  name : String
  certificate : Certificate

def rotateList (values : List α) (offset : Nat) : List α :=
  let pivot := if values.isEmpty then 0 else offset % values.length
  values.drop pivot ++ values.take pivot

def parityPermutation (values : List α) (oddFirst : Bool) : List α :=
  let indexed := values.zipIdx
  let even := indexed.filterMap fun (value, index) ↦
    if index % 2 == 0 then some value else none
  let odd := indexed.filterMap fun (value, index) ↦
    if index % 2 == 1 then some value else none
  if oddFirst then odd ++ even else even ++ odd

/-- The same six accepted-proof-net-preserving reorder families used by the
existing unification completeness search. Every concrete variant is rechecked
before it enters this audit. -/
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

/-- Construct the actual proof-relevant shallow guard from input queries.
Failure means exactly that at least one field of `NewGuard` could not be
constructed; no stronger route or enqueue condition is inspected here. -/
def newGuard? (certificate : Certificate) (before : ReservationState) :
    Option (NewGuard certificate before) :=
  match readyEquation : before.stack.ready.getLast? with
  | some (vertex :: readyTail) =>
      match sigmaEquation : before.stack.sigma.getLast? with
      | some rawAge =>
          match tensorEquation : certificate.tensorBelow? vertex with
          | some tensor =>
              if mateUnmarked :
                  before.core.marks[tensor.mate]? = some none then
                some {
                  head := {
                    vertex
                    readyTail
                    rawAge
                    top_ready := readyEquation
                    sigma_top := sigmaEquation }
                  tensor
                  tensor_valid :=
                    Certificate.tensorBelow?_eq_some_iff.mp tensorEquation
                  mate_unmarked := mateUnmarked }
              else
                none
          | none => none
      | none => none
  | _ => none

/-- Fine-grained reason that the later operational enqueue guard failed. -/
inductive OperationalGuardFailure where
  | zeroHorizon
  | activeNotTop
  | activeOutOfRange
  | reachedOutOfBounds
  | partnerOutOfBounds
  | equalEndpoints
  | reachedAlreadyQueued
  | partnerAlreadyQueued
  | reachedNotUnmarked
  | partnerNotUnmarked
  | activeWaitingNotUndefined
  | freshWaitingNotUndefined
  deriving Repr, DecidableEq

/-- Return the first false conjunct in `OperationalNewReadyAt`, in declaration
order. `none` means that the complete operational guard holds. -/
def operationalGuardFailure? (state : SequentialStackState)
    (active : RawTokenAge) (reached partner : Vertex) :
    Option OperationalGuardFailure :=
  if ¬ 0 < state.nextAge then
    some .zeroHorizon
  else if ¬ state.sigma.getLast? = some active then
    some .activeNotTop
  else if ¬ active < state.nextAge then
    some .activeOutOfRange
  else if ¬ reached < state.marks.size then
    some .reachedOutOfBounds
  else if ¬ partner < state.marks.size then
    some .partnerOutOfBounds
  else if ¬ reached ≠ partner then
    some .equalEndpoints
  else if ¬ reached ∉ state.queuedVertices then
    some .reachedAlreadyQueued
  else if ¬ partner ∉ state.queuedVertices then
    some .partnerAlreadyQueued
  else if ¬ state.marks[reached]? = some none then
    some .reachedNotUnmarked
  else if ¬ state.marks[partner]? = some none then
    some .partnerNotUnmarked
  else if ¬ state.waiting[active]? = some .undefined then
    some .activeWaitingNotUndefined
  else if ¬ state.waiting[state.nextAge]? = some .undefined then
    some .freshWaitingNotUndefined
  else
    none

/-- First failing stage in the exact operational `new?` pipeline. `success`
is retained as a consistency sentinel and cannot accompany a genuine
`new? = none` counterexample unless this diagnostic drifts from the executor. -/
inductive NewFailureStage where
  | popReady
  | markReady
  | tensorBelow
  | nextAxiom
  | orientedEndpoints
  | missingOperationalActive
  | operationalGuard (reason : OperationalGuardFailure)
  | operationalEnqueueInconsistent
  | reserveAxiom
  | success
  deriving Repr, DecidableEq

/-- Diagnose the first failing query in `new?` without mutating the state. -/
def diagnoseNew (certificate : Certificate) (before : ReservationState) :
    NewFailureStage :=
  match before.stack.popReadyMark? with
  | .error _ => .popReady
  | .ok stackResult =>
      match before.core.markReadyRaw? stackResult.vertex stackResult.rawAge with
      | .error _ => .markReady
      | .ok coreMarked =>
          match certificate.tensorBelow? stackResult.vertex with
          | none => .tensorBelow
          | some tensor =>
              match
                  SequentialUnification.nextAxiom? certificate coreMarked
                    (SequentialUnification.sourceIndex certificate)
                    (SequentialUnification.sourceIndex_sound certificate)
                    before.tags tensor.mate with
              | none => .nextAxiom
              | some search =>
                  match search.orientedEndpoints? with
                  | none => .orientedEndpoints
                  | some (reached, partner) =>
                      match stackResult.after.sigma.getLast? with
                      | none => .missingOperationalActive
                      | some active =>
                          match operationalGuardFailure?
                              stackResult.after active reached partner with
                          | some reason => .operationalGuard reason
                          | none =>
                              match stackResult.after.operationalNewEnqueue?
                                  reached partner with
                              | none => .operationalEnqueueInconsistent
                              | some _ =>
                                  match certificate.reserveAxiomAt?
                                      coreMarked search.linkIndex with
                                  | none => .reserveAxiom
                                  | some _ => .success

structure CheckedCandidate where
  depth : Nat
  seed : Nat
  variant : String
  certificate : Certificate
  accepted : certificate.check = true
  structural : certificate.StructurallyWellFormed

/-- A fully certified witness of the audited counterexample shape. The
`reachable` field is definitionally `Nonempty (ExecutedHistory ...)`, so this
cannot be populated by an arbitrary invariant-valid state. -/
structure Counterexample where
  depth : Nat
  seed : Nat
  variant : String
  start : Vertex
  step : Nat
  replayKinds : List Figure7RuleKind
  certificate : Certificate
  accepted : certificate.check = true
  state : ReservationState
  reachable : ReachableByImplementedDispatcher certificate state
  invariant : SchedulerInvariant certificate state
  guard : NewGuard certificate state
  newFailure :
    new? certificate state invariant.toReservationInvariant = none
  failureStage : NewFailureStage

structure AuditStats where
  baseDerivations : Nat := 0
  checkedCertificates : Nat := 0
  directCheckSentinels : Nat := 0
  initializationAttempts : Nat := 0
  initializationSuccesses : Nat := 0
  reachableStates : Nat := 0
  guardStates : Nat := 0
  newSuccessStates : Nat := 0
  newFailureStates : Nat := 0
  newSuccessWithoutGuard : Nat := 0
  dispatchSteps : Nat := 0
  terminalRuns : Nat := 0
  cycleRuns : Nat := 0
  truncatedRuns : Nat := 0
  maxReplaySteps : Nat := 0
  checksum : Nat := 0
  deriving Repr, DecidableEq

def AuditStats.add (left right : AuditStats) : AuditStats where
  baseDerivations := left.baseDerivations + right.baseDerivations
  checkedCertificates := left.checkedCertificates + right.checkedCertificates
  directCheckSentinels :=
    left.directCheckSentinels + right.directCheckSentinels
  initializationAttempts :=
    left.initializationAttempts + right.initializationAttempts
  initializationSuccesses :=
    left.initializationSuccesses + right.initializationSuccesses
  reachableStates := left.reachableStates + right.reachableStates
  guardStates := left.guardStates + right.guardStates
  newSuccessStates := left.newSuccessStates + right.newSuccessStates
  newFailureStates := left.newFailureStates + right.newFailureStates
  newSuccessWithoutGuard :=
    left.newSuccessWithoutGuard + right.newSuccessWithoutGuard
  dispatchSteps := left.dispatchSteps + right.dispatchSteps
  terminalRuns := left.terminalRuns + right.terminalRuns
  cycleRuns := left.cycleRuns + right.cycleRuns
  truncatedRuns := left.truncatedRuns + right.truncatedRuns
  maxReplaySteps := max left.maxReplaySteps right.maxReplaySteps
  checksum := left.checksum + right.checksum

structure SearchResult where
  stats : AuditStats := {}
  counterexample : Option Counterexample := none

def SearchResult.addStats (result : SearchResult) (stats : AuditStats) : SearchResult :=
  { result with stats := result.stats.add stats }

def stateChecksum (state : ReservationState) : Nat :=
  state.stack.nextAge + state.stack.sigma.length +
    state.stack.ready.flatten.length + state.stack.waitingVertices.length +
    state.core.startedAxioms + state.core.firedConnectives

/-- Conservative finite replay fuel. Zero truncations are required by the
executable gate, so this bound is observable rather than silently assumed. -/
def replayFuel (certificate : Certificate) : Nat :=
  16 * (certificate.formulas.size + certificate.links.length + 1)

def parCount (certificate : Certificate) : Nat :=
  certificate.links.foldl (fun count link ↦
    match link with
    | .par _ _ _ => count + 1
    | _ => count) 0

def inspectReachable (candidate : CheckedCandidate) (start : Vertex)
    (state : ReservationState)
    (reachable : ReachableByImplementedDispatcher candidate.certificate state)
    (seen : List ReservationState) (reversedKinds : List Figure7RuleKind)
    (step : Nat) : Nat → SearchResult
  | 0 =>
      if state ∈ seen then
        { stats := { cycleRuns := 1, maxReplaySteps := step } }
      else
        let invariant := reachable.schedulerInvariant candidate.structural
        let base : AuditStats := {
          reachableStates := 1
          truncatedRuns := 1
          maxReplaySteps := step
          checksum := stateChecksum state }
        match newEquation : new? candidate.certificate state
            invariant.toReservationInvariant with
        | none =>
            match newGuard? candidate.certificate state with
            | none => { stats := base }
            | some guard =>
                { stats := {
                    base with guardStates := 1, newFailureStates := 1 }
                  counterexample := some {
                    depth := candidate.depth
                    seed := candidate.seed
                    variant := candidate.variant
                    start
                    step
                    replayKinds := reversedKinds.reverse
                    certificate := candidate.certificate
                    accepted := candidate.accepted
                    state
                    reachable
                    invariant
                    guard
                    newFailure := newEquation
                    failureStage := diagnoseNew candidate.certificate state } }
        | some _ =>
            match newGuard? candidate.certificate state with
            | none =>
                { stats := {
                    base with
                      newSuccessStates := 1
                      newSuccessWithoutGuard := 1 } }
            | some _ =>
                { stats := {
                    base with guardStates := 1, newSuccessStates := 1 } }
  | fuel + 1 =>
      if state ∈ seen then
        { stats := { cycleRuns := 1, maxReplaySteps := step } }
      else
        let invariant := reachable.schedulerInvariant candidate.structural
        let base : AuditStats := {
          reachableStates := 1
          maxReplaySteps := step
          checksum := stateChecksum state }
        let afterGuard : SearchResult :=
          match newEquation : new? candidate.certificate state
              invariant.toReservationInvariant with
          | none =>
              match newGuard? candidate.certificate state with
              | none => { stats := base }
              | some guard =>
                  { stats := {
                      base with guardStates := 1, newFailureStates := 1 }
                    counterexample := some {
                      depth := candidate.depth
                      seed := candidate.seed
                      variant := candidate.variant
                      start
                      step
                      replayKinds := reversedKinds.reverse
                      certificate := candidate.certificate
                      accepted := candidate.accepted
                      state
                      reachable
                      invariant
                      guard
                      newFailure := newEquation
                      failureStage := diagnoseNew candidate.certificate state } }
          | some _ =>
              match newGuard? candidate.certificate state with
              | none =>
                  { stats := {
                      base with
                        newSuccessStates := 1
                        newSuccessWithoutGuard := 1 } }
              | some _ =>
                  { stats := {
                      base with guardStates := 1, newSuccessStates := 1 } }
        match afterGuard.counterexample with
        | some _ => afterGuard
        | none =>
            match dispatchEquation :
                dispatch? candidate.certificate state invariant with
            | none =>
                afterGuard.addStats {
                  terminalRuns := 1
                  maxReplaySteps := step }
            | some result =>
                let nextReachable :=
                  reachable.dispatch invariant dispatchEquation
                let tail :=
                  inspectReachable candidate start result.after nextReachable
                    (state :: seen) (result.kind :: reversedKinds) (step + 1) fuel
                { stats := (afterGuard.addStats {
                      dispatchSteps := 1
                      maxReplaySteps := step }).stats.add tail.stats
                  counterexample := tail.counterexample }

def inspectStarts (candidate : CheckedCandidate) : List Vertex → SearchResult
  | [] => {}
  | start :: rest =>
      let attempt : AuditStats := { initializationAttempts := 1 }
      match initializationEquation :
          initializeReservation? candidate.certificate start with
      | none =>
          (inspectStarts candidate rest).addStats attempt
      | some initial =>
          let reachable :=
            dispatcher_reachable_of_initializeReservation?_eq_some
              initializationEquation
          let replay :=
            inspectReachable candidate start initial reachable [] [] 0
              (replayFuel candidate.certificate)
          let current : SearchResult :=
            { replay with
              stats := replay.stats.add
                { initializationAttempts := 1
                  initializationSuccesses := 1 } }
          match current.counterexample with
          | some _ => current
          | none =>
              let tail := inspectStarts candidate rest
              { stats := current.stats.add tail.stats
                counterexample := tail.counterexample }

def inspectVariantCase (depth seed : Nat) (variant : PositiveVariant) :
    Except String SearchResult :=
  if fastAccepted : variant.certificate.unificationCheck = true then
    let accepted : variant.certificate.check = true := by
      rw [← variant.certificate.unificationCheck_eq_check]
      exact fastAccepted
    let candidate : CheckedCandidate := {
      depth
      seed
      variant := variant.name
      certificate := variant.certificate
      accepted
      structural :=
        (variant.certificate.check_iff_declarativelyCorrect.mp accepted).1 }
    .ok <|
      (inspectStarts candidate
        (List.range variant.certificate.formulas.size)).addStats
          { checkedCertificates := 1 }
  else
    .error
      s!"generated positive variant rejected by unificationCheck: depth={depth}, seed={seed}, variant={variant.name}"

def inspectVariants (depth seed : Nat) : List PositiveVariant →
    Except String SearchResult
  | [] => .ok {}
  | variant :: rest => do
      let current ← inspectVariantCase depth seed variant
      match current.counterexample with
      | some _ => return current
      | none =>
          let tail ← inspectVariants depth seed rest
          return {
            stats := current.stats.add tail.stats
            counterexample := tail.counterexample }

def inspectBase (depth seed : Nat) : Except String SearchResult := do
  let tree := CutFreeDerivation.generate seed depth
  let certificate ← match tree.desequentialize? with
    | none =>
        throw s!"positive generator failed: depth={depth}, seed={seed}"
    | some certificate => pure certificate
  let result ← inspectVariants depth seed (positiveVariants certificate seed)
  return result.addStats { baseDerivations := 1 }

def inspectSeeds (depth : Nat) : List Nat → Except String SearchResult
  | [] => .ok {}
  | seed :: rest => do
      let current ← inspectBase depth seed
      match current.counterexample with
      | some _ => return current
      | none =>
          let tail ← inspectSeeds depth rest
          return {
            stats := current.stats.add tail.stats
            counterexample := tail.counterexample }

def inspectDepths (seedsPerDepth : Nat) : List Nat →
    Except String SearchResult
  | [] => .ok {}
  | depth :: rest => do
      let current ← inspectSeeds depth (List.range seedsPerDepth)
      match current.counterexample with
      | some _ => return current
      | none =>
          let tail ← inspectDepths seedsPerDepth rest
          return {
            stats := current.stats.add tail.stats
            counterexample := tail.counterexample }

def variantsPerCertificate : Nat := 6
def directCheckDepthCount : Nat := 3

structure AuditConfig where
  modeName : String
  depths : List Nat
  seedsPerDepth : Nat
  budgetMs : Nat
  requireGuardCoverage : Bool
  traceStarts : Bool

def defaultConfig : AuditConfig where
  modeName := "default"
  depths := List.range 5
  seedsPerDepth := 1
  budgetMs := 300_000
  requireGuardCoverage := true
  traceStarts := false

def extendedConfig : AuditConfig where
  modeName := "extended"
  depths := List.range 6
  seedsPerDepth := 1
  budgetMs := 1_800_000
  requireGuardCoverage := true
  traceStarts := false

def depthConfig (depth : Nat) : AuditConfig where
  modeName := s!"depth-{depth}"
  depths := [depth]
  seedsPerDepth := 1
  budgetMs := 1_800_000
  requireGuardCoverage := false
  traceStarts := false

def profileDepthConfig (depth : Nat) : AuditConfig :=
  { depthConfig depth with
    modeName := s!"profile-depth-{depth}"
    traceStarts := true }

def renderCounterexample (counterexample : Counterexample) : String :=
  s!"new-guard-counterexample depth={counterexample.depth} seed={counterexample.seed} " ++
    s!"variant={counterexample.variant} start={counterexample.start} " ++
    s!"step={counterexample.step} replay={repr counterexample.replayKinds} " ++
    s!"failure_stage={repr counterexample.failureStage}\n" ++
    s!"certificate={repr counterexample.certificate}\n" ++
    s!"state={repr counterexample.state}"

def renderStats (stats : AuditStats) : String :=
  s!"base_derivations={stats.baseDerivations} " ++
    s!"labelled_certificates={stats.checkedCertificates} " ++
    s!"direct_check_sentinels={stats.directCheckSentinels} " ++
    s!"initialization_attempts={stats.initializationAttempts} " ++
    s!"initialization_successes={stats.initializationSuccesses} " ++
    s!"initialization_failures={stats.initializationAttempts - stats.initializationSuccesses} " ++
    s!"reachable_states={stats.reachableStates} " ++
    s!"new_guard_states={stats.guardStates} " ++
    s!"new_success_states={stats.newSuccessStates} " ++
    s!"new_failure_states={stats.newFailureStates} " ++
    s!"new_success_without_guard={stats.newSuccessWithoutGuard} " ++
    s!"dispatch_steps={stats.dispatchSteps} " ++
    s!"terminal_runs={stats.terminalRuns} " ++
    s!"max_replay_steps={stats.maxReplaySteps} " ++
    s!"cycles={stats.cycleRuns} truncations={stats.truncatedRuns} " ++
    s!"checksum={stats.checksum}"

def validateReplayStats (stats : AuditStats) : Except String Unit := do
  if stats.newFailureStates != 0 then
    throw s!"reachable NewGuard/new? failures observed: {stats.newFailureStates}"
  if stats.newSuccessWithoutGuard != 0 then
    throw
      s!"new? succeeded without reconstructed NewGuard: {stats.newSuccessWithoutGuard}"
  if stats.guardStates != stats.newSuccessStates then
    throw
      s!"NewGuard/new? success count mismatch: {stats.guardStates} != {stats.newSuccessStates}"
  if stats.cycleRuns != 0 then
    throw s!"reachable replay cycle detected: {stats.cycleRuns}"
  if stats.truncatedRuns != 0 then
    throw s!"reachable replay fuel exhausted: {stats.truncatedRuns}"
  if stats.terminalRuns + stats.cycleRuns + stats.truncatedRuns !=
      stats.initializationSuccesses then
    throw "replay stop-reason counts do not partition successful initializations"

def requireValidStats (context : String) (stats : AuditStats) : IO Unit :=
  match validateReplayStats stats with
  | .ok () => pure ()
  | .error message => throw <| IO.userError s!"{context}: {message}"

def requireNoCounterexample (result : SearchResult) : IO Unit :=
  match result.counterexample with
  | none => pure ()
  | some counterexample =>
      throw <| IO.userError (renderCounterexample counterexample)

def inspectStartsIO (candidate : CheckedCandidate) : List Vertex →
    IO SearchResult
  | [] => pure {}
  | start :: rest => do
      IO.println
        s!"new-progress-audit-start-begin depth={candidate.depth} seed={candidate.seed} variant={candidate.variant} start={start}"
      (← IO.getStdout).flush
      let initializationStarted ← IO.monoMsNow
      match initializationEquation :
          initializeReservation? candidate.certificate start with
      | none =>
          let initializationElapsed :=
            (← IO.monoMsNow) - initializationStarted
          IO.println
            s!"new-progress-audit-start-ok depth={candidate.depth} seed={candidate.seed} variant={candidate.variant} start={start} initialization=none initialization_ms={initializationElapsed}"
          (← IO.getStdout).flush
          let tail ← inspectStartsIO candidate rest
          return tail.addStats { initializationAttempts := 1 }
      | some initial =>
          let initializationElapsed :=
            (← IO.monoMsNow) - initializationStarted
          let replayStarted ← IO.monoMsNow
          let reachable :=
            dispatcher_reachable_of_initializeReservation?_eq_some
              initializationEquation
          let replay :=
            inspectReachable candidate start initial reachable [] [] 0
              (replayFuel candidate.certificate)
          let replayElapsed := (← IO.monoMsNow) - replayStarted
          let current : SearchResult :=
            { replay with
              stats := replay.stats.add
                { initializationAttempts := 1
                  initializationSuccesses := 1 } }
          IO.println <|
            s!"new-progress-audit-start-ok depth={candidate.depth} seed={candidate.seed} " ++
              s!"variant={candidate.variant} start={start} initialization=some " ++
              s!"initialization_ms={initializationElapsed} replay_ms={replayElapsed} " ++
              renderStats current.stats
          (← IO.getStdout).flush
          match current.counterexample with
          | some _ => return current
          | none =>
              let tail ← inspectStartsIO candidate rest
              return {
                stats := current.stats.add tail.stats
                counterexample := tail.counterexample }

def runVariantsIO (config : AuditConfig) (depth seed : Nat) :
    List PositiveVariant →
    AuditStats → IO AuditStats
  | [], total => pure total
  | variant :: rest, total => do
      IO.println
        s!"new-progress-audit-certificate-start depth={depth} seed={seed} variant={variant.name}"
      (← IO.getStdout).flush
      let started ← IO.monoMsNow
      let checkStarted ← IO.monoMsNow
      let result ← if fastAccepted :
          variant.certificate.unificationCheck = true then
        let checkElapsed := (← IO.monoMsNow) - checkStarted
        IO.println
          s!"new-progress-audit-check-ok depth={depth} seed={seed} variant={variant.name} check=unificationCheck check_ms={checkElapsed}"
        (← IO.getStdout).flush
        let accepted : variant.certificate.check = true := by
          rw [← variant.certificate.unificationCheck_eq_check]
          exact fastAccepted
        let directSentinel ← if depth < directCheckDepthCount then
          let directStarted ← IO.monoMsNow
          if _directAccepted : variant.certificate.check = true then
            let directElapsed := (← IO.monoMsNow) - directStarted
            IO.println
              s!"new-progress-audit-direct-check-ok depth={depth} seed={seed} variant={variant.name} direct_check_ms={directElapsed}"
            (← IO.getStdout).flush
            pure 1
          else
            throw <| IO.userError
              s!"direct-check differential mismatch: depth={depth}, seed={seed}, variant={variant.name}"
        else
          pure 0
        let candidate : CheckedCandidate := {
          depth
          seed
          variant := variant.name
          certificate := variant.certificate
          accepted
          structural :=
            (variant.certificate.check_iff_declarativelyCorrect.mp accepted).1 }
        let replayStarted ← IO.monoMsNow
        let result ← if config.traceStarts then
          inspectStartsIO candidate
            (List.range variant.certificate.formulas.size)
        else
          pure <| inspectStarts candidate
            (List.range variant.certificate.formulas.size)
        let replayElapsed := (← IO.monoMsNow) - replayStarted
        IO.println
          s!"new-progress-audit-replay-ok depth={depth} seed={seed} variant={variant.name} replay_ms={replayElapsed}"
        (← IO.getStdout).flush
        pure <| result.addStats {
          checkedCertificates := 1
          directCheckSentinels := directSentinel }
      else
        throw <| IO.userError
          s!"generated positive variant rejected by unificationCheck: depth={depth}, seed={seed}, variant={variant.name}"
      let elapsed := (← IO.monoMsNow) - started
      requireNoCounterexample result
      requireValidStats
        s!"depth={depth} seed={seed} variant={variant.name}" result.stats
      IO.println <|
        s!"new-progress-audit-certificate-ok depth={depth} seed={seed} " ++
          s!"variant={variant.name} {renderStats result.stats} elapsed_ms={elapsed}"
      (← IO.getStdout).flush
      runVariantsIO config depth seed rest (total.add result.stats)

def runSeedIO (config : AuditConfig) (depth seed : Nat) : IO AuditStats := do
  IO.println s!"new-progress-audit-base-start depth={depth} seed={seed}"
  (← IO.getStdout).flush
  let started ← IO.monoMsNow
  let tree := CutFreeDerivation.generate seed depth
  let certificate ← match tree.desequentialize? with
    | none =>
        throw <| IO.userError
          s!"positive generator failed: depth={depth}, seed={seed}"
    | some certificate => pure certificate
  let elapsed := (← IO.monoMsNow) - started
  IO.println <|
    s!"new-progress-audit-base-ok depth={depth} seed={seed} " ++
      s!"formulas={certificate.formulas.size} links={certificate.links.length} " ++
      s!"pars={parCount certificate} " ++
      s!"generate_desequentialize_ms={elapsed}"
  (← IO.getStdout).flush
  let stats ← runVariantsIO config depth seed
    (positiveVariants certificate seed) {}
  return stats.add { baseDerivations := 1 }

def runSeedsIO (config : AuditConfig) (depth : Nat) :
    List Nat → AuditStats → IO AuditStats
  | [], total => pure total
  | seed :: rest, total => do
      let stats ← runSeedIO config depth seed
      runSeedsIO config depth rest (total.add stats)

def runDepthsIO (config : AuditConfig) : List Nat →
    AuditStats → IO AuditStats
  | [], total => pure total
  | depth :: rest, total => do
      let started ← IO.monoMsNow
      let stats ←
        runSeedsIO config depth (List.range config.seedsPerDepth) {}
      let elapsed := (← IO.monoMsNow) - started
      requireValidStats s!"depth={depth}" stats
      IO.println <|
        s!"new-progress-audit-depth-ok mode={config.modeName} depth={depth} " ++
          s!"{renderStats stats} elapsed_ms={elapsed}"
      (← IO.getStdout).flush
      runDepthsIO config rest (total.add stats)

def parseConfig (args : List String) : Except String AuditConfig :=
  match args with
  | [] => .ok defaultConfig
  | ["--extended"] => .ok extendedConfig
  | ["--depth", value] =>
      match value.toNat? with
      | some depth => .ok (depthConfig depth)
      | none => .error s!"invalid depth: {value}"
  | ["--profile-depth", value] =>
      match value.toNat? with
      | some depth => .ok (profileDepthConfig depth)
      | none => .error s!"invalid depth: {value}"
  | _ => .error
      "usage: proofnet_ir_new_progress_audit [--extended | --depth N | --profile-depth N]"

/-- Run the bounded audit. Any witness is treated as a hard regression and is
printed with its complete certificate, state, initialization start, dispatcher
rule trace, and first failing `new?` stage. -/
def run (config : AuditConfig) : IO Unit := do
  let started ← IO.monoMsNow
  let stats ← runDepthsIO config config.depths {}
  let elapsed := (← IO.monoMsNow) - started
  let expectedBaseDerivations := config.seedsPerDepth * config.depths.length
  let expectedCheckedCertificates :=
    expectedBaseDerivations * variantsPerCertificate
  let expectedDirectCheckSentinels :=
    config.seedsPerDepth * variantsPerCertificate *
      (config.depths.filter fun depth ↦ depth < directCheckDepthCount).length
  requireValidStats s!"mode={config.modeName}" stats
  if stats.baseDerivations != expectedBaseDerivations then
    throw <| IO.userError
      s!"unexpected base count: {stats.baseDerivations} != {expectedBaseDerivations}"
  if stats.checkedCertificates != expectedCheckedCertificates then
    throw <| IO.userError
      s!"unexpected checked-certificate count: {stats.checkedCertificates} != {expectedCheckedCertificates}"
  if stats.directCheckSentinels != expectedDirectCheckSentinels then
    throw <| IO.userError
      s!"unexpected direct-check sentinel count: {stats.directCheckSentinels} != {expectedDirectCheckSentinels}"
  if stats.initializationSuccesses == 0 then
    throw <| IO.userError "audit exercised no successful initializations"
  if stats.reachableStates == 0 then
    throw <| IO.userError "audit exercised no dispatcher-reachable states"
  if config.requireGuardCoverage && stats.guardStates == 0 then
    throw <| IO.userError "audit exercised no reachable NewGuard states"
  if elapsed > config.budgetMs then
    throw <| IO.userError
      s!"new-progress audit budget exceeded: {elapsed}ms > {config.budgetMs}ms"
  IO.println <|
    s!"new-progress-audit-ok mode={config.modeName} " ++
      s!"depths={repr config.depths} seeds_per_depth={config.seedsPerDepth} " ++
      s!"variants_per_certificate={variantsPerCertificate} " ++
      s!"{renderStats stats} " ++
      s!"replay_fuel=16*(formulas+links+1) " ++
      s!"elapsed_ms={elapsed} budget_ms={config.budgetMs}"

end ProofNetIRNewProgressAudit

def main (args : List String) : IO Unit := do
  let config ← match ProofNetIRNewProgressAudit.parseConfig args with
    | .ok config => pure config
    | .error message => throw <| IO.userError message
  ProofNetIRNewProgressAudit.run config
