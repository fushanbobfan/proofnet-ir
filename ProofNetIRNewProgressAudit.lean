import ProofNetIR

open ProofNetIR

namespace ProofNetIRNewProgressAudit

open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerState

/-!
# Finite reachable-state audit for Figure-7 New, Wait, and Forward geometry

This executable searches only states produced by a successful
`initializeReservation?` followed by zero or more successful canonical
`dispatch?` calls. It looks for the finite counterexample shape

`certificate.check = true ∧ ReachableByImplementedDispatcher certificate state ∧
  Nonempty (NewGuard certificate state) ∧ new? certificate state invariant = none`.

The default and extended modes search the shallow-New counterexample above.
`--cross-representative-search` additionally decodes every successful New,
Wait, and Forward in the same replay, reconstructs the chronological
reservation ledger, and checks every rule-created future-New candidate against
every strictly older representative event for intersecting source-left
regions. Its coverage gates require successful steps, created candidates, and
strict older-event pairs. `--wait-search` remains a compatibility spelling for
the same combined finite search.

The search is deterministic and finite. Absence of either witness is regression
evidence over the constants below, not a progress theorem, NewGuard sufficiency,
or an unconditional New/Wait/Forward preservation theorem. Labelled variants may denote equal
certificates; the reported count is a count of labelled audit cases, not a
uniqueness or statistical-independence claim. Default CI covers depths zero
through four; `--extended` adds depth five; both cross-representative spellings
use fixed depth five and seeds zero through fifteen; `--profile-depth N` prints
every phase. Candidate
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

/-- The executable audit needs only the chronological event root and its raw
age. The pair is maintained from the exact initialization start and every
successful dispatcher `new`; it is checked against the state's raw-age
horizon at every replay state. This is audit data, not a replacement for the
proof-relevant reservation ledger. -/
structure AuditReservation where
  rawAge : RawTokenAge
  start : Vertex
  deriving Repr, DecidableEq

/-- A finite witness that one Wait-created candidate violated the proposed
cross-representative separation geometry.  Every field is executable audit
data so a failure can be frozen as a later theorem-level regression. -/
structure WaitRegionCounterexample where
  depth : Nat
  seed : Nat
  variant : String
  initializationStart : Vertex
  step : Nat
  replayKinds : List Figure7RuleKind
  certificate : Certificate
  before : ReservationState
  after : ReservationState
  event : AuditReservation
  eventRepresentative : Nat
  boundary : RawTokenAge
  boundaryRepresentative : Nat
  insertedConclusion : Vertex
  tensorMate : Vertex
  eventRegion : List Vertex
  candidateRegion : List Vertex
  deriving Repr

/-- A finite witness that one Forward-created candidate violated the proposed
cross-representative separation geometry. This is executable audit data, not an
unconditional preservation theorem. -/
structure ForwardRegionCounterexample where
  depth : Nat
  seed : Nat
  variant : String
  initializationStart : Vertex
  step : Nat
  replayKinds : List Figure7RuleKind
  certificate : Certificate
  before : ReservationState
  after : ReservationState
  event : AuditReservation
  eventRepresentative : Nat
  boundary : RawTokenAge
  boundaryRepresentative : Nat
  insertedConclusion : Vertex
  tensorMate : Vertex
  eventRegion : List Vertex
  candidateRegion : List Vertex
  deriving Repr

/-- A finite witness that one endpoint appended by New created a candidate
whose complete source-left region intersects a strictly older prior event. -/
structure NewRegionCounterexample where
  depth : Nat
  seed : Nat
  variant : String
  initializationStart : Vertex
  step : Nat
  replayKinds : List Figure7RuleKind
  certificate : Certificate
  before : ReservationState
  after : ReservationState
  event : AuditReservation
  eventRepresentative : Nat
  freshRawAge : RawTokenAge
  freshRepresentative : Nat
  createdAtReached : Bool
  insertedEndpoint : Vertex
  tensorMate : Vertex
  eventRegion : List Vertex
  candidateRegion : List Vertex
  deriving Repr

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
  newSteps : Nat := 0
  newCreatedCandidates : Nat := 0
  newCreatedReachedCandidates : Nat := 0
  newCreatedPartnerCandidates : Nat := 0
  newOrderedEventPairs : Nat := 0
  newRegionIntersections : Nat := 0
  newDecodeFailures : Nat := 0
  newRepresentativeFailures : Nat := 0
  newLedgerFailures : Nat := 0
  newRegionComputationFailures : Nat := 0
  waitSteps : Nat := 0
  waitCreatedCandidates : Nat := 0
  waitOrderedEventPairs : Nat := 0
  waitRegionIntersections : Nat := 0
  waitDecodeFailures : Nat := 0
  regionComputationFailures : Nat := 0
  forwardSteps : Nat := 0
  forwardCreatedCandidates : Nat := 0
  forwardOrderedEventPairs : Nat := 0
  forwardRegionIntersections : Nat := 0
  forwardDecodeFailures : Nat := 0
  forwardRegionComputationFailures : Nat := 0
  ledgerDecodeFailures : Nat := 0
  ledgerLengthMismatches : Nat := 0
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
  newSteps := left.newSteps + right.newSteps
  newCreatedCandidates :=
    left.newCreatedCandidates + right.newCreatedCandidates
  newCreatedReachedCandidates :=
    left.newCreatedReachedCandidates + right.newCreatedReachedCandidates
  newCreatedPartnerCandidates :=
    left.newCreatedPartnerCandidates + right.newCreatedPartnerCandidates
  newOrderedEventPairs :=
    left.newOrderedEventPairs + right.newOrderedEventPairs
  newRegionIntersections :=
    left.newRegionIntersections + right.newRegionIntersections
  newDecodeFailures := left.newDecodeFailures + right.newDecodeFailures
  newRepresentativeFailures :=
    left.newRepresentativeFailures + right.newRepresentativeFailures
  newLedgerFailures :=
    left.newLedgerFailures + right.newLedgerFailures
  newRegionComputationFailures :=
    left.newRegionComputationFailures + right.newRegionComputationFailures
  waitSteps := left.waitSteps + right.waitSteps
  waitCreatedCandidates :=
    left.waitCreatedCandidates + right.waitCreatedCandidates
  waitOrderedEventPairs :=
    left.waitOrderedEventPairs + right.waitOrderedEventPairs
  waitRegionIntersections :=
    left.waitRegionIntersections + right.waitRegionIntersections
  waitDecodeFailures := left.waitDecodeFailures + right.waitDecodeFailures
  regionComputationFailures :=
    left.regionComputationFailures + right.regionComputationFailures
  forwardSteps := left.forwardSteps + right.forwardSteps
  forwardCreatedCandidates :=
    left.forwardCreatedCandidates + right.forwardCreatedCandidates
  forwardOrderedEventPairs :=
    left.forwardOrderedEventPairs + right.forwardOrderedEventPairs
  forwardRegionIntersections :=
    left.forwardRegionIntersections + right.forwardRegionIntersections
  forwardDecodeFailures :=
    left.forwardDecodeFailures + right.forwardDecodeFailures
  forwardRegionComputationFailures :=
    left.forwardRegionComputationFailures +
      right.forwardRegionComputationFailures
  ledgerDecodeFailures :=
    left.ledgerDecodeFailures + right.ledgerDecodeFailures
  ledgerLengthMismatches :=
    left.ledgerLengthMismatches + right.ledgerLengthMismatches
  maxReplaySteps := max left.maxReplaySteps right.maxReplaySteps
  checksum := left.checksum + right.checksum

structure SearchResult where
  stats : AuditStats := {}
  counterexample : Option Counterexample := none
  newRegionCounterexample : Option NewRegionCounterexample := none
  waitCounterexample : Option WaitRegionCounterexample := none
  forwardCounterexample : Option ForwardRegionCounterexample := none

def SearchResult.addStats (result : SearchResult) (stats : AuditStats) : SearchResult :=
  { result with stats := result.stats.add stats }

def SearchResult.hasCounterexample (result : SearchResult) : Bool :=
  result.counterexample.isSome || result.newRegionCounterexample.isSome ||
    result.waitCounterexample.isSome || result.forwardCounterexample.isSome

def stateChecksum (state : ReservationState) : Nat :=
  state.stack.nextAge + state.stack.sigma.length +
    state.stack.ready.flatten.length + state.stack.waitingVertices.length +
    state.core.startedAxioms + state.core.firedConnectives

/-- Conservative finite replay fuel. Zero truncations are required by the
executable gate, so this bound is observable rather than silently assumed. -/
def replayFuel (certificate : Certificate) : Nat :=
  16 * (certificate.formulas.size + certificate.links.length + 1)

/-- Compute the complete structurally determined source-left region used by
the finite New/Wait/Forward audit. The list contains every recursively visited
stored-left source and the other endpoint of the terminal axiom. Accepted certificates
have singleton source buckets; every other shape fails closed. -/
def sourceLeftRegion? (certificate : Certificate) :
    Nat → Vertex → Option (List Vertex)
  | 0, _ => none
  | fuel + 1, vertex =>
      match
          (ProofNetIR.SequentialUnification.sourceIndex certificate)[vertex]?
      with
      | some [source] =>
          match source.link with
          | .axiom left right =>
              if vertex = left then
                some [vertex, right]
              else if vertex = right then
                some [vertex, left]
              else
                none
          | .tensor left _ conclusion
          | .par left _ conclusion =>
              if vertex = conclusion then
                match sourceLeftRegion? certificate fuel left with
                | none => none
                | some region => some (vertex :: region)
              else
                none
      | _ => none

def sourceRegionFuel (certificate : Certificate) : Nat :=
  certificate.formulas.size + 1

abbrev SourceRegionCache := Array (Option (List Vertex))

/-- Cache the exact complete source-left computation once per certificate and
vertex. An outer lookup miss and a cached inner `none` both remain fail-closed
at each audited ordered pair. -/
def sourceRegionCache (certificate : Certificate) : SourceRegionCache :=
  (List.range certificate.formulas.size |>.map fun vertex ↦
    sourceLeftRegion? certificate (sourceRegionFuel certificate) vertex).toArray

def regionsIntersect (first second : List Vertex) : Bool :=
  first.any fun vertex ↦ second.contains vertex

structure NewCandidateInspection where
  stats : AuditStats := {}
  counterexample : Option NewRegionCounterexample := none

def NewCandidateInspection.add
    (left right : NewCandidateInspection) : NewCandidateInspection where
  stats := left.stats.add right.stats
  counterexample :=
    match left.counterexample with
    | some witness => some witness
    | none => right.counterexample

structure NewInspection where
  stats : AuditStats := {}
  counterexample : Option NewRegionCounterexample := none
  reservation : Option AuditReservation := none

def inspectNewEvent (candidate : CheckedCandidate)
    (regionCache : SourceRegionCache)
    (initializationStart replayStep : Nat)
    (replayKinds : List Figure7RuleKind)
    (before markedMiddle after : ReservationState)
    (freshRawAge : RawTokenAge) (createdAtReached : Bool)
    (insertedEndpoint tensorMate : Vertex)
    (event : AuditReservation) : NewCandidateInspection :=
  let eventBeforeRepresentative :=
    before.core.representative event.rawAge
  let eventMiddleRepresentative :=
    markedMiddle.core.representative event.rawAge
  let eventAfterRepresentative :=
    after.core.representative event.rawAge
  let freshMiddleRepresentative :=
    markedMiddle.core.representative freshRawAge
  let freshAfterRepresentative := after.core.representative freshRawAge
  if eventBeforeRepresentative != eventMiddleRepresentative then
    { stats := { newRepresentativeFailures := 1 } }
  else if eventAfterRepresentative != eventMiddleRepresentative then
    { stats := { newRepresentativeFailures := 1 } }
  else if freshAfterRepresentative != freshMiddleRepresentative then
    { stats := { newRepresentativeFailures := 1 } }
  else if eventMiddleRepresentative < freshMiddleRepresentative then
    if eventAfterRepresentative < freshAfterRepresentative then
      match regionCache[event.start]?, regionCache[tensorMate]? with
      | some (some eventRegion), some (some candidateRegion) =>
          if regionsIntersect eventRegion candidateRegion then
            { stats := {
                newOrderedEventPairs := 1
                newRegionIntersections := 1 }
              counterexample := some {
                depth := candidate.depth
                seed := candidate.seed
                variant := candidate.variant
                initializationStart
                step := replayStep
                replayKinds
                certificate := candidate.certificate
                before
                after
                event
                eventRepresentative := eventMiddleRepresentative
                freshRawAge
                freshRepresentative := freshMiddleRepresentative
                createdAtReached
                insertedEndpoint
                tensorMate
                eventRegion
                candidateRegion } }
          else
            { stats := { newOrderedEventPairs := 1 } }
      | _, _ =>
          { stats := {
              newOrderedEventPairs := 1
              newRegionComputationFailures := 1 } }
    else
      { stats := { newRepresentativeFailures := 1 } }
  else if eventAfterRepresentative < freshAfterRepresentative then
    { stats := { newRepresentativeFailures := 1 } }
  else
    {}

def inspectNewEvents (candidate : CheckedCandidate)
    (regionCache : SourceRegionCache)
    (initializationStart replayStep : Nat)
    (replayKinds : List Figure7RuleKind)
    (before markedMiddle after : ReservationState)
    (freshRawAge : RawTokenAge) (createdAtReached : Bool)
    (insertedEndpoint tensorMate : Vertex) :
    List AuditReservation → NewCandidateInspection
  | [] => {}
  | event :: rest =>
      (inspectNewEvent candidate regionCache initializationStart replayStep
        replayKinds before markedMiddle after freshRawAge createdAtReached
        insertedEndpoint tensorMate event).add
        (inspectNewEvents candidate regionCache initializationStart replayStep
          replayKinds before markedMiddle after freshRawAge createdAtReached
          insertedEndpoint tensorMate rest)

def inspectNewCreatedEndpoint (candidate : CheckedCandidate)
    (regionCache : SourceRegionCache)
    (initializationStart replayStep : Nat)
    (replayKinds : List Figure7RuleKind)
    (before markedMiddle after : ReservationState)
    (freshRawAge : RawTokenAge) (createdAtReached : Bool)
    (insertedEndpoint : Vertex) (events : List AuditReservation) :
    NewCandidateInspection :=
  match candidate.certificate.tensorBelow? insertedEndpoint with
  | none => {}
  | some tensor =>
      if markedMiddle.core.marks[tensor.mate]? == some none &&
          after.core.marks[tensor.mate]? == some none then
        let inspected :=
          inspectNewEvents candidate regionCache initializationStart replayStep
            replayKinds before markedMiddle after freshRawAge createdAtReached
            insertedEndpoint tensor.mate events
        let createdStats : AuditStats :=
          if createdAtReached then
            { newCreatedCandidates := 1
              newCreatedReachedCandidates := 1 }
          else
            { newCreatedCandidates := 1
              newCreatedPartnerCandidates := 1 }
        { inspected with stats := inspected.stats.add createdStats }
      else
        {}

/-- Fail-closed replay of one successful dispatcher New. The event is exposed
only after every operational stage reproduces the exact dispatcher output. -/
def inspectNewTransition (candidate : CheckedCandidate)
    (regionCache : SourceRegionCache)
    (initializationStart replayStep : Nat)
    (replayKinds : List Figure7RuleKind)
    (before after : ReservationState) (events : List AuditReservation) :
    NewInspection :=
  let decodeFailure : NewInspection :=
    { stats := { newSteps := 1, newDecodeFailures := 1 } }
  match before.stack.popReadyMark? with
  | .error _ => decodeFailure
  | .ok stackResult =>
      match
          before.core.markReadyRaw?
            stackResult.vertex stackResult.rawAge with
      | .error _ => decodeFailure
      | .ok coreMarked =>
          match candidate.certificate.tensorBelow? stackResult.vertex with
          | none => decodeFailure
          | some tensor =>
              match
                  SequentialUnification.nextAxiom? candidate.certificate
                    coreMarked
                    (SequentialUnification.sourceIndex candidate.certificate)
                    (SequentialUnification.sourceIndex_sound
                      candidate.certificate)
                    before.tags tensor.mate with
              | none => decodeFailure
              | some search =>
                  match search.orientedEndpoints? with
                  | none => decodeFailure
                  | some (reached, partner) =>
                      match
                          stackResult.after.operationalNewEnqueue?
                            reached partner with
                      | none => decodeFailure
                      | some stackAfter =>
                          match
                              candidate.certificate.reserveAxiomAt?
                                coreMarked search.linkIndex with
                          | none => decodeFailure
                          | some coreAfter =>
                              let decodedAfter : ReservationState := {
                                stack := stackAfter
                                core := coreAfter
                                tags := search.tags }
                              if after = decodedAfter then
                                let markedMiddle : ReservationState := {
                                  stack := stackResult.after
                                  core := coreMarked
                                  tags := before.tags }
                                let freshRawAge := before.stack.nextAge
                                let reservation : AuditReservation := {
                                  rawAge := freshRawAge
                                  start := tensor.mate }
                                let appendedEvents := events ++ [reservation]
                                let priorRawAges :=
                                  events.map AuditReservation.rawAge
                                let appendedRawAges :=
                                  appendedEvents.map AuditReservation.rawAge
                                let ledgerOk :=
                                  events.length == freshRawAge &&
                                  priorRawAges == List.range freshRawAge &&
                                  appendedEvents.length ==
                                    after.stack.nextAge &&
                                  appendedRawAges ==
                                    List.range after.stack.nextAge &&
                                  after.stack.nextAge == freshRawAge + 1 &&
                                  !(events.any fun event ↦
                                    event.rawAge == freshRawAge)
                                let oldMiddleStable :=
                                  events.all fun event ↦
                                    before.core.representative event.rawAge ==
                                      markedMiddle.core.representative
                                        event.rawAge
                                let oldAfterStable :=
                                  events.all fun event ↦
                                    after.core.representative event.rawAge ==
                                      markedMiddle.core.representative
                                        event.rawAge
                                let freshMiddleRepresentative :=
                                  markedMiddle.core.representative freshRawAge
                                let freshAfterRepresentative :=
                                  after.core.representative freshRawAge
                                let representativesOk :=
                                  oldMiddleStable && oldAfterStable &&
                                  coreMarked.parents == before.core.parents &&
                                  freshMiddleRepresentative == freshRawAge &&
                                  freshAfterRepresentative == freshRawAge &&
                                  decide (freshRawAge < after.stack.nextAge) &&
                                  !(decide (freshAfterRepresentative <
                                    freshAfterRepresentative))
                                let reachedInspection :=
                                  inspectNewCreatedEndpoint candidate regionCache
                                    initializationStart replayStep replayKinds
                                    before markedMiddle after freshRawAge true
                                    reached events
                                let partnerInspection :=
                                  inspectNewCreatedEndpoint candidate regionCache
                                    initializationStart replayStep replayKinds
                                    before markedMiddle after freshRawAge false
                                    partner events
                                let createdInspection :=
                                  reachedInspection.add partnerInspection
                                let baseStats : AuditStats := {
                                  newSteps := 1
                                  newLedgerFailures :=
                                    if ledgerOk then 0 else 1
                                  newRepresentativeFailures :=
                                    if representativesOk then 0 else 1 }
                                { stats :=
                                    baseStats.add createdInspection.stats
                                  counterexample :=
                                    createdInspection.counterexample
                                  reservation := some reservation }
                              else
                                decodeFailure

structure WaitInspection where
  stats : AuditStats := {}
  counterexample : Option WaitRegionCounterexample := none

def WaitInspection.add (left right : WaitInspection) : WaitInspection where
  stats := left.stats.add right.stats
  counterexample :=
    match left.counterexample with
    | some witness => some witness
    | none => right.counterexample

def inspectWaitEvent (candidate : CheckedCandidate)
    (regionCache : SourceRegionCache)
    (initializationStart replayStep : Nat)
    (replayKinds : List Figure7RuleKind)
    (before after : ReservationState) (boundary : RawTokenAge)
    (insertedConclusion tensorMate : Vertex)
    (event : AuditReservation) : WaitInspection :=
  let eventRepresentative := after.core.representative event.rawAge
  let boundaryRepresentative := after.core.representative boundary
  if eventRepresentative < boundaryRepresentative then
    match regionCache[event.start]?, regionCache[tensorMate]? with
    | some (some eventRegion), some (some candidateRegion) =>
        if regionsIntersect eventRegion candidateRegion then
          { stats := {
              waitOrderedEventPairs := 1
              waitRegionIntersections := 1 }
            counterexample := some {
              depth := candidate.depth
              seed := candidate.seed
              variant := candidate.variant
              initializationStart
              step := replayStep
              replayKinds
              certificate := candidate.certificate
              before
              after
              event
              eventRepresentative
              boundary
              boundaryRepresentative
              insertedConclusion
              tensorMate
              eventRegion
              candidateRegion } }
        else
          { stats := { waitOrderedEventPairs := 1 } }
    | _, _ =>
        { stats := {
            waitOrderedEventPairs := 1
            regionComputationFailures := 1 } }
  else
    {}

def inspectWaitEvents (candidate : CheckedCandidate)
    (regionCache : SourceRegionCache)
    (initializationStart replayStep : Nat)
    (replayKinds : List Figure7RuleKind)
    (before after : ReservationState) (boundary : RawTokenAge)
    (insertedConclusion tensorMate : Vertex) :
    List AuditReservation → WaitInspection
  | [] => {}
  | event :: rest =>
      (inspectWaitEvent candidate regionCache initializationStart replayStep
        replayKinds before after boundary insertedConclusion tensorMate
        event).add
        (inspectWaitEvents candidate regionCache initializationStart replayStep
          replayKinds before after boundary insertedConclusion tensorMate rest)

/-- Inspect one successful dispatcher Wait.  Reconstructing the selected par,
its older boundary, and the inserted payload from the input state must succeed;
otherwise the audit records a fail-closed decoder drift.  Absence of a tensor
below the inserted conclusion, or a marked tensor mate, is a valid Wait with no
new candidate. -/
def inspectWaitTransition (candidate : CheckedCandidate)
    (regionCache : SourceRegionCache)
    (initializationStart replayStep : Nat)
    (replayKinds : List Figure7RuleKind)
    (before after : ReservationState) (events : List AuditReservation) :
    WaitInspection :=
  let decodeFailure : WaitInspection :=
    { stats := { waitSteps := 1, waitDecodeFailures := 1 } }
  match before.stack.ready.getLast? with
  | some (selected :: _) =>
      match candidate.certificate.connectiveBelow? selected with
      | some consumer =>
          if consumer.kind == .par then
            match before.core.marks[consumer.mate]? with
            | some (some mateRawAge) =>
                match sigmaBoundary? before.stack.sigma mateRawAge with
                | some boundary =>
                    match before.stack.waiting[boundary]?,
                        after.stack.waiting[boundary]? with
                    | some (.initialized oldPayload),
                        some (.initialized afterPayload) =>
                        if afterPayload = consumer.conclusion :: oldPayload then
                          match
                              candidate.certificate.tensorBelow?
                                consumer.conclusion with
                          | none => { stats := { waitSteps := 1 } }
                          | some tensor =>
                              if after.core.marks[tensor.mate]? == some none then
                                let inspected :=
                                  inspectWaitEvents candidate regionCache
                                    initializationStart replayStep replayKinds
                                    before after boundary consumer.conclusion
                                    tensor.mate events
                                { inspected with
                                  stats := inspected.stats.add {
                                    waitSteps := 1
                                    waitCreatedCandidates := 1 } }
                              else
                                { stats := { waitSteps := 1 } }
                        else
                          decodeFailure
                    | _, _ => decodeFailure
                | none => decodeFailure
            | _ => decodeFailure
          else
            decodeFailure
      | none => decodeFailure
  | _ => decodeFailure

structure ForwardInspection where
  stats : AuditStats := {}
  counterexample : Option ForwardRegionCounterexample := none

def ForwardInspection.add (left right : ForwardInspection) : ForwardInspection where
  stats := left.stats.add right.stats
  counterexample :=
    match left.counterexample with
    | some witness => some witness
    | none => right.counterexample

def inspectForwardEvent (candidate : CheckedCandidate)
    (regionCache : SourceRegionCache)
    (initializationStart replayStep : Nat)
    (replayKinds : List Figure7RuleKind)
    (before after : ReservationState) (boundary : RawTokenAge)
    (insertedConclusion tensorMate : Vertex)
    (event : AuditReservation) : ForwardInspection :=
  let eventRepresentative := after.core.representative event.rawAge
  let boundaryRepresentative := after.core.representative boundary
  if eventRepresentative < boundaryRepresentative then
    match regionCache[event.start]?, regionCache[tensorMate]? with
    | some (some eventRegion), some (some candidateRegion) =>
        if regionsIntersect eventRegion candidateRegion then
          { stats := {
              forwardOrderedEventPairs := 1
              forwardRegionIntersections := 1 }
            counterexample := some {
              depth := candidate.depth
              seed := candidate.seed
              variant := candidate.variant
              initializationStart
              step := replayStep
              replayKinds
              certificate := candidate.certificate
              before
              after
              event
              eventRepresentative
              boundary
              boundaryRepresentative
              insertedConclusion
              tensorMate
              eventRegion
              candidateRegion } }
        else
          { stats := { forwardOrderedEventPairs := 1 } }
    | _, _ =>
        { stats := {
            forwardOrderedEventPairs := 1
            forwardRegionComputationFailures := 1 } }
  else
    {}

def inspectForwardEvents (candidate : CheckedCandidate)
    (regionCache : SourceRegionCache)
    (initializationStart replayStep : Nat)
    (replayKinds : List Figure7RuleKind)
    (before after : ReservationState) (boundary : RawTokenAge)
    (insertedConclusion tensorMate : Vertex) :
    List AuditReservation → ForwardInspection
  | [] => {}
  | event :: rest =>
      (inspectForwardEvent candidate regionCache initializationStart replayStep
        replayKinds before after boundary insertedConclusion tensorMate
        event).add
        (inspectForwardEvents candidate regionCache initializationStart
          replayStep replayKinds before after boundary insertedConclusion
          tensorMate rest)

/-- Inspect one successful dispatcher Forward. The decoder independently
replays the exact common preparation, submitted par lookup, paper guards,
production queue, and ready prepend, and requires their complete output to equal `after`.
Absence of a tensor below the prepended conclusion, or a marked tensor mate, is
a valid Forward with no created candidate. Every decoder mismatch fails closed. -/
def inspectForwardTransition (candidate : CheckedCandidate)
    (regionCache : SourceRegionCache)
    (initializationStart replayStep : Nat)
    (replayKinds : List Figure7RuleKind)
    (before after : ReservationState) (events : List AuditReservation) :
    ForwardInspection :=
  let decodeFailure : ForwardInspection :=
    { stats := { forwardSteps := 1, forwardDecodeFailures := 1 } }
  match prepare? before with
  | none => decodeFailure
  | some prepared =>
      match
          candidate.certificate.connectiveBelow?
            prepared.stackResult.vertex with
      | none => decodeFailure
      | some consumer =>
          if consumer.kind == .par then
            match prepared.coreMarked.marks[consumer.mate]? with
            | some (some mateRawAge) =>
                if prepared.stackResult.rawAge ≤ mateRawAge then
                  if (consumer.conclusion ::
                      prepared.stackResult.remainingTop).Nodup then
                    match
                        Certificate.queuePar? prepared.coreMarked
                          consumer.storedLeft consumer.storedRight
                          consumer.conclusion with
                    | none => decodeFailure
                    | some coreAfter =>
                        match
                            prepared.stackResult.after.prependReadyTop?
                              consumer.conclusion with
                        | none => decodeFailure
                        | some stackAfter =>
                            let decodedAfter : ReservationState := {
                              stack := stackAfter
                              core := coreAfter
                              tags := before.tags }
                            if after = decodedAfter then
                              match
                                  candidate.certificate.tensorBelow?
                                    consumer.conclusion with
                              | none => { stats := { forwardSteps := 1 } }
                              | some tensor =>
                                  if after.core.marks[tensor.mate]? == some none then
                                    let inspected :=
                                      inspectForwardEvents candidate regionCache
                                        initializationStart replayStep
                                        replayKinds before after
                                        prepared.stackResult.rawAge
                                        consumer.conclusion tensor.mate events
                                    { inspected with
                                      stats := inspected.stats.add {
                                        forwardSteps := 1
                                        forwardCreatedCandidates := 1 } }
                                  else
                                    { stats := { forwardSteps := 1 } }
                            else
                              decodeFailure
                  else
                    decodeFailure
                else
                  decodeFailure
            | _ => decodeFailure
          else
            decodeFailure

def parCount (certificate : Certificate) : Nat :=
  certificate.links.foldl (fun count link ↦
    match link with
    | .par _ _ _ => count + 1
    | _ => count) 0

def inspectReachable (candidate : CheckedCandidate)
    (regionCache : SourceRegionCache) (start : Vertex)
    (state : ReservationState)
    (reachable : ReachableByImplementedDispatcher candidate.certificate state)
    (events : List AuditReservation)
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
          ledgerLengthMismatches :=
            if events.length == state.stack.nextAge then 0 else 1
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
          ledgerLengthMismatches :=
            if events.length == state.stack.nextAge then 0 else 1
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
                let newInspection :=
                  if result.kind == .new then
                    inspectNewTransition candidate regionCache start step
                      (result.kind :: reversedKinds).reverse state result.after
                      events
                  else
                    {}
                let waitInspection :=
                  if result.kind == .wait then
                    inspectWaitTransition candidate regionCache start step
                      (result.kind :: reversedKinds).reverse state result.after
                      events
                  else
                    {}
                let forwardInspection :=
                  if result.kind == .forward then
                    inspectForwardTransition candidate regionCache start step
                      (result.kind :: reversedKinds).reverse state result.after
                      events
                  else
                    {}
                let nextEventsAndStats : List AuditReservation × AuditStats :=
                  if result.kind == .new then
                    match newInspection.reservation with
                    | some reservation =>
                        (events ++ [reservation], {})
                    | none =>
                        (events, { ledgerDecodeFailures := 1 })
                  else
                    (events, {})
                let currentStats :=
                  (afterGuard.addStats {
                    dispatchSteps := 1
                    maxReplaySteps := step }).stats |>.add
                    newInspection.stats |>.add waitInspection.stats |>.add
                    forwardInspection.stats |>.add nextEventsAndStats.2
                match newInspection.counterexample with
                | some witness =>
                    { stats := currentStats
                      newRegionCounterexample := some witness }
                | none =>
                    match waitInspection.counterexample with
                    | some witness =>
                        { stats := currentStats
                          waitCounterexample := some witness }
                    | none =>
                        match forwardInspection.counterexample with
                        | some witness =>
                            { stats := currentStats
                              forwardCounterexample := some witness }
                        | none =>
                            let tail :=
                              inspectReachable candidate regionCache start
                                result.after
                                nextReachable nextEventsAndStats.1
                                (state :: seen)
                                (result.kind :: reversedKinds) (step + 1) fuel
                            { stats := currentStats.add tail.stats
                              counterexample := tail.counterexample
                              newRegionCounterexample :=
                                tail.newRegionCounterexample
                              waitCounterexample := tail.waitCounterexample
                              forwardCounterexample :=
                                tail.forwardCounterexample }

def inspectStarts (candidate : CheckedCandidate)
    (regionCache : SourceRegionCache) : List Vertex → SearchResult
  | [] => {}
  | start :: rest =>
      let attempt : AuditStats := { initializationAttempts := 1 }
      match initializationEquation :
          initializeReservation? candidate.certificate start with
      | none =>
          (inspectStarts candidate regionCache rest).addStats attempt
      | some initial =>
          let reachable :=
            dispatcher_reachable_of_initializeReservation?_eq_some
              initializationEquation
          let replay :=
            inspectReachable candidate regionCache start initial reachable
              [{ rawAge := 0, start }] [] [] 0
              (replayFuel candidate.certificate)
          let current : SearchResult :=
            { replay with
              stats := replay.stats.add
                { initializationAttempts := 1
                  initializationSuccesses := 1 } }
          if current.hasCounterexample then
            current
          else
            let tail := inspectStarts candidate regionCache rest
            { stats := current.stats.add tail.stats
              counterexample := tail.counterexample
              newRegionCounterexample := tail.newRegionCounterexample
              waitCounterexample := tail.waitCounterexample
              forwardCounterexample := tail.forwardCounterexample }

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
    let regionCache := sourceRegionCache candidate.certificate
    .ok <|
      (inspectStarts candidate regionCache
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
      if current.hasCounterexample then
        return current
      else
        let tail ← inspectVariants depth seed rest
        return {
          stats := current.stats.add tail.stats
          counterexample := tail.counterexample
          newRegionCounterexample := tail.newRegionCounterexample
          waitCounterexample := tail.waitCounterexample
          forwardCounterexample := tail.forwardCounterexample }

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
      if current.hasCounterexample then
        return current
      else
        let tail ← inspectSeeds depth rest
        return {
          stats := current.stats.add tail.stats
          counterexample := tail.counterexample
          newRegionCounterexample := tail.newRegionCounterexample
          waitCounterexample := tail.waitCounterexample
          forwardCounterexample := tail.forwardCounterexample }

def inspectDepths (seedsPerDepth : Nat) : List Nat →
    Except String SearchResult
  | [] => .ok {}
  | depth :: rest => do
      let current ← inspectSeeds depth (List.range seedsPerDepth)
      if current.hasCounterexample then
        return current
      else
        let tail ← inspectDepths seedsPerDepth rest
        return {
          stats := current.stats.add tail.stats
          counterexample := tail.counterexample
          newRegionCounterexample := tail.newRegionCounterexample
          waitCounterexample := tail.waitCounterexample
          forwardCounterexample := tail.forwardCounterexample }

def variantsPerCertificate : Nat := 6
def directCheckDepthCount : Nat := 3

structure AuditConfig where
  modeName : String
  depths : List Nat
  seedsPerDepth : Nat
  budgetMs : Nat
  requireGuardCoverage : Bool
  requireNewCoverage : Bool := false
  requireNewCreatedCoverage : Bool := false
  requireNewReachedCreatedCoverage : Bool := false
  requireNewPartnerCreatedCoverage : Bool := false
  requireNewOrderedPairCoverage : Bool := false
  requireWaitCoverage : Bool := false
  requireWaitCreatedCoverage : Bool := false
  requireWaitOrderedPairCoverage : Bool := false
  requireForwardCoverage : Bool := false
  requireForwardCreatedCoverage : Bool := false
  requireForwardOrderedPairCoverage : Bool := false
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

def waitSearchConfig : AuditConfig where
  modeName := "wait-search"
  depths := [5]
  seedsPerDepth := 16
  budgetMs := 1_800_000
  requireGuardCoverage := true
  requireNewCoverage := true
  requireNewCreatedCoverage := true
  requireNewReachedCreatedCoverage := true
  requireNewPartnerCreatedCoverage := true
  requireNewOrderedPairCoverage := true
  requireWaitCoverage := true
  requireWaitCreatedCoverage := true
  requireWaitOrderedPairCoverage := true
  requireForwardCoverage := true
  requireForwardCreatedCoverage := true
  requireForwardOrderedPairCoverage := true
  traceStarts := false

/-- Preferred name for the combined New/Wait/Forward cross-representative search.
`waitSearchConfig` remains the legacy-compatible spelling with identical bounds
and hard coverage gates. -/
def crossRepresentativeSearchConfig : AuditConfig :=
  { waitSearchConfig with modeName := "cross-representative-search" }

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

def renderWaitCounterexample
    (counterexample : WaitRegionCounterexample) : String :=
  s!"wait-region-counterexample depth={counterexample.depth} " ++
    s!"seed={counterexample.seed} variant={counterexample.variant} " ++
    s!"initialization_start={counterexample.initializationStart} " ++
    s!"step={counterexample.step} replay={repr counterexample.replayKinds}\n" ++
    s!"event={repr counterexample.event} " ++
    s!"event_representative={counterexample.eventRepresentative} " ++
    s!"boundary={counterexample.boundary} " ++
    s!"boundary_representative={counterexample.boundaryRepresentative} " ++
    s!"inserted_conclusion={counterexample.insertedConclusion} " ++
    s!"tensor_mate={counterexample.tensorMate}\n" ++
    s!"event_region={repr counterexample.eventRegion} " ++
    s!"candidate_region={repr counterexample.candidateRegion}\n" ++
    s!"certificate={repr counterexample.certificate}\n" ++
    s!"before={repr counterexample.before}\n" ++
    s!"after={repr counterexample.after}"

def renderForwardCounterexample
    (counterexample : ForwardRegionCounterexample) : String :=
  s!"forward-region-counterexample depth={counterexample.depth} " ++
    s!"seed={counterexample.seed} variant={counterexample.variant} " ++
    s!"initialization_start={counterexample.initializationStart} " ++
    s!"step={counterexample.step} replay={repr counterexample.replayKinds}\n" ++
    s!"event={repr counterexample.event} " ++
    s!"event_representative={counterexample.eventRepresentative} " ++
    s!"boundary={counterexample.boundary} " ++
    s!"boundary_representative={counterexample.boundaryRepresentative} " ++
    s!"inserted_conclusion={counterexample.insertedConclusion} " ++
    s!"tensor_mate={counterexample.tensorMate}\n" ++
    s!"event_region={repr counterexample.eventRegion} " ++
    s!"candidate_region={repr counterexample.candidateRegion}\n" ++
    s!"certificate={repr counterexample.certificate}\n" ++
    s!"before={repr counterexample.before}\n" ++
    s!"after={repr counterexample.after}"

def renderNewRegionCounterexample
    (counterexample : NewRegionCounterexample) : String :=
  s!"new-region-counterexample depth={counterexample.depth} " ++
    s!"seed={counterexample.seed} variant={counterexample.variant} " ++
    s!"initialization_start={counterexample.initializationStart} " ++
    s!"step={counterexample.step} replay={repr counterexample.replayKinds}\n" ++
    s!"event={repr counterexample.event} " ++
    s!"event_representative={counterexample.eventRepresentative} " ++
    s!"fresh_raw_age={counterexample.freshRawAge} " ++
    s!"fresh_representative={counterexample.freshRepresentative} " ++
    s!"created_at_reached={counterexample.createdAtReached} " ++
    s!"inserted_endpoint={counterexample.insertedEndpoint} " ++
    s!"tensor_mate={counterexample.tensorMate}\n" ++
    s!"event_region={repr counterexample.eventRegion} " ++
    s!"candidate_region={repr counterexample.candidateRegion}\n" ++
    s!"certificate={repr counterexample.certificate}\n" ++
    s!"before={repr counterexample.before}\n" ++
    s!"after={repr counterexample.after}"

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
    s!"new_steps={stats.newSteps} " ++
    s!"new_created_candidates={stats.newCreatedCandidates} " ++
    s!"new_created_reached_candidates=" ++
    s!"{stats.newCreatedReachedCandidates} " ++
    s!"new_created_partner_candidates=" ++
    s!"{stats.newCreatedPartnerCandidates} " ++
    s!"new_ordered_event_pairs={stats.newOrderedEventPairs} " ++
    s!"new_region_intersections={stats.newRegionIntersections} " ++
    s!"new_decode_failures={stats.newDecodeFailures} " ++
    s!"new_representative_failures={stats.newRepresentativeFailures} " ++
    s!"new_ledger_failures={stats.newLedgerFailures} " ++
    s!"new_region_computation_failures=" ++
    s!"{stats.newRegionComputationFailures} " ++
    s!"wait_steps={stats.waitSteps} " ++
    s!"wait_created_candidates={stats.waitCreatedCandidates} " ++
    s!"wait_ordered_event_pairs={stats.waitOrderedEventPairs} " ++
    s!"wait_region_intersections={stats.waitRegionIntersections} " ++
    s!"wait_decode_failures={stats.waitDecodeFailures} " ++
    s!"region_computation_failures={stats.regionComputationFailures} " ++
    s!"forward_steps={stats.forwardSteps} " ++
    s!"forward_created_candidates={stats.forwardCreatedCandidates} " ++
    s!"forward_ordered_event_pairs={stats.forwardOrderedEventPairs} " ++
    s!"forward_region_intersections={stats.forwardRegionIntersections} " ++
    s!"forward_decode_failures={stats.forwardDecodeFailures} " ++
    s!"forward_region_computation_failures=" ++
    s!"{stats.forwardRegionComputationFailures} " ++
    s!"ledger_decode_failures={stats.ledgerDecodeFailures} " ++
    s!"ledger_length_mismatches={stats.ledgerLengthMismatches} " ++
    s!"terminal_runs={stats.terminalRuns} " ++
    s!"max_replay_steps={stats.maxReplaySteps} " ++
    s!"cycles={stats.cycleRuns} truncations={stats.truncatedRuns} " ++
    s!"checksum={stats.checksum}"

def validateReplayStats (stats : AuditStats) : Except String Unit := do
  if stats.newCreatedCandidates !=
      stats.newCreatedReachedCandidates + stats.newCreatedPartnerCandidates then
    throw <|
      s!"New-created endpoint counts do not sum to the aggregate count: " ++
        s!"{stats.newCreatedCandidates} != {stats.newCreatedReachedCandidates} + " ++
        s!"{stats.newCreatedPartnerCandidates}"
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
  if stats.newRegionIntersections != 0 then
    throw <|
      s!"New-created source-region intersections observed: " ++
        s!"{stats.newRegionIntersections}"
  if stats.newDecodeFailures != 0 then
    throw <|
      s!"successful New transitions failed full audit replay: " ++
        s!"{stats.newDecodeFailures}"
  if stats.newRepresentativeFailures != 0 then
    throw <|
      s!"New representative transport checks failed: " ++
        s!"{stats.newRepresentativeFailures}"
  if stats.newLedgerFailures != 0 then
    throw s!"New ledger checks failed: {stats.newLedgerFailures}"
  if stats.newRegionComputationFailures != 0 then
    throw <|
      s!"New source-left region computations failed: " ++
        s!"{stats.newRegionComputationFailures}"
  if stats.waitRegionIntersections != 0 then
    throw s!"Wait-created source-region intersections observed: {stats.waitRegionIntersections}"
  if stats.waitDecodeFailures != 0 then
    throw s!"successful Wait transitions failed audit decoding: {stats.waitDecodeFailures}"
  if stats.regionComputationFailures != 0 then
    throw s!"Wait source-left region computations failed: {stats.regionComputationFailures}"
  if stats.forwardRegionIntersections != 0 then
    throw <|
      s!"Forward-created source-region intersections observed: " ++
        s!"{stats.forwardRegionIntersections}"
  if stats.forwardDecodeFailures != 0 then
    throw <|
      s!"successful Forward transitions failed audit decoding: " ++
        s!"{stats.forwardDecodeFailures}"
  if stats.forwardRegionComputationFailures != 0 then
    throw <|
      s!"Forward source-left region computations failed: " ++
        s!"{stats.forwardRegionComputationFailures}"
  if stats.ledgerDecodeFailures != 0 then
    throw s!"successful New transitions failed ledger decoding: {stats.ledgerDecodeFailures}"
  if stats.ledgerLengthMismatches != 0 then
    throw s!"audit ledger/raw-age horizon mismatches observed: {stats.ledgerLengthMismatches}"
  if stats.terminalRuns + stats.cycleRuns + stats.truncatedRuns !=
      stats.initializationSuccesses then
    throw "replay stop-reason counts do not partition successful initializations"

def requireValidStats (context : String) (stats : AuditStats) : IO Unit :=
  match validateReplayStats stats with
  | .ok () => pure ()
  | .error message => throw <| IO.userError s!"{context}: {message}"

def requireNoCounterexample (result : SearchResult) : IO Unit :=
  match result.counterexample with
  | some counterexample =>
      throw <| IO.userError (renderCounterexample counterexample)
  | none =>
      match result.newRegionCounterexample with
      | some counterexample =>
          throw <| IO.userError
            (renderNewRegionCounterexample counterexample)
      | none =>
          match result.waitCounterexample with
          | some counterexample =>
              throw <| IO.userError (renderWaitCounterexample counterexample)
          | none =>
              match result.forwardCounterexample with
              | none => pure ()
              | some counterexample =>
                  throw <| IO.userError
                    (renderForwardCounterexample counterexample)

def inspectStartsIO (candidate : CheckedCandidate)
    (regionCache : SourceRegionCache) : List Vertex →
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
          let tail ← inspectStartsIO candidate regionCache rest
          return tail.addStats { initializationAttempts := 1 }
      | some initial =>
          let initializationElapsed :=
            (← IO.monoMsNow) - initializationStarted
          let replayStarted ← IO.monoMsNow
          let reachable :=
            dispatcher_reachable_of_initializeReservation?_eq_some
              initializationEquation
          let replay :=
            inspectReachable candidate regionCache start initial reachable
              [{ rawAge := 0, start }] [] [] 0
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
          if current.hasCounterexample then
            return current
          else
            let tail ← inspectStartsIO candidate regionCache rest
            return {
              stats := current.stats.add tail.stats
              counterexample := tail.counterexample
              newRegionCounterexample := tail.newRegionCounterexample
              waitCounterexample := tail.waitCounterexample
              forwardCounterexample := tail.forwardCounterexample }

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
        let regionCache := sourceRegionCache candidate.certificate
        let replayStarted ← IO.monoMsNow
        let result ← if config.traceStarts then
          inspectStartsIO candidate regionCache
            (List.range variant.certificate.formulas.size)
        else
          pure <| inspectStarts candidate regionCache
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
  | ["--wait-search"] => .ok waitSearchConfig
  | ["--cross-representative-search"] => .ok crossRepresentativeSearchConfig
  | ["--depth", value] =>
      match value.toNat? with
      | some depth => .ok (depthConfig depth)
      | none => .error s!"invalid depth: {value}"
  | ["--profile-depth", value] =>
      match value.toNat? with
      | some depth => .ok (profileDepthConfig depth)
      | none => .error s!"invalid depth: {value}"
  | _ => .error <|
      "usage: proofnet_ir_new_progress_audit [--extended | --wait-search | " ++
        "--cross-representative-search | --depth N | --profile-depth N]"

/-- Run the bounded finite audit. Any New failure or New/Wait/Forward region
intersection is a hard regression and is printed with its complete certificate,
states, initialization start, dispatcher rule trace, and decoded witness data.
Passing these labelled, potentially duplicate cases proves no unconditional
progress or cross-representative preservation theorem. -/
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
  if config.requireNewCoverage && stats.newSteps == 0 then
    throw <| IO.userError "audit exercised no successful New transitions"
  if config.requireNewCreatedCoverage && stats.newCreatedCandidates == 0 then
    throw <| IO.userError "audit exercised no New-created future New candidates"
  if config.requireNewReachedCreatedCoverage &&
      stats.newCreatedReachedCandidates == 0 then
    throw <| IO.userError "audit exercised no reached-side New-created candidates"
  if config.requireNewPartnerCreatedCoverage &&
      stats.newCreatedPartnerCandidates == 0 then
    throw <| IO.userError "audit exercised no partner-side New-created candidates"
  if config.requireNewOrderedPairCoverage &&
      stats.newOrderedEventPairs == 0 then
    throw <| IO.userError "audit exercised no strictly ordered New/event pairs"
  if config.requireWaitCoverage && stats.waitSteps == 0 then
    throw <| IO.userError "audit exercised no successful Wait transitions"
  if config.requireWaitCreatedCoverage && stats.waitCreatedCandidates == 0 then
    throw <| IO.userError "audit exercised no Wait-created future New candidates"
  if config.requireWaitOrderedPairCoverage &&
      stats.waitOrderedEventPairs == 0 then
    throw <| IO.userError "audit exercised no strictly ordered Wait/event pairs"
  if config.requireForwardCoverage && stats.forwardSteps == 0 then
    throw <| IO.userError "audit exercised no successful Forward transitions"
  if config.requireForwardCreatedCoverage &&
      stats.forwardCreatedCandidates == 0 then
    throw <| IO.userError "audit exercised no Forward-created future New candidates"
  if config.requireForwardOrderedPairCoverage &&
      stats.forwardOrderedEventPairs == 0 then
    throw <| IO.userError "audit exercised no strictly ordered Forward/event pairs"
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
