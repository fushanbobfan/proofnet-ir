import ProofNetIR.Figure7.TailLaw
import ProofNetIR.Figure7.Sequential
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
C6--C8 and C11 at nop and wait, C12 at every reachable state (a par-premise
head whose mate is unmarked or older leaves a non-conclusion in the rest of the
active bucket), C13 (the same condition on every suffix of that bucket),
SHAPE and PAIRS at every reachable state (the bucket is connective
conclusions then atoms; each atom's axiom partner is in the atom run or
marked), I1--I6, the whole ready-stack shape, the seven conditions of the
order-free region-closure candidate CLOSURE (marked axiom endpoints and raw
bucket atoms keep their partner in the same region, the active class has no
tensor premise waiting for its mate, each class has at most one such premise,
fired tensors and same-class pars keep their conclusion in the region,
region conclusions have both premises marked there, and cross-class pars sit
in the waiting cell of the older class), and
C2 at every wait, and C3--C5 separately at both rules, before the popped head
receives its raw mark. C4 counts submitted pars with exactly one premise whose
raw mark resolves to the active component, including marks created at older
raw ages. First failures include the submitted occurrence numbering.

`--inductiveness-probe` uses one label decoration and all six ordering variants
of both shape families, with no deep random trees. At reachable states with at
most 32 vertices and at most four active entries, it permutes the active bucket
and takes zero or more bare pop/mark prefixes. These seeds carry a proof of
SchedulerInvariant but need not be reachable. Every seed is replayed to a stop;
the resulting snapshot list is checked closed under dispatch. Preservation is
measured per rule only when the candidate bundle holds before that rule, and
the implication CLOSURE to C12 is counted at every snapshot where CLOSURE
holds. Counts include repeated snapshots. Skipped reachable states are
reported.

The ten-minute limit is checked between complete histories. Exhausting replay
fuel or missing the requested coverage fails closed and never prints `-ok`.
The private obstruction regression is kernel checked; the aggregate measurements
have no Boolean-reflection, completeness, or unbounded preservation theorem.
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

private def bucketLabels : Array String :=
  #["I1 last-guarded-atom-has-unmarked-partner", "I2 pairs-with-at-most-one-singleton",
    "I3 prefix-marked-suffix-guard", "STACK every-bucket-shaped",
    "I4 legal-pop-prefix", "I5 adjacent-live-axiom-pairs",
    "I6 marked-premises-have-marked-or-queued-conclusion",
    "CLOSURE PAIRS-class", "CLOSURE T-top", "CLOSURE T-one", "CLOSURE T-fired",
    "CLOSURE P-fired", "CLOSURE D-down", "CLOSURE W-exact"]

private def mergeLabels : Array String :=
  #["payload-atoms", "previous-atoms", "active-atoms", "payload-connectives"]

private def bundleLabels : Array String :=
  #["BASE", "BASE+I4", "BASE+I5", "BASE+I4+I5+STACK", "BASE+I4+I5+STACK+I6",
    "CLOSURE", "CLOSURE+C12"]

private def atomAt (certificate : Certificate) (vertex : Vertex) : Bool :=
  match certificate.formulas[vertex]? with
  | some (.atom _ _) => true
  | _ => false

private def axiomPartner? (certificate : Certificate) (vertex : Vertex) : Option Vertex :=
  certificate.links.findSome? fun link ↦ match link with
    | .axiom left right =>
        if left == vertex then some right else if right == vertex then some left else none
    | _ => none

private def shaped (certificate : Certificate) (bucket : List Vertex) : Bool :=
  (bucket.dropWhile fun vertex ↦ !atomAt certificate vertex).all (atomAt certificate)

private def completePairs (certificate : Certificate) : List Vertex → Bool
  | [] => true
  | left :: right :: rest =>
      axiomPartner? certificate left == some right && completePairs certificate rest
  | [_] => false

-- Only concl/nop/wait may advance this lookahead. Forward and tensor consumers
-- end it: their created vertices, suspension, and merging change the order.
private def popPrefixSafe (certificate : Certificate) (state : ReservationState)
    (age : RawTokenAge) : List Vertex → List Vertex → Bool
  | _, [] => true
  | earlier, head :: rest =>
      if certificate.conclusions.contains head then
        popPrefixSafe certificate state age (head :: earlier) rest
      else match certificate.connectiveBelow? head with
        | none => true
        | some consumer =>
            let guarded := consumer.kind == .par && !earlier.contains consumer.mate &&
              (state.core.marks[consumer.mate]? == some none ||
                match state.core.marks[consumer.mate]? with
                | some (some mateAge) => mateAge < age
                | _ => false)
            !guarded || (hasNonconclusion certificate rest &&
              popPrefixSafe certificate state age (head :: earlier) rest)

private def adjacentLivePairs (certificate : Certificate) (state : ReservationState) :
    List Vertex → Bool
  | [] => true
  | head :: rest => match axiomPartner? certificate head with
    | none => false
    | some partner =>
        match state.core.marks[partner]? with
        | some (some _) => adjacentLivePairs certificate state rest
        | _ => match rest with
          | [] => false
          | next :: tail => partner == next && adjacentLivePairs certificate state tail

private def oneSingletonPairs (certificate : Certificate) (state : ReservationState) :
    List Vertex → Bool
  | [] => true
  | head :: rest => match axiomPartner? certificate head with
    | none => false
    | some partner => match state.core.marks[partner]? with
      | some (some _) => completePairs certificate rest
      | _ => match rest with
        | [] => false
        | next :: tail => partner == next && oneSingletonPairs certificate state tail

private def markedPremisesAccounted (certificate : Certificate) (state : ReservationState) : Bool :=
  let marked := fun vertex ↦ match state.core.marks[vertex]? with
    | some (some _) => true
    | _ => false
  certificate.links.all fun link ↦ match link with
    | .axiom _ _ => true
    | .par left right conclusion | .tensor left right conclusion =>
        !marked left || !marked right || marked conclusion ||
          state.stack.queuedVertices.contains conclusion

-- CLOSURE: an order-free candidate. Every vertex is placed in the class
-- (union-find representative of its mark) of the layer that consumed it;
-- the region of a class is its marked vertices plus the raw vertices of the
-- ready bucket at that class's sigma boundary. The conditions say that the
-- marked part of every region is closed under the link structure except at
-- par links whose other premise lies outside the region, and that the active
-- class carries no tensor premise still waiting for a `new`.
private def classOf (state : ReservationState) (vertex : Vertex) : Option RawTokenAge :=
  match state.core.marks[vertex]? with
  | some (some age) => some (state.core.representative age)
  | _ => none

private def bucketOfClass (state : ReservationState) (cls : RawTokenAge) : List Vertex :=
  ((state.stack.sigma.zip state.stack.ready).find? fun entry ↦
    state.core.representative entry.1 == cls).map (·.2) |>.getD []

private def inRegion (state : ReservationState) (cls : RawTokenAge) (vertex : Vertex) : Bool :=
  classOf state vertex == some cls || (bucketOfClass state cls).contains vertex

private def closureLabels : Array String :=
  #["PAIRS-class", "T-top", "T-one", "T-fired", "P-fired", "D-down", "W-exact"]

private def closureConditions (certificate : Certificate) (state : ReservationState) :
    Array Bool :=
  let marked := fun vertex ↦ (classOf state vertex).isSome
  let active := state.stack.sigma.getLast?
  let sameClass := fun (left right : Vertex) ↦
    match classOf state left, classOf state right with
    | some l, some r => l == r
    | _, _ => false
  let regionOfMarked := fun (premise target : Vertex) ↦
    match classOf state premise with
    | some cls => inRegion state cls target
    | none => true
  let pairs := certificate.links.all fun link ↦ match link with
    | .axiom left right => regionOfMarked left right && regionOfMarked right left
    | _ => true
  let tTop := certificate.links.all fun link ↦ match link with
    | .tensor left right _ =>
        (classOf state left != active || marked right) &&
          (classOf state right != active || marked left)
    | _ => true
  let pendingTensors := certificate.links.flatMap fun link ↦ match link with
    | .tensor left right _ =>
        (if marked left && !marked right then [classOf state left] else []) ++
          (if marked right && !marked left then [classOf state right] else [])
    | _ => []
  let tOne := pendingTensors.all fun cls ↦ pendingTensors.count cls ≤ 1
  let tFired := certificate.links.all fun link ↦ match link with
    | .tensor left right conclusion =>
        !(marked left && marked right) ||
          (sameClass left right && regionOfMarked left conclusion)
    | _ => true
  let pFired := certificate.links.all fun link ↦ match link with
    | .par left right conclusion =>
        !sameClass left right || regionOfMarked left conclusion
    | _ => true
  let dDown := certificate.links.all fun link ↦ match link with
    | .tensor left right conclusion | .par left right conclusion =>
        (match classOf state conclusion with
          | some cls => classOf state left == some cls && classOf state right == some cls
          | none => true) &&
        ((state.stack.sigma.zip state.stack.ready).all fun entry ↦
          !entry.2.contains conclusion ||
            (classOf state left == some (state.core.representative entry.1) &&
              classOf state right == some (state.core.representative entry.1)))
    | _ => true
  let waitingCell := fun (boundary : RawTokenAge) ↦ match state.stack.waiting[boundary]? with
    | some (.initialized vertices) => vertices
    | _ => []
  let wForward := certificate.links.all fun link ↦ match link with
    | .par left right conclusion =>
        match classOf state left, classOf state right with
        | some l, some r => l == r || (waitingCell (min l r)).contains conclusion
        | _, _ => true
    | _ => true
  let wBackward := state.stack.sigma.all fun boundary ↦ (waitingCell boundary).all fun vertex ↦
    certificate.links.any fun link ↦ match link with
      | .par left right conclusion => conclusion == vertex &&
          (match classOf state left, classOf state right with
            | some l, some r => l != r && min l r == state.core.representative boundary
            | _, _ => false)
      | _ => false
  #[pairs, tTop, tOne, tFired, pFired, dDown, wForward && wBackward]

private def closureHolds (certificate : Certificate) (state : ReservationState) : Bool :=
  (closureConditions certificate state).all id

-- I1 quantifies over atoms; "last" is with respect to non-conclusions in that
-- atom run. I2 permits one singleton anywhere, a relaxation of requiring that
-- it come from the current layer's original pair.
-- I3 virtually marks every earlier bucket entry at the active age. It makes
-- no assumption that those virtual pops are legal dispatcher transitions.
private def bucketCandidates (certificate : Certificate) (state : ReservationState) : Array Bool :=
  let bucket := state.stack.ready.getLast?.getD []
  let atoms := bucket.filter (atomAt certificate)
  let guarded := fun age vertex (earlier : List Vertex) ↦
    match certificate.connectiveBelow? vertex with
    | some consumer => consumer.kind == .par && !earlier.contains consumer.mate &&
        (state.core.marks[consumer.mate]? == some none ||
          match state.core.marks[consumer.mate]? with
          | some (some mateAge) => mateAge < age
          | _ => false)
    | none => false
  let i1 := match state.stack.sigma.getLast? with
    | none => true
    | some age => (List.range atoms.length).all fun index ↦
        let vertex := atoms[index]!
        !guarded age vertex ([] : List Vertex) ||
          hasNonconclusion certificate (atoms.drop (index + 1)) ||
          match axiomPartner? certificate vertex with
          | some partner => atoms.contains partner && state.core.marks[partner]? == some none
          | none => false
  let i2 := oneSingletonPairs certificate state atoms
  let i3 := match state.stack.sigma.getLast? with
    | none => true
    | some age => (List.range bucket.length).all fun index ↦
        !guarded age bucket[index]! (bucket.take index) ||
          hasNonconclusion certificate (bucket.drop (index + 1))
  let i4 := (state.stack.sigma.getLast?).all fun age ↦
    popPrefixSafe certificate state age [] bucket
  #[i1, i2, i3, state.stack.ready.all (shaped certificate),
    i4, adjacentLivePairs certificate state atoms, markedPremisesAccounted certificate state] ++
    closureConditions certificate state

private theorem mapReadyInvariant {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state) (f : List Vertex → List Vertex)
    (permutation : ∀ bucket, (f bucket).Perm bucket) :
    SchedulerInvariant certificate
      { state with stack := { state.stack with ready := state.stack.ready.map f } } := by
  have flattened : (state.stack.ready.map f).flatten.Perm state.stack.ready.flatten := by
    induction state.stack.ready with
    | nil => exact .nil
    | cons bucket rest ih =>
        simpa using (permutation bucket).append ih
  have queued := flattened.append_right state.stack.waitingVertices
  refine { invariant with
    stack_wellShaped := ?_
    stack_operationalWaitingDomain := ?_
    realizesSigma := ?_
    ready_bucket_frontier_exact := ?_
    queued_vertices_nodup := ?_
    queued_vertices_unmarked := ?_
    pending_premises_covered_except_ready := ?_ }
  · refine { invariant.stack_wellShaped with
      ready_aligned := by simpa using invariant.stack_wellShaped.ready_aligned
      ready_nodup := ?_
      ready_in_bounds := ?_ }
    · intro bucket member
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
      exact (permutation old).nodup_iff.mpr (invariant.stack_wellShaped.ready_nodup old oldMember)
    · intro bucket member vertex inside
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
      exact invariant.stack_wellShaped.ready_in_bounds old oldMember vertex
        ((permutation old).mem_iff.mp inside)
  · exact { invariant.stack_operationalWaitingDomain with }
  · exact { invariant.realizesSigma with }
  · intro position boundary bucket sigmaLookup readyLookup
    change (state.stack.ready.map f)[position]? = some bucket at readyLookup
    rw [List.getElem?_map] at readyLookup
    cases oldEq : state.stack.ready[position]? with
    | none => simp [oldEq] at readyLookup
    | some old =>
        have same : f old = bucket := by simpa [oldEq] using readyLookup
        subst bucket
        obtain ⟨component, lookup, membership⟩ :=
          invariant.ready_bucket_frontier_exact sigmaLookup oldEq
        exact ⟨component, lookup, fun vertex ↦ (permutation old).mem_iff.trans (membership vertex)⟩
  · exact queued.nodup_iff.mpr invariant.queued_vertices_nodup
  · intro vertex member
    exact invariant.queued_vertices_unmarked vertex (queued.mem_iff.mp member)
  · intro link member
    have old := invariant.pending_premises_covered_except_ready member
    cases link with
    | «axiom» _ _ => trivial
    | par left right conclusion | tensor left right conclusion =>
        intro raw absent
        exact old raw fun member ↦ absent (flattened.mem_iff.mpr member)

private def invariantBundles (certificate : Certificate) (state : ReservationState) : Array Bool :=
  let bucket := state.stack.ready.getLast?.getD []
  let atoms := bucket.filter (atomAt certificate)
  let pairs := atoms.all fun vertex ↦ match axiomPartner? certificate vertex with
    | none => false
    | some partner => atoms.contains partner || match state.core.marks[partner]? with
      | some (some _) => true
      | _ => false
  let c12 := match state.stack.sigma.getLast?, bucket with
    | some age, head :: rest => match certificate.connectiveBelow? head with
      | none => true
      | some consumer =>
          let guarded := consumer.kind == .par &&
            (state.core.marks[consumer.mate]? == some none ||
              match state.core.marks[consumer.mate]? with
              | some (some mateAge) => mateAge < age
              | _ => false)
          !guarded || hasNonconclusion certificate rest
    | _, _ => true
  let base := shaped certificate bucket && pairs && c12
  let candidates := bucketCandidates certificate state
  let combined := base && candidates[4]! && candidates[5]! && candidates[3]!
  let closure := closureHolds certificate state
  #[base, base && candidates[4]!, base && candidates[5]!, combined,
    combined && candidates[6]!, closure, closure && c12]

private structure Snapshot (certificate : Certificate) where
  state : ReservationState
  invariant : SchedulerInvariant certificate state

private def traceSnapshots (certificate : Certificate) :
    Nat → Snapshot certificate → IO (List (Snapshot certificate))
  | fuel, snapshot => do
      match equation : dispatch? certificate snapshot.state snapshot.invariant with
      | none => return [snapshot]
      | some result => match fuel with
        | 0 => throw (IO.userError "inductiveness-probe-INCOMPLETE snapshot fuel")
        | fuel + 1 =>
            let rest ← traceSnapshots certificate fuel
              ⟨result.after, dispatch?_schedulerInvariant snapshot.invariant equation⟩
            return snapshot :: rest

private def preparedSnapshots (certificate : Certificate) :
    Nat → Snapshot certificate → List (Snapshot certificate)
  | 0, snapshot => [snapshot]
  | fuel + 1, snapshot => snapshot ::
      match prepare? snapshot.state with
      | none => []
      | some prepared => preparedSnapshots certificate fuel
          ⟨prepared.after, prepared.schedulerInvariant snapshot.invariant⟩

private def insertEverywhere (vertex : Vertex) : List Vertex → List (List Vertex)
  | [] => [[vertex]]
  | head :: rest => (vertex :: head :: rest) ::
      (insertEverywhere vertex rest).map (head :: ·)

private def permutations : List Vertex → List (List Vertex)
  | [] => [[]]
  | head :: rest => (permutations rest).flatMap (insertEverywhere head)

namespace BucketObstruction

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private def certificate : Certificate where
  formulas := #[.atom "p4" true, .atom "p4" false, .atom "p5" false, .atom "p5" true,
    .tensor (.atom "p4" true) (.atom "p5" false),
    .par (.tensor (.atom "p4" true) (.atom "p5" false)) (.atom "p4" false),
    .atom "p4" false, .atom "p4" true,
    .tensor (.atom "p5" true) (.atom "p4" false),
    .par (.tensor (.atom "p5" true) (.atom "p4" false))
      (.par (.tensor (.atom "p4" true) (.atom "p5" false)) (.atom "p4" false))]
  links := [.axiom 0 1, .axiom 2 3, .tensor 0 2 4, .par 4 1 5,
    .axiom 6 7, .tensor 3 6 8, .par 8 5 9]
  conclusions := [7, 9]

private theorem correct : certificate.DeclarativelyCorrect :=
  certificate.check_iff_declarativelyCorrect.mp (by decide +kernel)

private def initial : Snapshot certificate :=
  let state := (initializeReservation? certificate 0).getD (ReservationState.empty certificate)
  have equation : initializeReservation? certificate 0 = some state := by decide +kernel
  ⟨state, initializeReservation?_schedulerInvariant correct.1 equation⟩

private def advance (snapshot : Snapshot certificate) : Snapshot certificate :=
  match equation : dispatch? certificate snapshot.state snapshot.invariant with
  | none => snapshot
  | some result => ⟨result.after, dispatch?_schedulerInvariant snapshot.invariant equation⟩

private def reordered : Snapshot certificate :=
  let first := advance initial
  ⟨{ first.state with stack := { first.state.stack with ready := first.state.stack.ready.map List.reverse } },
    mapReadyInvariant first.invariant List.reverse (fun _ ↦ List.reverse_perm _)⟩

private def skipped : Snapshot certificate :=
  let prepared := (prepare? reordered.state).get (by decide +kernel)
  ⟨prepared.after, prepared.schedulerInvariant reordered.invariant⟩

private def before := advance (advance skipped)
private def result := (dispatch? certificate before.state before.invariant).getD ⟨.concl, before.state⟩

-- Kernel regression for the strongest tested bundle: a skipped tensor search
-- can satisfy every current candidate, then fail C12 at a canonical forward.
private theorem forward_obstruction :
    certificate.DeclarativelyCorrect ∧
    invariantBundles certificate before.state = #[true, true, true, true, true, false, false] ∧
    before.state.stack.ready = [[1]] ∧
    dispatch? certificate before.state before.invariant = some result ∧
    result.kind = .forward ∧ result.after.stack.ready = [[5]] ∧
    invariantBundles certificate result.after =
      #[false, false, false, false, false, false, false] ∧
    ¬ ParHeadGuardTailNonconclusion certificate result.after := by
  refine ⟨correct, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro law
  let consumer := (certificate.connectiveBelow? 5).get (by decide +kernel)
  have tail := law (age := 0) (head := 5) (rest := []) consumer
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Or.inl (by decide +kernel))
  simp at tail

end BucketObstruction

private def probeLabels : Array String :=
  #["C1 rule=nop", "C2 rule=wait", "C3 rule=nop", "C3 rule=wait",
    "C4 rule=nop", "C4 rule=wait", "C5 rule=nop", "C5 rule=wait",
    "C6 rule=nop", "C6 rule=wait", "C7 rule=nop", "C7 rule=wait",
    "C8raw2 rule=nop", "C8raw2 rule=wait", "C8nomark rule=nop", "C8nomark rule=wait",
    "C11noConclInTail rule=nop", "C11noConclInTail rule=wait"]

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
  probes : Array ProbeCount := Array.replicate 18 {}
  singletonStates : Nat := 0
  shapeFails : Nat := 0
  pairFails : Nat := 0
  singletonParFails : Nat := 0
  suffixParFails : Nat := 0
  bucketProbes : Array ProbeCount := Array.replicate bucketLabels.size {}
  mergeProbes : Array ProbeCount := Array.replicate mergeLabels.size {}
  inductivenessProbe : Bool := false
  preservation : Array ProbeCount := Array.replicate (bundleLabels.size * 6) {}
  snapshotSeeds : Nat := 0
  snapshotStates : Nat := 0
  snapshotEdges : Nat := 0
  snapshotSkipped : Nat := 0
  closureStates : Nat := 0
  closureC12Fails : Nat := 0
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

-- The seeds need not be reachable. Bucket permutations carry a Lean proof of
-- SchedulerInvariant, and every successor uses its existing preservation proof.
-- Each finite trace is checked closed under dispatch before testing antecedents.
private def observePreservation (certificate : Certificate) (state : ReservationState)
    (invariant : SchedulerInvariant certificate state) (context : String) (start step : Nat)
    (stats : Stats) : IO Stats := do
  if !stats.inductivenessProbe then return stats
  let bucket := state.stack.ready.getLast?.getD []
  if bucket.length > 4 || certificate.formulas.size > 32 then
    return { stats with snapshotSkipped := stats.snapshotSkipped + 1 }
  let mut stats := stats
  for replacement in permutations bucket do
    let f := fun old ↦ if replacement.Perm old then replacement else old
    have perm : ∀ old, (f old).Perm old := by
      intro old
      dsimp [f]
      split
      · assumption
      · exact .refl _
    let seed : Snapshot certificate :=
      ⟨{ state with stack := { state.stack with ready := state.stack.ready.map f } },
        mapReadyInvariant invariant f perm⟩
    for (preparedSeed, pops) in (preparedSnapshots certificate bucket.length seed).zipIdx do
      let snapshots ← traceSnapshots certificate (2 * certificate.formulas.size + 1) preparedSeed
      let states := snapshots.map Snapshot.state
      stats := { stats with
        snapshotSeeds := stats.snapshotSeeds + 1
        snapshotStates := stats.snapshotStates + snapshots.length }
      for (snapshot, offset) in snapshots.zipIdx do
        match dispatch? certificate snapshot.state snapshot.invariant with
        | none => pure ()
        | some result =>
            unless states.contains result.after do
              throw (IO.userError "inductiveness-probe-ERROR snapshot set is not closed")
            stats := { stats with snapshotEdges := stats.snapshotEdges + 1 }
            let before := invariantBundles certificate snapshot.state
            let after := invariantBundles certificate result.after
            if before[5]! then
              stats := { stats with closureStates := stats.closureStates + 1 }
              if !before[6]! then
                if stats.closureC12Fails == 0 then
                  IO.println "inductiveness-probe-first-failure CLOSURE-implies-C12"
                  IO.println s!"submitted={submittedJson certificate |>.compress}"
                  IO.println (s!"{context} start={start} step={step} replacement={repr replacement} " ++
                    s!"pops={pops} offset={offset} sigma={repr snapshot.state.stack.sigma} " ++
                    s!"ready={repr snapshot.state.stack.ready} marks={repr snapshot.state.core.marks}")
                stats := { stats with closureC12Fails := stats.closureC12Fails + 1 }
            for bundle in List.range bundleLabels.size do
              if before[bundle]! then
                let index := bundle * 6 + kindIndex result.kind
                let prior := stats.preservation[index]!
                let holds := after[bundle]!
                if !holds && prior.fails == 0 then
                  IO.println (s!"inductiveness-probe-first-failure {bundleLabels[bundle]!} " ++
                    s!"rule={repr result.kind}")
                  IO.println s!"submitted={submittedJson certificate |>.compress}"
                  IO.println (s!"{context} start={start} step={step} replacement={repr replacement} " ++
                    s!"pops={pops} offset={offset} sigma={repr snapshot.state.stack.sigma}")
                  IO.println (s!"before_ready={repr snapshot.state.stack.ready} " ++
                    s!"before_marks={repr snapshot.state.core.marks} " ++
                    s!"before_waiting={repr snapshot.state.stack.waiting}")
                  IO.println (s!"after_ready={repr result.after.stack.ready} " ++
                    s!"after_marks={repr result.after.core.marks} " ++
                    s!"before_bundles={repr before} after_bundles={repr after}")
                let next := if holds then { prior with holds := prior.holds + 1 }
                  else { prior with fails := prior.fails + 1 }
                stats := { stats with preservation := stats.preservation.set! index next }
  return stats

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
  let bucket := prepared.stackResult.remainingTop
  let mateInBucket := bucket.contains consumer.mate
  let olderMarked := fun vertex ↦ match state.core.marks[vertex]? with
    | some (some rawAge) => rawAge < age
    | _ => false
  let bucketParsCovered := bucket.all fun vertex ↦
    match certificate.connectiveBelow? vertex with
    | some other => other.kind != .par || bucket.contains other.mate || olderMarked other.mate
    | none => true
  -- C8: the active frontier is a derivation's conclusion list; count how many of
  -- its vertices are raw versus marked, and whether the tree is a bare axiom.
  let rawCount := component.frontier.countP unmarked
  let markedCount := component.frontier.length - rawCount
  let treeIsAxiom := match component.tree with | .axiom _ _ => true | _ => false
  let observations := [(offset, localCandidate), (2 + offset, !debt || payers.length ≥ 2),
    (4 + offset, payers.length ≥ singleMarkedPars), (6 + offset, p),
    (8 + offset, mateInBucket), (10 + offset, bucketParsCovered && p),
    (12 + offset, rawCount ≥ 2), (14 + offset, markedCount == 0),
    (16 + offset, !bucket.any fun vertex ↦ certificate.conclusions.contains vertex)]
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
        s!"single_marked_pars={singleMarkedPars} raw={rawCount} marked={markedCount} " ++
        s!"tree_is_axiom={treeIsAxiom} sigma={repr state.stack.sigma} ready={repr state.stack.ready}")
    let next := if holds then { prior with holds := prior.holds + 1 }
      else { prior with fails := prior.fails + 1 }
    stats := { stats with probes := stats.probes.set! index next }
  return stats

private def observeMerge (certificate : Certificate) (state : ReservationState)
    (context : String) (start step : Nat) (result : Figure7DispatchResult)
    (stats : Stats) : IO Stats := do
  if !stats.invariantProbe || result.kind != .unifyPayload then return stats
  let some prepared := prepare? state
    | throw (IO.userError "invariant-probe-ERROR missing merge prefix")
  let stack := prepared.stackResult.after
  let some previous := stack.ready.dropLast.getLast?
    | throw (IO.userError "invariant-probe-ERROR missing previous bucket")
  let some active := stack.ready.getLast?
    | throw (IO.userError "invariant-probe-ERROR missing active bucket")
  let some boundary := stack.sigma.dropLast.getLast?
    | throw (IO.userError "invariant-probe-ERROR missing previous boundary")
  let some (.initialized payload) := stack.waiting[boundary]?
    | throw (IO.userError "invariant-probe-ERROR missing waiting payload")
  let observations := #[payload.all (atomAt certificate), previous.all (atomAt certificate),
    active.all (atomAt certificate), payload.all fun vertex ↦ !atomAt certificate vertex]
  let mut stats := stats
  for index in List.range observations.size do
    let prior := stats.mergeProbes[index]!
    let holds := observations[index]!
    if !holds && prior.fails == 0 then
      IO.println s!"invariant-probe-first-failure MERGE {mergeLabels[index]!}"
      IO.println s!"submitted={submittedJson certificate |>.compress}"
      IO.println (s!"{context} start={start} step={step} payload={repr payload} " ++
        s!"previous={repr previous} active={repr active}")
    let next := if holds then { prior with holds := prior.holds + 1 }
      else { prior with fails := prior.fails + 1 }
    stats := { stats with mergeProbes := stats.mergeProbes.set! index next }
  return stats

private def observeBucketCandidates (certificate : Certificate) (state : ReservationState)
    (context : String) (start step : Nat) (stats : Stats) : IO Stats := do
  if !stats.invariantProbe then
    return stats
  let observations := bucketCandidates certificate state
  let mut stats := stats
  for index in List.range observations.size do
    let prior := stats.bucketProbes[index]!
    let holds := observations[index]!
    if !holds && prior.fails == 0 then
      IO.println s!"invariant-probe-first-failure {bucketLabels[index]!}"
      IO.println s!"submitted={submittedJson certificate |>.compress}"
      IO.println (s!"{context} start={start} step={step} sigma={repr state.stack.sigma} " ++
        s!"ready={repr state.stack.ready} marks={repr state.core.marks}")
    let next := if holds then { prior with holds := prior.holds + 1 }
      else { prior with fails := prior.fails + 1 }
    stats := { stats with bucketProbes := stats.bucketProbes.set! index next }
  return stats

private def observeSingletonBucket (certificate : Certificate) (state : ReservationState)
    (context : String) (start step : Nat) (stats : Stats) : IO Stats := do
  if !stats.invariantProbe then return stats
  let stats ← observeBucketCandidates certificate state context start step stats
  -- C12, at every reachable state: if the active bucket's head is a par
  -- premise whose mate is not marked at or above the active age (the nop or
  -- wait guard), then the rest of the bucket contains a non-conclusion.
  let holds := match state.stack.sigma.getLast?, state.stack.ready.getLast? with
    | some age, some (head :: rest) =>
        match certificate.connectiveBelow? head with
        | some consumer =>
            consumer.kind != .par ||
              (match state.core.marks[consumer.mate]? with
                | some (some mateAge) => mateAge ≥ age
                | _ => false) ||
              rest.any fun vertex ↦ !certificate.conclusions.contains vertex
        | none => true
    | _, _ => true
  -- C13 is the proposed suffix strengthening for pop preservation of C12.
  let suffixHolds := match state.stack.sigma.getLast?, state.stack.ready.getLast? with
    | some age, some bucket => (List.range bucket.length).all fun index ↦
        match bucket.drop index with
        | [] => true
        | head :: rest =>
            match certificate.connectiveBelow? head with
            | some consumer =>
                consumer.kind != .par ||
                  (match state.core.marks[consumer.mate]? with
                    | some (some mateAge) => mateAge ≥ age
                    | _ => false) || hasNonconclusion certificate rest
            | none => true
    | _, _ => true
  if !suffixHolds && stats.suffixParFails == 0 then
    IO.println "invariant-probe-first-failure C13 par-suffix-guard-tail-nonconclusion"
    IO.println s!"submitted={submittedJson certificate |>.compress}"
    IO.println (s!"{context} start={start} step={step} sigma={repr state.stack.sigma} " ++
      s!"ready={repr state.stack.ready} marks={repr state.core.marks}")
  if !holds && stats.singletonParFails == 0 then
    IO.println "invariant-probe-first-failure C12 par-head-guard-tail-nonconclusion"
    IO.println s!"certificate={certificate.canonicalString}"
    IO.println (s!"{context} start={start} step={step} sigma={repr state.stack.sigma} " ++
      s!"ready={repr state.stack.ready}")
  -- Shape probe: the active bucket read as roles (P = produced by a par link,
  -- T = produced by a tensor link, A = atom) must match P* then at most two A.
  let role := fun vertex ↦ match certificate.formulas[vertex]? with
    | some (.par _ _) => 'P'
    | some (.tensor _ _) => 'T'
    | _ => 'A'
  let shapeOk := match state.stack.ready.getLast? with
    | some bucket =>
        let roles := bucket.map role
        let connectives := roles.takeWhile (· != 'A')
        let restRoles := roles.drop connectives.length
        restRoles.all (· == 'A')
    | none => true
  let axiomPartner := fun vertex ↦ certificate.links.findSome? fun link ↦ match link with
    | .axiom l r => if l == vertex then some r else if r == vertex then some l else none
    | _ => none
  let atomSegment := match state.stack.ready.getLast? with
    | some bucket => bucket.filter fun v ↦ role v == 'A'
    | none => []
  let pairsOk : Bool := atomSegment.all fun v ↦ match axiomPartner v with
    | some w => atomSegment.contains w || (match state.core.marks[w]? with | some (some _) => true | _ => false)
    | none => true
  if !pairsOk && stats.pairFails == 0 then
    IO.println "invariant-probe-first-failure PAIRS atom-partner-not-in-segment-nor-marked"
    IO.println (s!"{context} start={start} step={step} sigma={repr state.stack.sigma} " ++
      s!"ready={repr state.stack.ready} marks={repr (atomSegment.map fun v ↦ (v, axiomPartner v, state.core.marks[v]?))}")
  let stats := { stats with pairFails := stats.pairFails + (if pairsOk then 0 else 1) }
  if !shapeOk && stats.shapeFails == 0 then
    IO.println "invariant-probe-first-failure SHAPE bucket-not-(P|T)*A*"
    IO.println (s!"{context} start={start} step={step} sigma={repr state.stack.sigma} " ++
      s!"ready={repr state.stack.ready} roles={repr ((state.stack.ready.getLast?.getD []).map role)}")
  return { stats with
    shapeFails := stats.shapeFails + (if shapeOk then 0 else 1)
    singletonStates := stats.singletonStates + 1
    singletonParFails := stats.singletonParFails + (if holds then 0 else 1)
    suffixParFails := stats.suffixParFails + (if suffixHolds then 0 else 1) }

private def printProbe (setName : String) (stats : Stats) : IO Unit := do
  if stats.inductivenessProbe then
    IO.println (s!"inductiveness-probe set={setName} closed-traces={stats.snapshotSeeds} " ++
      s!"states={stats.snapshotStates} edges={stats.snapshotEdges} " ++
      s!"skipped-reachable-states={stats.snapshotSkipped} bucket-cap=4 vertex-cap=32")
    for bundle in List.range bundleLabels.size do
      for kind in [.concl, .nop, .new, .wait, .forward, .unifyPayload] do
        let count := stats.preservation[bundle * 6 + kindIndex kind]!
        IO.println (s!"inductiveness-probe set={setName} {bundleLabels[bundle]!} " ++
          s!"rule={repr kind} holds={count.holds} fails={count.fails}")
    IO.println (s!"inductiveness-probe set={setName} CLOSURE-implies-C12 " ++
      s!"closure-states={stats.closureStates} c12-fails={stats.closureC12Fails}")
  if stats.invariantProbe then
    for index in List.range probeLabels.size do
      let count := stats.probes[index]!
      let steps := stats.kinds[if index % 2 == 0 then 1 else 3]!
      unless count.holds + count.fails == steps do
        throw (IO.userError s!"invariant-probe-ERROR incomplete counts {probeLabels[index]!}")
      IO.println (s!"invariant-probe set={setName} {probeLabels[index]!} " ++
        s!"holds={count.holds} fails={count.fails}")
    IO.println s!"invariant-probe set={setName} SHAPE bucket-PT*A* states={stats.singletonStates} fails={stats.shapeFails}"
    IO.println s!"invariant-probe set={setName} PAIRS atom-partner-in-segment-or-marked states={stats.singletonStates} fails={stats.pairFails}"
    IO.println (s!"invariant-probe set={setName} C12 par-head-guard-tail-nonconclusion states={stats.singletonStates} " ++
      s!"fails={stats.singletonParFails}")
    IO.println (s!"invariant-probe set={setName} C13 par-suffix-guard-tail-nonconclusion " ++
      s!"states={stats.singletonStates} fails={stats.suffixParFails}")
    for index in List.range bucketLabels.size do
      let count := stats.bucketProbes[index]!
      unless count.holds + count.fails == stats.singletonStates do
        throw (IO.userError "invariant-probe-ERROR incomplete bucket counts")
      IO.println (s!"invariant-probe set={setName} {bucketLabels[index]!} " ++
        s!"states={stats.singletonStates} fails={count.fails}")
    for index in List.range mergeLabels.size do
      let count := stats.mergeProbes[index]!
      unless count.holds + count.fails == stats.kinds[5]! do
        throw (IO.userError "invariant-probe-ERROR incomplete merge counts")
      IO.println (s!"invariant-probe set={setName} MERGE {mergeLabels[index]!} " ++
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
      let stats ← observeSingletonBucket certificate state context start step stats
      let invariant := reachable.schedulerInvariant correct.1
      let stats ← observePreservation certificate state invariant context start step stats
      match equation : dispatch? certificate state invariant with
      | none => return { stats with stops := stats.stops + 1 }
      | some result =>
          match fuel with
          | 0 => throw (IO.userError s!"tail-law-search-INCOMPLETE replay fuel {context}")
          | fuel + 1 =>
              let stats ← observeInvariants certificate state context start step result stats
              let stats ← observeMerge certificate state context start step result stats
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

private def run (smoke : Bool) (invariantProbe : Bool := false)
    (inductivenessProbe : Bool := false) : IO Unit := do
  let started ← IO.monoMsNow
  let deadline := started + 600000
  let statsRef ← IO.mkRef ({ invariantProbe, inductivenessProbe } : Stats)
  let randomSeeds := if smoke || inductivenessProbe then 0 else 4
  let labelVariants := if smoke || inductivenessProbe then 1 else 8
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
  let minimumCases := if inductivenessProbe then 2000 else 20000
  unless smoke || (stats.cases ≥ minimumCases && completed ≥ 5 && stats.stops == stats.histories) do
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

private def runWaitFocus (invariantProbe : Bool := false)
    (inductivenessProbe : Bool := false) : IO Unit := do
  let started ← IO.monoMsNow
  let deadline := started + 600000
  let statsRef ← IO.mkRef ({ invariantProbe, inductivenessProbe } : Stats)
  let baseTrees := 24
  let labelVariants := if inductivenessProbe then 1 else 8
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
  let minimumWaitCertificates := if inductivenessProbe then 60 else 500
  let minimumWaitSteps := if inductivenessProbe then 625 else 5000
  IO.println s!"tail-law-wait-focus-coverage {waitFocusSummary stats baseTrees
    labelVariants orderVariants startCeiling elapsed}"
  unless stats.cases == baseTrees * labelVariants * orderVariants &&
      stats.skippedStarts == 0 && stats.stops == stats.histories &&
      stats.waitCertificates ≥ minimumWaitCertificates &&
      stats.kinds[3]! ≥ minimumWaitSteps && elapsed ≤ 600000 do
    throw (IO.userError
      (s!"tail-law-search-INCOMPLETE wait coverage " ++
        s!"wait_certificates={stats.waitCertificates}/{minimumWaitCertificates} " ++
        s!"wait_steps={stats.kinds[3]!}/{minimumWaitSteps} wait_pairs={stats.waitPairs}; " ++
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
  | ["--inductiveness-probe"] =>
      ProofNetIRTailLawSearch.run false false true
      ProofNetIRTailLawSearch.runWaitFocus false true
  | ["--inductiveness-probe", "--smoke"] => ProofNetIRTailLawSearch.run true false true
  | ["--inductiveness-probe", "--wait-focus"] => ProofNetIRTailLawSearch.runWaitFocus false true
  | _ => throw (IO.userError
      ("usage: proofnet_ir_tail_law_search [--invariant-probe | --inductiveness-probe] " ++
        "[--smoke | --wait-focus]"))
