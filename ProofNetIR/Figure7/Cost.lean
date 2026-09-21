import ProofNetIR.Figure7.Sequential

/-!
# Operation counters of the public decision

`Certificate.sequentialDecisionWithStats` runs the public decision
`Certificate.unificationCheck` and records, for every phase, the operations
it performs. The counters are explicit cost models of the implementation,
derived from the executable definitions; every term below names the
traversal it charges. Conventions:

- a list traversal (`getLast?`, `dropLast`, `++`, `flatten`, `flatMap`,
  `all`, `any`, `filter`, `filterMap`, `mapM`, `contains`, `idxOf`, `pick?`)
  is charged the length of the list it traverses;
- a duplicate scan (`eraseDups`, the decidable `Nodup` guard) is charged the
  square of its list length;
- an array read or write and a constant-work primitive are charged one;
- the consumer and source indices, rebuilt on every use, are charged
  `formulas.size + links.length`; a bucket scan of an index is charged
  `links.length`;
- a bounded search is charged its fuel plus one, and a representative walk
  is charged the parent-array size;
- a scan that may stop early and a rule attempt that may fail early are
  charged as if they ran to the end, so every counter is an upper bound of
  the operations actually performed by that phase.
-/

namespace ProofNetIR

open SequentialSchedulerBridge SequentialSchedulerState SequentialFigure7

namespace SequentialCost

/-- Counters of one run of the public decision, one per phase. -/
structure SequentialDecisionStats where
  /-- `Certificate.wellFormed`. -/
  structural : Nat
  /-- `initializeReservation?` at the first conclusion. -/
  initialization : Nat
  /-- Number of `dispatch?` calls made by `runDispatcher`. -/
  dispatchCalls : Nat
  /-- Operations of those calls, by the rule attempts each one made. -/
  dispatch : Nat
  /-- `sequentialFinalTree?`. -/
  extraction : Nat
  /-- `verifyDerivation?`. -/
  verification : Nat
  deriving Repr, DecidableEq

namespace SequentialDecisionStats

/-- All operations of the run. -/
def total (stats : SequentialDecisionStats) : Nat :=
  stats.structural + stats.initialization + stats.dispatchCalls + stats.dispatch +
    stats.extraction + stats.verification

/-- Counters of a run that stopped before the dispatcher. -/
def early (structural initialization : Nat) : SequentialDecisionStats :=
  ⟨structural, initialization, 0, 0, 0, 0⟩

end SequentialDecisionStats

/-- `Certificate.wellFormed`: the size and length tests, the in-bounds scan
of the conclusions, the duplicate scan of the conclusions, one local check
per link, and one node check per occurrence (`nodeWellFormed`: one link
filter for the source count, one `contains` over the conclusions, and one
link filter for the parent-use count). -/
def structuralCost (certificate : Certificate) : Nat :=
  let n := certificate.formulas.size
  let m := certificate.links.length
  let k := certificate.conclusions.length
  2 + k + k * k + m + n * (2 * m + k + 1)

/-- `ConsumerIndex.build` and `sourceIndex`: the carrier-sized table and one
fold step per link. -/
def indexCost (certificate : Certificate) : Nat :=
  certificate.formulas.size + certificate.links.length

/-- `uniqueConsumer?` on a freshly built consumer index: the build and the
scan of one bucket, which holds at most one entry per link. -/
def uniqueConsumerCost (certificate : Certificate) : Nat :=
  indexCost certificate + certificate.links.length

/-- `connectiveBelow?` and `tensorBelow?`: the unique-consumer lookup and the
constant link inspection. -/
def consumerLookupCost (certificate : Certificate) : Nat :=
  uniqueConsumerCost certificate + 1

/-- `nodeWellFormed` at one occurrence. -/
def nodeCheckCost (certificate : Certificate) : Nat :=
  2 * certificate.links.length + certificate.conclusions.length + 1

/-- `conclusionBelow?`: conclusion membership, the node check, and the
consumer-index bucket test. -/
def conclusionLookupCost (certificate : Certificate) : Nat :=
  certificate.conclusions.length + nodeCheckCost certificate + indexCost certificate + 1

/-- Occurrences currently queued in the ready buckets and waiting cells. -/
def queued (state : ReservationState) : Nat :=
  state.stack.queuedVertices.length

/-- `prepare?`: the ready and sigma tail reads, the mark test and write, the
ready tail rewrite, and the core mark. -/
def prepareCost (state : ReservationState) : Nat :=
  2 * state.stack.ready.length + state.stack.sigma.length + 3

/-- `queuePar?`: the token guard (two representative walks), the component
read, two frontier picks, the frontier append, and the component write. -/
def queueParCost (certificate : Certificate) (state : ReservationState) : Nat :=
  2 * state.core.parents.size + 3 * certificate.formulas.size + 3

/-- `queueTensor?`: the token guard (two representative walks), two component
reads, two frontier picks, the frontier append, and three writes. -/
def queueTensorCost (certificate : Certificate) (state : ReservationState) : Nat :=
  2 * state.core.parents.size + 3 * certificate.formulas.size + 5

/-- Length of the waiting payload merged by `unifyPayload?`: the cell at the
boundary below the active one. -/
def mergedPayloadLength (state : ReservationState) : Nat :=
  match state.stack.sigma.dropLast.getLast? with
  | none => 0
  | some boundary =>
      match state.stack.waiting[boundary]? with
      | some (.initialized payload) => payload.length
      | _ => 0

/-- `concl?`: the prepared prefix and the conclusion lookup. -/
def conclCost (certificate : Certificate) (state : ReservationState) : Nat :=
  prepareCost state + conclusionLookupCost certificate

/-- `nop?`: the prepared prefix, the consumer lookup, and the mate mark test. -/
def nopCost (certificate : Certificate) (state : ReservationState) : Nat :=
  prepareCost state + consumerLookupCost certificate + 1

/-- `new?`: the prepared prefix, the tensor lookup, the source index, the
carrier-fuelled `NEXTAXIOM` search, the trace tail read, the operational
`new` guard (sigma tail, two queued-occurrence scans, four lookups) and
update (sigma and ready appends, one cell write), and the axiom
reservation. -/
def newCost (certificate : Certificate) (state : ReservationState) : Nat :=
  let n := certificate.formulas.size
  prepareCost state + consumerLookupCost certificate + indexCost certificate + (n + 1) +
    (n + 1) + (2 * state.stack.sigma.length + 2 * queued state + 4) +
    (state.stack.sigma.length + state.stack.ready.length + 1) + 3

/-- `wait?`: the prepared prefix, the consumer lookup, the mate mark test,
the sigma boundary scan, and the waiting-cell read and write. -/
def waitCost (certificate : Certificate) (state : ReservationState) : Nat :=
  prepareCost state + consumerLookupCost certificate + 1 + state.stack.sigma.length + 2

/-- `forward?`: the prepared prefix, the consumer lookup, the mate mark
test, the duplicate guard on the rebuilt active bucket, the par queue, and
the ready-top prepend (ready tail read and rewrite). -/
def forwardCost (certificate : Certificate) (state : ReservationState) : Nat :=
  prepareCost state + consumerLookupCost certificate + 1 +
    (queued state + 1) * (queued state + 1) + queueParCost certificate state +
    2 * state.stack.ready.length

/-- `unifyPayload?`: the prepared prefix, the tensor lookup, the mate mark
test, the previous-boundary read, the waiting-cell read, the tensor queue,
one par queue per payload occurrence, the two-level merge (two sigma and two
ready tail reads, the bucket rebuild, and the cell write), the merged-bucket
read, and the duplicate guard on the merged bucket. -/
def unifyPayloadCost (certificate : Certificate) (state : ReservationState) : Nat :=
  prepareCost state + consumerLookupCost certificate + 1 + 2 * state.stack.sigma.length + 1 +
    queueTensorCost certificate state +
    mergedPayloadLength state * queueParCost certificate state +
    (2 * state.stack.sigma.length + 2 * state.stack.ready.length + queued state + 1) +
    state.stack.ready.length + (queued state + 1) * (queued state + 1)

/-- One `dispatch?` call: the rule attempts made in precedence order, up to
and including the successful one, or all six when none succeeds. -/
def dispatchCost (certificate : Certificate) (state : ReservationState)
    (result : Option Figure7DispatchResult) : Nat :=
  let concl := conclCost certificate state
  let nop := concl + nopCost certificate state
  let new := nop + newCost certificate state
  let wait := new + waitCost certificate state
  let forward := wait + forwardCost certificate state
  let unify := forward + unifyPayloadCost certificate state
  match result with
  | some ⟨.concl, _⟩ => concl
  | some ⟨.nop, _⟩ => nop
  | some ⟨.new, _⟩ => new
  | some ⟨.wait, _⟩ => wait
  | some ⟨.forward, _⟩ => forward
  | some ⟨.unifyPayload, _⟩ => unify
  | none => unify

/-- `initializeReservation?`: the empty state (three carrier-sized arrays),
the source index, the carrier-fuelled search, the trace tail read, the
initial-enqueue guard (two carrier scans and constant tests) and update, and
the axiom reservation. -/
def initializationCost (certificate : Certificate) : Nat :=
  let n := certificate.formulas.size
  3 * n + indexCost certificate + (n + 1) + (n + 1) + (2 * n + 8) + 3

/-- `sequentialFinalTree?`: the live-component scan, and for a single live
component the frontier length test, one `findIdx?` over the frontier per
conclusion, and the duplicate scan of the order. -/
def extractionCost (certificate : Certificate) (state : ReservationState) : Nat :=
  let k := certificate.conclusions.length
  state.core.components.size +
    match state.core.liveComponents with
    | [component] => 1 + k * component.frontier.length + k * k + 1
    | _ => 0

/-- Length of the sequent inferred below a subtree, zero when inference fails. -/
def sequentLength (tree : CutFreeDerivation) : Nat :=
  (tree.infer?.map List.length).getD 0

/-- `infer?`: one step per axiom, two premise picks and one append per
tensor, two picks and one append per par, and the reorder (one indexed read
per position and the duplicate scan) per exchange. -/
def inferCost : CutFreeDerivation → Nat
  | .axiom _ _ => 1
  | .tensor _ _ leftTree rightTree =>
      inferCost leftTree + inferCost rightTree + 2 * sequentLength leftTree +
        2 * sequentLength rightTree + 1
  | .par _ _ premise => inferCost premise + 3 * sequentLength premise + 1
  | .exchange order premise =>
      inferCost premise + order.length * sequentLength premise + order.length * order.length + 1

/-- Carrier size of the fragment built below a subtree, zero when the build fails. -/
def fragmentSize (tree : CutFreeDerivation) : Nat :=
  (tree.build?.map fun fragment => fragment.formulas.size).getD 0

/-- Link count of the fragment built below a subtree, zero when the build fails. -/
def fragmentLinks (tree : CutFreeDerivation) : Nat :=
  (tree.build?.map fun fragment => fragment.links.length).getD 0

/-- `build?`: the axiom fragment; per tensor the two entry picks, the formula
array append, the shifted link map and append, and the entry append; per par
the two picks, the push, the link append, and the entry append; per exchange
the reorder. Entry lists are bounded by the fragment carriers. -/
def buildCost : CutFreeDerivation → Nat
  | .axiom _ _ => 2
  | .tensor _ _ leftTree rightTree =>
      buildCost leftTree + buildCost rightTree + 3 * fragmentSize leftTree +
        3 * fragmentSize rightTree + fragmentLinks leftTree + 2 * fragmentLinks rightTree + 2
  | .par _ _ premise =>
      buildCost premise + 3 * fragmentSize premise + fragmentLinks premise + 2
  | .exchange order premise =>
      buildCost premise + order.length * fragmentSize premise + order.length * order.length + 1

/-- `intrinsicCanonicalCode`: the occurrence walks from the conclusions (one
producer filter over the links and one append per visited occurrence), the
duplicate scan of the raw traversal, one owned-link filter per traversal
vertex, the relabel (the duplicate scan of the conclusion and link vertices,
one `idxOf` per link vertex and conclusion, and the formula map), and the
structural code (one token or unary character each). -/
def canonicalCodeCost (certificate : Certificate) : Nat :=
  let n := certificate.formulas.size
  let m := certificate.links.length
  let k := certificate.conclusions.length
  let raw := certificate.intrinsicTraversalRaw.length
  let traversal := certificate.intrinsicTraversalVertices.length
  let relabelled := (certificate.conclusions ++ certificate.links.flatMap Link.vertices).length
  raw * (m + 1) + raw * raw + traversal * (m + 1) +
    relabelled * relabelled + (3 * m + k) * n + n +
    (certificate.intrinsicCanonicalCode.foldl (fun acc token => acc + token.length + 1) 0)

/-- `verifyDerivation?`: the structural check, the conclusion labels, the
inference, the desequentialization, both canonical codes, and their
comparison (charged as the input code length). -/
def verificationCost (certificate : Certificate) (tree : CutFreeDerivation) : Nat :=
  structuralCost certificate + certificate.conclusions.length + inferCost tree + buildCost tree +
    (match tree.desequentialize? with
      | some output => canonicalCodeCost output
      | none => 0) +
    canonicalCodeCost certificate + certificate.intrinsicCanonicalCode.length + 1

/-- Result of the instrumented bounded dispatcher run. -/
structure DispatcherRun (certificate : Certificate) where
  state : ReservationState
  invariant : SchedulerInvariant certificate state
  calls : Nat
  cost : Nat

/-- `runDispatcher` with its call and operation counters. -/
def runDispatcherWithStats (certificate : Certificate) : (fuel : Nat) →
    (state : ReservationState) → SchedulerInvariant certificate state →
    DispatcherRun certificate
  | 0, state, invariant => ⟨state, invariant, 0, 0⟩
  | fuel + 1, state, invariant =>
      match equation : dispatch? certificate state invariant with
      | none => ⟨state, invariant, 1, dispatchCost certificate state none⟩
      | some result =>
          let rest := runDispatcherWithStats certificate fuel result.after
            (dispatch?_schedulerInvariant invariant equation)
          ⟨rest.state, rest.invariant, rest.calls + 1,
            rest.cost + dispatchCost certificate state (some result)⟩

/-- The instrumented run visits exactly the states of `runDispatcher`. -/
theorem runDispatcherWithStats_state (certificate : Certificate) (fuel : Nat)
    (state : ReservationState) (invariant : SchedulerInvariant certificate state) :
    (runDispatcherWithStats certificate fuel state invariant).state =
      runDispatcher certificate fuel state invariant := by
  induction fuel generalizing state invariant with
  | zero => rfl
  | succ fuel ih =>
      unfold runDispatcherWithStats runDispatcher
      split
      · rename_i noneEq
        split
        · rfl
        · rename_i result someEq
          rw [noneEq] at someEq
          cases someEq
      · rename_i result someEq
        split
        · rename_i noneEq
          rw [noneEq] at someEq
          cases someEq
        · rename_i result' someEq'
          have eq : result = result' := Option.some.inj (someEq.symm.trans someEq')
          subst eq
          exact ih _ _

/-- The bounded run makes at most `fuel` calls. -/
theorem runDispatcherWithStats_calls_le (certificate : Certificate) (fuel : Nat)
    (state : ReservationState) (invariant : SchedulerInvariant certificate state) :
    (runDispatcherWithStats certificate fuel state invariant).calls ≤ fuel := by
  induction fuel generalizing state invariant with
  | zero => exact Nat.le_refl 0
  | succ fuel ih =>
      unfold runDispatcherWithStats
      split
      · exact Nat.succ_le_succ (Nat.zero_le fuel)
      · exact Nat.succ_le_succ (ih _ _)

end SequentialCost

namespace Certificate

open SequentialCost

/-- Outcome of the instrumented public decision. -/
structure SequentialDecisionRun where
  accepted : Bool
  stats : SequentialDecisionStats
  deriving Repr, DecidableEq

/-- The public decision with its operation counters: the structural check,
initialization at the first conclusion, the bounded dispatcher run, the
final extraction, and the verification of the final derivation. -/
def sequentialDecisionWithStats (certificate : Certificate) : SequentialDecisionRun :=
  let structural := structuralCost certificate
  if wellFormed : certificate.wellFormed = true then
    match certificate.conclusions.head? with
    | none => ⟨false, .early structural 0⟩
    | some start =>
        let initialization := initializationCost certificate
        match equation : initializeReservation? certificate start with
        | none => ⟨false, .early structural initialization⟩
        | some state =>
            let invariant := initializeReservation?_schedulerInvariant
              (certificate.wellFormed_iff_structurallyWellFormed.mp wellFormed) equation
            let run := runDispatcherWithStats certificate (certificate.formulas.size + 1)
              state invariant
            let extraction := extractionCost certificate run.state
            match sequentialFinalTree? certificate run.state with
            | none =>
                ⟨false, ⟨structural, initialization, run.calls, run.cost, extraction, 0⟩⟩
            | some tree =>
                ⟨(certificate.verifyDerivation? tree).isSome,
                  ⟨structural, initialization, run.calls, run.cost, extraction,
                    verificationCost certificate tree⟩⟩
  else
    ⟨false, .early structural 0⟩

/-- The instrumented decision accepts exactly what the public decision accepts. -/
theorem sequentialDecisionWithStats_accepted (certificate : Certificate) :
    certificate.sequentialDecisionWithStats.accepted = certificate.unificationCheck := by
  unfold unificationCheck sequentialFastCheck sequentialReconstruct?
  by_cases wellFormed : certificate.wellFormed = true
  · rw [dif_pos wellFormed]
    cases headEq : certificate.conclusions.head? with
    | none =>
        unfold sequentialDecisionWithStats
        rw [dif_pos wellFormed, headEq]
        rfl
    | some start =>
        simp only [Option.bind_eq_bind, Option.bind_some]
        split
        · rename_i noneEq
          unfold sequentialDecisionWithStats
          rw [dif_pos wellFormed, headEq]
          dsimp only
          split
          · rfl
          · rename_i state someEq
            rw [noneEq] at someEq
            cases someEq
        · rename_i state someEq
          unfold sequentialDecisionWithStats
          rw [dif_pos wellFormed, headEq]
          dsimp only
          split
          · rename_i noneEq
            rw [noneEq] at someEq
            cases someEq
          · rename_i state' someEq'
            have eq : state = state' := Option.some.inj (someEq.symm.trans someEq')
            subst eq
            simp only [runDispatcherWithStats_state]
            cases sequentialFinalTree? certificate
                (runDispatcher certificate (certificate.formulas.size + 1) state
                  (initializeReservation?_schedulerInvariant
                    (certificate.wellFormed_iff_structurallyWellFormed.mp wellFormed) someEq)) with
            | none => rfl
            | some tree => rfl
  · unfold sequentialDecisionWithStats
    rw [dif_neg wellFormed, dif_neg wellFormed]
    rfl

end Certificate
end ProofNetIR
