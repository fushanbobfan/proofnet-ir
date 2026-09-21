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
- a duplicate scan by `eraseDups` is charged its list length times its
  accumulator of distinct elements plus one: the carrier size when the
  elements are carrier vertices, the list length when they are positions;
  a permutation decision is charged the square of its list length;
  the scheduler's duplicate guard `nodupGuard` is charged its bounds scan,
  its carrier-sized table, and its marking pass, `formulas.size + 2 *
  length`, which is its cost at every state the run visits because the
  invariant keeps every queued occurrence inside the carrier;
- an array read or write and a constant-work primitive are charged one;
- the consumer and source indices, rebuilt on every use, are charged
  `formulas.size + links.length`; a bucket scan of an index is charged
  `links.length`;
- a bounded search is charged its fuel plus one, and a representative walk
  is charged the parent-array size;
- a formula is measured in symbols, two per connective and one per atom,
  with an atom name counted as one symbol; building a dual or comparing two
  formulas is charged the symbols involved;
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

/-- Symbols of the formula stored at an occurrence, one for a missing one. -/
def formulaText (certificate : Certificate) (vertex : Vertex) : Nat :=
  2 * certificate.formulaComplexityAt vertex + 1

/-- Symbols of every stored formula. -/
def formulaTextTotal (certificate : Certificate) : Nat :=
  ((List.range certificate.formulas.size).map (formulaText certificate)).sum

/-- `linkLocallyWellFormed` at one link: the constant tests, the lookups,
and the dual construction and formula comparison at its vertices. -/
def linkCheckCost (certificate : Certificate) (link : Link) : Nat :=
  1 + (link.vertices.map (formulaText certificate)).sum

/-- `Certificate.wellFormed`: the size and length tests, the in-bounds scan
of the conclusions, the duplicate scan of the conclusions, one local check
per link, and one node check per occurrence (`nodeWellFormed`: one link
filter for the source count, one `contains` over the conclusions, and one
link filter for the parent-use count). -/
def structuralCost (certificate : Certificate) : Nat :=
  2 + certificate.conclusions.length +
    certificate.conclusions.length * (certificate.formulas.size + 1) +
    (certificate.links.map (linkCheckCost certificate)).sum +
    certificate.formulas.size *
      (2 * certificate.links.length + certificate.conclusions.length + 1)

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
  prepareCost state + consumerLookupCost certificate + indexCost certificate +
    (certificate.formulas.size + 1) + (certificate.formulas.size + 1) +
    (2 * state.stack.sigma.length + 2 * queued state + 4) +
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
    (certificate.formulas.size + 2 * (queued state + 1)) + queueParCost certificate state +
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
    state.stack.ready.length + (certificate.formulas.size + 2 * (queued state + 1))

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
  3 * certificate.formulas.size + indexCost certificate + (certificate.formulas.size + 1) +
    (certificate.formulas.size + 1) + (2 * certificate.formulas.size + 8) + 3

/-- `sequentialFinalTree?`: the live-component scan, and for a single live
component the frontier length test, one `findIdx?` over the frontier per
conclusion, and the duplicate scan of the order (positions below the
frontier length). -/
def extractionCost (certificate : Certificate) (state : ReservationState) : Nat :=
  state.core.components.size +
    match state.core.liveComponents with
    | [component] =>
        1 + certificate.conclusions.length * component.frontier.length +
          certificate.conclusions.length * (certificate.conclusions.length + 1) + 1
    | _ => 0

/-- Length of the sequent inferred below a subtree, zero when inference fails. -/
def sequentLength (tree : CutFreeDerivation) : Nat :=
  (tree.infer?.map List.length).getD 0

/-- `reorder?` of a list of the given length by an order: the length test,
the duplicate scan of the order (positions), the bounds scan, one indexed
read per position, and the permutation decision. -/
def reorderCost (length : Nat) (order : List Nat) : Nat :=
  1 + order.length * (order.length + 1) + order.length + order.length * length +
    length * length

/-- `infer?`: one step per axiom, two premise picks and one append per
tensor, two picks and one append per par, and the reorder per exchange. -/
def inferCost : CutFreeDerivation → Nat
  | .axiom _ _ => 1
  | .tensor _ _ leftTree rightTree =>
      inferCost leftTree + inferCost rightTree + 2 * sequentLength leftTree +
        2 * sequentLength rightTree + 1
  | .par _ _ premise => inferCost premise + 3 * sequentLength premise + 1
  | .exchange order premise => inferCost premise + reorderCost (sequentLength premise) order

/-- Carrier size of the fragment built below a subtree, zero when the build fails. -/
def fragmentSize (tree : CutFreeDerivation) : Nat :=
  (tree.build?.map fun fragment => fragment.formulas.size).getD 0

/-- Link count of the fragment built below a subtree, zero when the build fails. -/
def fragmentLinks (tree : CutFreeDerivation) : Nat :=
  (tree.build?.map fun fragment => fragment.links.length).getD 0

/-- Boundary entry count of the fragment built below a subtree, zero when the build fails. -/
def fragmentEntries (tree : CutFreeDerivation) : Nat :=
  (tree.build?.map fun fragment => fragment.entries.length).getD 0

/-- `build?`: the axiom fragment; per tensor the two entry picks, the formula
array append, the shifted link map and append, and the entry append; per par
the two picks, the push, the link append, and the entry append; per exchange
the reorder of the entries. -/
def buildCost : CutFreeDerivation → Nat
  | .axiom _ _ => 2
  | .tensor _ _ leftTree rightTree =>
      buildCost leftTree + buildCost rightTree + 2 * fragmentEntries leftTree +
        2 * fragmentEntries rightTree + fragmentSize leftTree + fragmentSize rightTree +
        fragmentLinks leftTree + 2 * fragmentLinks rightTree + 2
  | .par _ _ premise =>
      buildCost premise + 3 * fragmentEntries premise + fragmentLinks premise + 2
  | .exchange order premise => buildCost premise + reorderCost (fragmentEntries premise) order

/-- `intrinsicCanonicalize`: the occurrence walks from the conclusions (one
producer filter over the links and one append per visited occurrence), the
duplicate scan of the raw traversal (carrier vertices), one owned-link filter
per traversal vertex, and the relabel (the duplicate scan of the conclusion
and link vertices, one `idxOf` over the traversal per link vertex and
conclusion, and the formula map). -/
def canonicalizeCost (certificate : Certificate) : Nat :=
  certificate.intrinsicTraversalRaw.length * (certificate.links.length + 1) +
    certificate.intrinsicTraversalRaw.length * certificate.intrinsicTraversalRaw.length +
    certificate.intrinsicTraversalRaw.length * (certificate.formulas.size + 1) +
    certificate.intrinsicTraversalVertices.length * (certificate.links.length + 1) +
    (certificate.conclusions ++ certificate.links.flatMap Link.vertices).length *
      (certificate.formulas.size + 1) +
    (3 * certificate.links.length + certificate.conclusions.length) *
      certificate.traversalVertices.length +
    certificate.traversalVertices.length

/-- Comparing a certificate with another: its formula symbols, links, and
conclusions, charged for both sides. -/
def compareCost (certificate : Certificate) : Nat :=
  formulaTextTotal certificate + certificate.links.length + certificate.conclusions.length

/-- Canonicalization and comparison of the desequentialized output, when it exists. -/
def outputCost (tree : CutFreeDerivation) : Nat :=
  match tree.desequentialize? with
  | some output => canonicalizeCost output + compareCost output
  | none => 0

/-- `verifyDerivation?`: the structural check, the conclusion labels, the
inference, the desequentialization, both canonicalizations, and the
comparison of the canonicalized certificates. -/
def verificationCost (certificate : Certificate) (tree : CutFreeDerivation) : Nat :=
  structuralCost certificate + certificate.conclusions.length + inferCost tree + buildCost tree +
    outputCost tree + canonicalizeCost certificate + compareCost certificate + 1

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

open SequentialSchedulerState.SequentialStackState in
section
/-! ## Sizes of the scheduler state under the invariant -/

private theorem length_le_of_nodup_subset {values ambient : List Nat} (nodup : values.Nodup)
    (subset : ∀ value ∈ values, value ∈ ambient) : values.length ≤ ambient.length := by
  induction values generalizing ambient with
  | nil => simp
  | cons head tail ih =>
      have headMembership : head ∈ ambient := subset head (by simp)
      have tailSubset : ∀ value ∈ tail, value ∈ ambient.erase head := by
        intro value membership
        have valueMembership : value ∈ ambient := subset value (by simp [membership])
        have different : value ≠ head := by
          intro same
          subst value
          exact (List.nodup_cons.mp nodup).1 membership
        exact (List.mem_erase_of_ne different).2 valueMembership
      have tailBound := ih (List.nodup_cons.mp nodup).2 tailSubset
      rw [List.length_erase_of_mem headMembership] at tailBound
      have positive : 0 < ambient.length := List.length_pos_of_mem headMembership
      simp only [List.length_cons]
      omega

private theorem length_le_of_nodup_bounded {values : List Nat} {size : Nat}
    (nodup : values.Nodup) (bounded : ∀ value ∈ values, value < size) :
    values.length ≤ size := by
  have := length_le_of_nodup_subset nodup (ambient := List.range size)
    (fun value member ↦ List.mem_range.mpr (bounded value member))
  simpa using this

/-- The sigma boundary list is bounded by the carrier: it is strictly
increasing below the raw-age horizon, which is at most the waiting-table size. -/
theorem sigma_length_le {certificate : Certificate} {state : ReservationState}
    (invariant : ReservationInvariant certificate state) :
    state.stack.sigma.length ≤ certificate.formulas.size := by
  have shaped := invariant.stack_wellShaped
  have nodup : state.stack.sigma.Nodup :=
    shaped.sigma_partition.strictIncreasing.imp fun lt ↦ Nat.ne_of_lt lt
  have horizon : state.stack.nextAge ≤ certificate.formulas.size :=
    shaped.waiting_size ▸ shaped.nextAge_le_waiting
  exact Nat.le_trans (length_le_of_nodup_bounded nodup fun boundary member ↦
    shaped.sigma_partition.boundary_lt boundary member) horizon

/-- The ready stack has one bucket per sigma boundary. -/
theorem ready_length_le {certificate : Certificate} {state : ReservationState}
    (invariant : ReservationInvariant certificate state) :
    state.stack.ready.length ≤ certificate.formulas.size :=
  invariant.stack_wellShaped.ready_aligned ▸ sigma_length_le invariant

/-- The parent array grows with the raw-age horizon, which is inside the carrier. -/
theorem parents_size_le {certificate : Certificate} {state : ReservationState}
    (invariant : ReservationInvariant certificate state) :
    state.core.parents.size ≤ certificate.formulas.size := by
  have shaped := invariant.stack_wellShaped
  rw [invariant.realizesSigma.horizon_eq]
  exact shaped.waiting_size ▸ shaped.nextAge_le_waiting

/-- Queued occurrences are duplicate-free and unmarked, hence inside the carrier. -/
theorem queued_le {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state) :
    queued state ≤ certificate.formulas.size := by
  apply length_le_of_nodup_bounded invariant.queued_vertices_nodup
  intro vertex member
  have unmarked := invariant.queued_vertices_unmarked vertex member
  have bound := (Array.getElem?_eq_some_iff.mp unmarked).1
  rw [invariant.realizesSigma.marks_eq, invariant.stack_wellShaped.marks_size] at bound
  exact bound

/-- The conclusion list is duplicate-free inside the carrier. -/
theorem conclusions_length_le {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) :
    certificate.conclusions.length ≤ certificate.formulas.size :=
  length_le_of_nodup_bounded
    (CutFreeDerivation.nodup_of_eraseDups_length_eq structural.2.2.2.1) structural.2.2.1

/-- Every waiting payload is part of the queued occurrences. -/
private theorem mergedPayloadLength_le_waiting (state : ReservationState) :
    mergedPayloadLength state ≤ state.stack.waitingVertices.length := by
  unfold mergedPayloadLength
  split
  · exact Nat.zero_le _
  · rename_i boundary _
    split
    · rename_i payload lookup
      have member : WaitingCell.initialized payload ∈ state.stack.waiting.toList :=
        List.mem_iff_getElem?.mpr ⟨boundary, by simpa using lookup⟩
      unfold SequentialStackState.waitingVertices
      have sub : List.Sublist payload
          (state.stack.waiting.toList.flatMap WaitingCell.vertices) := by
        have := List.sublist_flatten_of_mem
          (List.mem_map_of_mem (f := WaitingCell.vertices) member)
        simpa [List.flatMap, WaitingCell.vertices] using this
      exact sub.length_le
    · exact Nat.zero_le _

private theorem waiting_length_le_queued (state : ReservationState) :
    state.stack.waitingVertices.length ≤ queued state := by
  unfold queued SequentialStackState.queuedVertices
  simp

/-- A merged payload is inside the carrier. -/
theorem mergedPayloadLength_le {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state) :
    mergedPayloadLength state ≤ certificate.formulas.size :=
  Nat.le_trans (mergedPayloadLength_le_waiting state)
    (Nat.le_trans (waiting_length_le_queued state) (queued_le invariant))

/-! ## One dispatcher call -/

/-- Linear bound of one dispatcher call, apart from payload activation. -/
def callBound (certificate : Certificate) : Nat :=
  62 * (certificate.formulas.size + certificate.links.length + 1)

/-- Bound of one par queue, the unit of payload activation. -/
def activationCost (certificate : Certificate) : Nat :=
  5 * certificate.formulas.size + 3

/-- One par queue costs at most one activation. -/
theorem queueParCost_le {certificate : Certificate} {state : ReservationState}
    (invariant : ReservationInvariant certificate state) :
    queueParCost certificate state ≤ activationCost certificate := by
  have := parents_size_le invariant
  unfold queueParCost activationCost
  omega

/-- Payload occurrences activated by a call: the merged payload of a
`unifyPayload` success, or of the failed final attempt. -/
def activated (state : ReservationState) : Option Figure7DispatchResult → Nat
  | some ⟨.unifyPayload, _⟩ => mergedPayloadLength state
  | none => mergedPayloadLength state
  | some _ => 0

/-- One dispatcher call costs at most the linear call bound plus one
activation per payload occurrence it activates. -/
theorem dispatchCost_le {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    (result : Option Figure7DispatchResult) :
    dispatchCost certificate state result ≤
      callBound certificate + activated state result * activationCost certificate := by
  have sigma := sigma_length_le invariant.toReservationInvariant
  have ready := ready_length_le invariant.toReservationInvariant
  have parents := parents_size_le invariant.toReservationInvariant
  have queuedBound := queued_le invariant
  have conclusions := conclusions_length_le invariant.structural
  have queuePar := queueParCost_le invariant.toReservationInvariant
  have payloadTerm : mergedPayloadLength state * queueParCost certificate state ≤
      mergedPayloadLength state * activationCost certificate :=
    Nat.mul_le_mul_left _ queuePar
  have activation : activationCost certificate = 5 * certificate.formulas.size + 3 := rfl
  unfold dispatchCost conclCost nopCost newCost waitCost forwardCost unifyPayloadCost
    prepareCost conclusionLookupCost consumerLookupCost uniqueConsumerCost indexCost
    nodeCheckCost queueTensorCost callBound activated
  rcases result with _ | ⟨kind, after⟩
  · simp only
    omega
  · cases kind <;> simp only <;> omega

/-! ## The waiting potential -/

/-- Occurrences currently stored in waiting cells. -/
def waitingTotal (state : ReservationState) : Nat :=
  state.stack.waitingVertices.length

private theorem sum_map_set {l : List WaitingCell} {index : Nat} (bound : index < l.length)
    (cell : WaitingCell) :
    ((l.set index cell).map fun c ↦ (WaitingCell.vertices c).length).sum +
        (WaitingCell.vertices l[index]).length =
      (l.map fun c ↦ (WaitingCell.vertices c).length).sum + (WaitingCell.vertices cell).length := by
  induction l generalizing index with
  | nil => simp at bound
  | cons head tail ih =>
      cases index with
      | zero => simp [Nat.add_comm, Nat.add_left_comm]
      | succ index =>
          have := ih (Nat.lt_of_succ_lt_succ bound) (index := index)
          simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]
          omega

/-- Replacing one waiting cell changes the stored total by the cell difference. -/
private theorem waitingTotal_set (stack : SequentialStackState) {boundary : Nat} {old : WaitingCell}
    (lookup : stack.waiting[boundary]? = some old) (cell : WaitingCell) :
    ({ stack with waiting := stack.waiting.setIfInBounds boundary cell } :
        SequentialStackState).waitingVertices.length + (WaitingCell.vertices old).length =
      stack.waitingVertices.length + (WaitingCell.vertices cell).length := by
  have bound : boundary < stack.waiting.size := (Array.getElem?_eq_some_iff.mp lookup).1
  have oldEq : stack.waiting.toList[boundary] = old := by
    have := List.getElem?_eq_getElem (l := stack.waiting.toList) (by simpa using bound)
    rw [Array.getElem?_toList, lookup] at this
    exact (Option.some.inj this).symm
  unfold SequentialStackState.waitingVertices
  simp only [Array.toList_setIfInBounds, List.length_flatMap]
  have := sum_map_set (l := stack.waiting.toList) (by simpa using bound) cell
  rw [oldEq] at this
  exact this

private theorem waitingTotal_eq_of_waiting_eq {left right : SequentialStackState}
    (eq : left.waiting = right.waiting) :
    left.waitingVertices.length = right.waitingVertices.length := by
  unfold SequentialStackState.waitingVertices
  rw [eq]

/-- Replacing one waiting cell changes the stored total by the cell difference,
for any state whose waiting table is the replaced one. -/
private theorem waitingTotal_replace {stack after : SequentialStackState} {boundary : Nat}
    {old : WaitingCell} (lookup : stack.waiting[boundary]? = some old) (cell : WaitingCell)
    (afterEq : after.waiting = stack.waiting.setIfInBounds boundary cell) :
    after.waitingVertices.length + (WaitingCell.vertices old).length =
      stack.waitingVertices.length + (WaitingCell.vertices cell).length := by
  rw [waitingTotal_eq_of_waiting_eq (right := { stack with
    waiting := stack.waiting.setIfInBounds boundary cell }) afterEq]
  exact waitingTotal_set stack lookup cell

/-- The prepared prefix does not touch the waiting table. -/
private theorem prepared_waiting_eq {before : ReservationState} (step : PreparedStep before) :
    step.stackResult.after.waiting = before.stack.waiting :=
  (SequentialStackState.popReadyMark?_exact step.stack_eq).2.2.2.2.2.2.2.1

/-- The merged payload read by the cost model is the payload the merge consumes. -/
private theorem mergedPayloadLength_eq {state : ReservationState} {sigmaPrefix : List RawTokenAge}
    {previousBoundary activeBoundary : RawTokenAge} {payload : List Vertex}
    (sigmaEq : state.stack.sigma = sigmaPrefix ++ [previousBoundary, activeBoundary])
    (waitingEq : state.stack.waiting[previousBoundary]? = some (.initialized payload)) :
    mergedPayloadLength state = payload.length := by
  unfold mergedPayloadLength
  have boundary : state.stack.sigma.dropLast.getLast? = some previousBoundary := by
    rw [sigmaEq]
    simp [List.dropLast_append_of_ne_nil]
  rw [boundary]
  simp [waitingEq]

/-- One successful call: the payload it activates plus the occurrences still
waiting afterwards are at most the occurrences waiting before plus one. -/
theorem waitingTotal_step {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state) {result : Figure7DispatchResult}
    (equation : dispatch? certificate state invariant = some result) :
    activated state (some result) + waitingTotal result.after ≤ waitingTotal state + 1 := by
  obtain ⟨step⟩ := (dispatch?_some_iff invariant).mp equation
  unfold waitingTotal
  cases step with
  | concl conclEq =>
      obtain ⟨rule⟩ := (concl?_some_iff invariant.toReservationInvariant).mp conclEq
      rw [rule.output_eq]
      simp only [activated, PreparedStep.after, Nat.zero_add]
      rw [waitingTotal_eq_of_waiting_eq (prepared_waiting_eq rule.prepared)]
      exact Nat.le_succ _
  | nop _ nopEq =>
      obtain ⟨rule⟩ := (nop?_some_iff invariant.toReservationInvariant).mp nopEq
      rw [rule.output_eq]
      simp only [activated, PreparedStep.after, Nat.zero_add]
      rw [waitingTotal_eq_of_waiting_eq (prepared_waiting_eq rule.prepared)]
      exact Nat.le_succ _
  | new _ _ newEq =>
      obtain ⟨rule⟩ := (new?_some_iff invariant.toReservationInvariant).mp newEq
      obtain ⟨enqueue⟩ :=
        SequentialStackState.operationalNewEnqueue?_some_iff.mp rule.stack_enqueue_eq
      rw [rule.output_eq]
      simp only [activated, Nat.zero_add]
      have popWaiting : rule.stackResult.after.waiting = state.stack.waiting :=
        (SequentialStackState.popReadyMark?_exact rule.stack_eq).2.2.2.2.2.2.2.1
      have undefinedAt : rule.stackResult.after.waiting[enqueue.active]? = some .undefined :=
        enqueue.ready.2.2.2.2.2.2.2.2.2.2.1
      have replaced := waitingTotal_replace undefinedAt (.initialized [])
        (after := rule.stackAfter) (congrArg SequentialStackState.waiting enqueue.after_eq)
      simp only [WaitingCell.vertices, List.length_nil, Nat.add_zero] at replaced
      rw [replaced, waitingTotal_eq_of_waiting_eq popWaiting]
      exact Nat.le_succ _
  | wait _ _ _ waitEq =>
      obtain ⟨rule⟩ := (wait?_some_iff invariant.toReservationInvariant).mp waitEq
      obtain ⟨prepend⟩ :=
        SequentialStackState.prependWaiting?_some_iff.mp rule.destination.stack_eq
      rw [rule.destination.output_eq]
      simp only [activated, Nat.zero_add]
      have replaced := waitingTotal_replace prepend.initialized
        (.initialized (rule.consumer.conclusion :: prepend.payload))
        (after := rule.destination.stackAfter)
        (congrArg SequentialStackState.waiting prepend.after_eq)
      simp only [WaitingCell.vertices, List.length_cons] at replaced
      have prefixEq : rule.prepared.after.stack.waitingVertices.length =
          state.stack.waitingVertices.length :=
        waitingTotal_eq_of_waiting_eq (prepared_waiting_eq rule.prepared)
      omega
  | forward _ _ _ _ forwardEq =>
      obtain ⟨rule⟩ := (forward?_some_iff invariant.toReservationInvariant).mp forwardEq
      rw [rule.output_eq]
      simp only [activated, Nat.zero_add]
      have keep : rule.stackAfter.waiting = rule.prepared.stackResult.after.waiting := by
        have := congrArg SequentialStackState.waiting rule.prependStep.after_eq
        exact this
      rw [waitingTotal_eq_of_waiting_eq keep,
        waitingTotal_eq_of_waiting_eq (prepared_waiting_eq rule.prepared)]
      exact Nat.le_succ _
  | unifyPayload _ _ _ _ _ unifyEq =>
      obtain ⟨rule⟩ := (unifyPayload?_some_iff invariant.toReservationInvariant).mp unifyEq
      rw [rule.output_eq]
      simp only [activated]
      have popSigma : rule.prepared.stackResult.after.sigma = state.stack.sigma :=
        (SequentialStackState.popReadyMark?_exact rule.prepared.stack_eq).2.2.2.2.2.1
      have popWaiting := prepared_waiting_eq rule.prepared
      have merged := mergedPayloadLength_eq (state := state)
        (popSigma ▸ rule.mergeStep.sigma_eq) (popWaiting ▸ rule.mergeStep.waiting_initialized)
      have replaced := waitingTotal_replace rule.mergeStep.waiting_initialized .undefined
        (after := rule.stackAfter) (congrArg SequentialStackState.waiting rule.mergeStep.after_eq)
      simp only [WaitingCell.vertices, List.length_nil, Nat.add_zero] at replaced
      have prefixEq : rule.prepared.stackResult.after.waitingVertices.length =
          state.stack.waitingVertices.length :=
        waitingTotal_eq_of_waiting_eq popWaiting
      omega

/-! ## The dispatcher phase -/

/-- The instrumented run: its operations, plus the occurrences still waiting
at the end weighted by one activation, are bounded by the calls made, the
occurrences waiting at the start, and one failed final attempt. -/
theorem runDispatcherWithStats_cost_le {certificate : Certificate} (fuel : Nat)
    (state : ReservationState) (invariant : SchedulerInvariant certificate state) :
    (runDispatcherWithStats certificate fuel state invariant).cost +
        waitingTotal (runDispatcherWithStats certificate fuel state invariant).state *
          activationCost certificate ≤
      (runDispatcherWithStats certificate fuel state invariant).calls *
          (callBound certificate + activationCost certificate) +
        waitingTotal state * activationCost certificate +
        certificate.formulas.size * activationCost certificate := by
  induction fuel generalizing state invariant with
  | zero =>
      simp only [runDispatcherWithStats, Nat.zero_mul, Nat.zero_add]
      exact Nat.le_add_right _ _
  | succ fuel ih =>
    unfold runDispatcherWithStats
    split
    · rename_i noneEq
      simp only
      have call := dispatchCost_le invariant none
      have payload : mergedPayloadLength state * activationCost certificate ≤
          certificate.formulas.size * activationCost certificate :=
        Nat.mul_le_mul_right _ (mergedPayloadLength_le invariant)
      simp only [activated] at call
      omega
    · rename_i result someEq
      simp only
      have rest := ih result.after (dispatch?_schedulerInvariant invariant someEq)
      have call := dispatchCost_le invariant (some result)
      have potential := Nat.mul_le_mul_right (activationCost certificate)
        (waitingTotal_step invariant someEq)
      rw [Nat.add_mul, Nat.add_mul, Nat.one_mul] at potential
      have calls : ((runDispatcherWithStats certificate fuel result.after
            (dispatch?_schedulerInvariant invariant someEq)).calls + 1) *
          (callBound certificate + activationCost certificate) =
          (runDispatcherWithStats certificate fuel result.after
            (dispatch?_schedulerInvariant invariant someEq)).calls *
            (callBound certificate + activationCost certificate) +
          (callBound certificate + activationCost certificate) := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [calls]
      omega

/-- Initialization leaves every waiting cell undefined. -/
theorem waitingTotal_initial {certificate : Certificate} {start : Vertex}
    {state : ReservationState} (equation : initializeReservation? certificate start = some state) :
    waitingTotal state = 0 := by
  obtain ⟨step⟩ := initializeReservation?_some_iff.mp equation
  obtain ⟨ready, _⟩ := SequentialStackState.initEnqueue?_some_iff.mp step.stack_eq
  have undefined := ready.2.2.2.2.1
  unfold waitingTotal SequentialStackState.waitingVertices
  rw [step.output_eq]
  show (step.stackAfter.waiting.toList.flatMap WaitingCell.vertices).length = 0
  have waitingEq : step.stackAfter.waiting = (ReservationState.empty certificate).stack.waiting :=
    (SequentialStackState.initEnqueue?_exact step.stack_eq).2.2.2.2.1
  rw [waitingEq]
  simp only [List.length_eq_zero_iff, List.flatMap_eq_nil_iff]
  intro cell member
  obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
  rw [Array.getElem?_toList] at lookup
  have bound := (Array.getElem?_eq_some_iff.mp lookup).1
  have := undefined.lookup bound
  rw [this] at lookup
  cases lookup
  rfl

/-- The dispatcher phase of the public decision is quadratic: the run from the
initial reservation makes at most `formulas.size + 1` calls, each linear
apart from payload activation, and activates each waiting occurrence once. -/
theorem dispatchPhase_le {certificate : Certificate} {start : Vertex} {state : ReservationState}
    (equation : initializeReservation? certificate start = some state)
    (invariant : SchedulerInvariant certificate state) :
    (runDispatcherWithStats certificate (certificate.formulas.size + 1) state invariant).cost ≤
      72 * (certificate.formulas.size + 1) *
        (certificate.formulas.size + certificate.links.length + 1) := by
  have run := runDispatcherWithStats_cost_le (certificate.formulas.size + 1) state invariant
  have calls := runDispatcherWithStats_calls_le certificate (certificate.formulas.size + 1)
    state invariant
  rw [waitingTotal_initial equation, Nat.zero_mul, Nat.add_zero] at run
  have callsBound : (runDispatcherWithStats certificate (certificate.formulas.size + 1) state
        invariant).calls * (callBound certificate + activationCost certificate) ≤
      (certificate.formulas.size + 1) * (callBound certificate + activationCost certificate) :=
    Nat.mul_le_mul_right _ calls
  have final : (certificate.formulas.size + 1) *
        (callBound certificate + activationCost certificate) +
        certificate.formulas.size * activationCost certificate ≤
      72 * (certificate.formulas.size + 1) *
        (certificate.formulas.size + certificate.links.length + 1) := by
    unfold callBound activationCost
    have inner : 62 * (certificate.formulas.size + certificate.links.length + 1) +
          (5 * certificate.formulas.size + 3) + (5 * certificate.formulas.size + 3) ≤
        72 * (certificate.formulas.size + certificate.links.length + 1) := by omega
    calc (certificate.formulas.size + 1) *
          (62 * (certificate.formulas.size + certificate.links.length + 1) +
            (5 * certificate.formulas.size + 3)) +
          certificate.formulas.size * (5 * certificate.formulas.size + 3)
        ≤ (certificate.formulas.size + 1) *
          (62 * (certificate.formulas.size + certificate.links.length + 1) +
            (5 * certificate.formulas.size + 3)) +
          (certificate.formulas.size + 1) * (5 * certificate.formulas.size + 3) :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
      _ = (certificate.formulas.size + 1) *
          (62 * (certificate.formulas.size + certificate.links.length + 1) +
            (5 * certificate.formulas.size + 3) + (5 * certificate.formulas.size + 3)) := by
          simp only [Nat.mul_add]
      _ ≤ (certificate.formulas.size + 1) *
          (72 * (certificate.formulas.size + certificate.links.length + 1)) :=
          Nat.mul_le_mul_left _ inner
      _ = 72 * (certificate.formulas.size + 1) *
          (certificate.formulas.size + certificate.links.length + 1) := by
          rw [Nat.mul_left_comm, Nat.mul_assoc]
  omega

end

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
