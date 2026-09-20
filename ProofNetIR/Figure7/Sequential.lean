import ProofNetIR.Figure7.Closure
import ProofNetIR.Figure7.Termination

/-!
# The sequential fast path

`runDispatcher` executes the canonical Figure-7 dispatcher for a bounded
number of calls, threading the scheduler invariant as a proof argument.
`sequentialReconstruct?` initializes at the first conclusion, runs the
dispatcher with the formula-carrier budget, exchanges the final component's
frontier into the public conclusion order, and accepts only a derivation that
passes the independent verifier, so `sequentialFastCheck` is sound by
construction. `runDispatcher_spec` shows that from any started reachable state
of a correct certificate the run ends reachable, fully marked, and unable to
dispatch (ledger items D3 and D4). `StructurallyWellFormed.initializeReservation?_isSome` proves that
initialization succeeds at every in-bounds start, through the carrier
complexity bound `StructurallyWellFormed.formulaComplexityAt_lt_size`.
Completeness of `sequentialFastCheck` (ledger item D1) is not proved here:
the verification of the final component's derivation remains open.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge

/-- Execute at most `fuel` canonical dispatches, stopping at the first failed call.
The invariant argument is proof-only and is threaded through successful steps. -/
def runDispatcher (certificate : Certificate) : (fuel : Nat) →
    (state : ReservationState) → SchedulerInvariant certificate state → ReservationState
  | 0, state, _ => state
  | fuel + 1, state, invariant =>
      match equation : dispatch? certificate state invariant with
      | none => state
      | some result => runDispatcher certificate fuel result.after
          (dispatch?_schedulerInvariant invariant equation)

private theorem run_invariant {certificate : Certificate} (fuel : Nat)
    (state : ReservationState) (invariant : SchedulerInvariant certificate state) :
    SchedulerInvariant certificate (runDispatcher certificate fuel state invariant) := by
  induction fuel generalizing state with
  | zero => exact invariant
  | succ fuel ih =>
      unfold runDispatcher
      split
      · exact invariant
      · exact ih _ _

private theorem run_reachable {certificate : Certificate} (fuel : Nat)
    (state : ReservationState) (invariant : SchedulerInvariant certificate state)
    (reachable : ReachableByImplementedDispatcher certificate state) :
    ReachableByImplementedDispatcher certificate
      (runDispatcher certificate fuel state invariant) := by
  induction fuel generalizing state with
  | zero => exact reachable
  | succ fuel ih =>
      unfold runDispatcher
      split
      · exact reachable
      · rename_i result equation
        exact ih _ _ (reachable.dispatch invariant equation)

private def DispatcherStopped (certificate : Certificate) (state : ReservationState) : Prop :=
  ∃ invariant : SchedulerInvariant certificate state, dispatch? certificate state invariant = none

private theorem run_stopped {certificate : Certificate} (fuel : Nat)
    (state : ReservationState) (invariant : SchedulerInvariant certificate state)
    (budget : certificate.formulas.size < dispatchMeasure state + fuel) :
    DispatcherStopped certificate (runDispatcher certificate fuel state invariant) := by
  induction fuel generalizing state with
  | zero =>
      have := dispatchMeasure_le invariant
      omega
  | succ fuel ih =>
      simp only [runDispatcher]
      split
      · exact ⟨invariant, by assumption⟩
      · rename_i result equation
        have nextInvariant := dispatch?_schedulerInvariant invariant equation
        obtain ⟨step⟩ := (dispatch?_some_iff invariant).mp equation
        have increase := step.measure_eq
        exact ih result.after nextInvariant (by omega)

private theorem run_started {certificate : Certificate} (fuel : Nat)
    (state : ReservationState) (invariant : SchedulerInvariant certificate state)
    (started : 0 < state.stack.nextAge) :
    0 < (runDispatcher certificate fuel state invariant).stack.nextAge := by
  induction fuel generalizing state with
  | zero => exact started
  | succ fuel ih =>
      unfold runDispatcher
      split
      · exact started
      · rename_i result equation
        obtain ⟨step⟩ := (dispatch?_some_iff invariant).mp equation
        obtain ⟨evidence⟩ := step.tagEvidence
        have count := evidence.linkIndices_length_add_nextAge
        exact ih result.after _ (Nat.lt_of_lt_of_le started (by omega))

/-- From any started reachable state of a correct certificate, the carrier-sized
run ends at a reachable, invariant, fully marked state where dispatch fails. -/
theorem runDispatcher_spec {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    (reachable : ReachableByImplementedDispatcher certificate state)
    (correct : certificate.DeclarativelyCorrect) (started : 0 < state.stack.nextAge) :
    let final := runDispatcher certificate (certificate.formulas.size + 1) state invariant
    ReachableByImplementedDispatcher certificate final ∧
      ∃ finalInvariant : SchedulerInvariant certificate final,
        dispatch? certificate final finalInvariant = none ∧ final.core.allMarked = true := by
  dsimp only
  have finalReachable := run_reachable (certificate.formulas.size + 1) state invariant reachable
  obtain ⟨finalInvariant, stopped⟩ :=
    run_stopped (certificate.formulas.size + 1) state invariant (by omega)
  have finalStarted := run_started (certificate.formulas.size + 1) state invariant started
  refine ⟨finalReachable, finalInvariant, stopped, ?_⟩
  rcases finalReachable.dispatch_or_allMarked correct finalStarted with succeeds | marked
  · obtain ⟨result, equation⟩ := succeeds
    rw [stopped] at equation
    cases equation
  · exact marked

end SequentialFigure7

namespace Certificate

open SequentialSchedulerBridge SequentialFigure7

private def occurrenceOrder? (source : List Vertex) : List Vertex → Option (List Nat)
  | [] => some []
  | vertex :: rest => do
      let index ← source.findIdx? (· == vertex)
      let tail ← occurrenceOrder? source rest
      pure (index :: tail)

private def sequentialFinalTree? (certificate : Certificate)
    (state : ReservationState) : Option CutFreeDerivation := do
  let [component] := state.core.liveComponents | none
  guard (component.frontier.length = certificate.conclusions.length)
  let order ← occurrenceOrder? component.frontier certificate.conclusions
  guard (order.eraseDups.length = order.length)
  pure (.exchange order component.tree)

/-- Initialize at the first conclusion, run the canonical dispatcher with the
formula-carrier budget, and independently verify the exchanged final component.
No switching enumeration or recursive reconstruction fallback is executed. -/
def sequentialReconstruct? (certificate : Certificate) :
    Option (DerivationVerificationResult certificate) :=
  if wellFormed : certificate.wellFormed = true then do
    let start ← certificate.conclusions.head?
    match equation : initializeReservation? certificate start with
    | none => none
    | some state =>
        let invariant := initializeReservation?_schedulerInvariant
          (certificate.wellFormed_iff_structurallyWellFormed.mp wellFormed) equation
        let final := runDispatcher certificate (certificate.formulas.size + 1) state invariant
        let tree ← sequentialFinalTree? certificate final
        certificate.verifyDerivation? tree
  else none

/-! ## Formula complexity is below the carrier size

Descending through producer links from a vertex visits distinct occurrences,
one per subformula, so a formula's connective count is smaller than the
number of occurrences. This is the fuel bound the production `nextAxiom?`
wrapper needs. -/

/-- `Under certificate top vertex`: `vertex` is reached from `top` by descending
through producer links. -/
private inductive Under (certificate : Certificate) (top : Vertex) : Vertex → Prop
  | refl : Under certificate top top
  | step {conclusion premise : Vertex} {link : Link} :
      Under certificate top conclusion → link ∈ certificate.links →
      link.produces conclusion = true → premise ∈ link.premises →
      Under certificate top premise

private theorem produces_conclusion {link : Link} {vertex : Vertex}
    (produces : link.produces vertex = true) :
    (∃ left right, link = .tensor left right vertex) ∨ ∃ left right, link = .par left right vertex := by
  cases link with
  | «axiom» _ _ => simp [Link.produces] at produces
  | tensor left right conclusion =>
      simp only [Link.produces, beq_iff_eq] at produces
      exact Or.inl ⟨left, right, by rw [produces]⟩
  | par left right conclusion =>
      simp only [Link.produces, beq_iff_eq] at produces
      exact Or.inr ⟨left, right, by rw [produces]⟩

/-- A premise of a producer has strictly smaller complexity than the conclusion. -/
private theorem premise_lt {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {link : Link} {conclusion premise : Vertex}
    (member : link ∈ certificate.links) (produces : link.produces conclusion = true)
    (premise_mem : premise ∈ link.premises) :
    certificate.formulaComplexityAt premise < certificate.formulaComplexityAt conclusion := by
  have wf := structural.2.2.2.2.1 _ member
  have lt := LinkWellFormed.premise_complexity_lt_conclusion wf premise_mem
  rcases produces_conclusion produces with ⟨l, r, rfl⟩ | ⟨l, r, rfl⟩ <;>
    simpa [linkConclusionComplexity] using lt

private theorem Under.complexity_le {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {top vertex : Vertex}
    (under : Under certificate top vertex) :
    certificate.formulaComplexityAt vertex ≤ certificate.formulaComplexityAt top := by
  induction under with
  | refl => exact Nat.le_refl _
  | step _ member produces premise_mem ih =>
      exact Nat.le_trans (Nat.le_of_lt (premise_lt structural member produces premise_mem)) ih

private theorem premise_not_conclusion {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {link : Link} (member : link ∈ certificate.links)
    {vertex : Vertex} (premise : vertex ∈ link.premises) (bound : vertex < certificate.formulas.size) :
    vertex ∉ certificate.conclusions := by
  intro conclusion
  have node := structural.2.2.2.2.2 vertex bound
  have zero : (certificate.links.filter (Link.usesAsPremise vertex)).length = 0 := by
    have := node.2
    rw [if_pos conclusion] at this
    exact this
  have inFilter : link ∈ certificate.links.filter (Link.usesAsPremise vertex) := by
    rw [List.mem_filter]
    exact ⟨member, by simpa [Link.usesAsPremise] using premise⟩
  have := List.length_pos_of_mem inFilter
  omega

private theorem two_le_length_of_mem_ne {α : Type} {a b : α} {l : List α}
    (aMem : a ∈ l) (bMem : b ∈ l) (ne : a ≠ b) : 2 ≤ l.length := by
  induction l with
  | nil => simp at aMem
  | cons head tail ih =>
      simp only [List.mem_cons] at aMem bMem
      simp only [List.length_cons]
      rcases aMem with rfl | aTail
      · rcases bMem with rfl | bTail
        · exact absurd rfl ne
        · have := List.length_pos_of_mem bTail
          omega
      · rcases bMem with rfl | bTail
        · have := List.length_pos_of_mem aTail
          omega
        · have := ih aTail bTail
          omega

/-- A vertex is a premise of at most one link. -/
private theorem premise_unique {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {link link' : Link}
    (member : link ∈ certificate.links) (member' : link' ∈ certificate.links)
    {vertex : Vertex} (premise : vertex ∈ link.premises) (premise' : vertex ∈ link'.premises)
    (bound : vertex < certificate.formulas.size) : link = link' := by
  by_cases same : link = link'
  · exact same
  have node := structural.2.2.2.2.2 vertex bound
  have notConclusion := premise_not_conclusion structural member premise bound
  have one : (certificate.links.filter (Link.usesAsPremise vertex)).length = 1 := by
    have := node.2
    rw [if_neg notConclusion] at this
    exact this
  have inFilter : link ∈ certificate.links.filter (Link.usesAsPremise vertex) := by
    rw [List.mem_filter]
    exact ⟨member, by simpa [Link.usesAsPremise] using premise⟩
  have inFilter' : link' ∈ certificate.links.filter (Link.usesAsPremise vertex) := by
    rw [List.mem_filter]
    exact ⟨member', by simpa [Link.usesAsPremise] using premise'⟩
  have := two_le_length_of_mem_ne inFilter inFilter' same
  omega

private theorem premise_bound {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {link : Link} (member : link ∈ certificate.links)
    {vertex : Vertex} (premise : vertex ∈ link.premises) : vertex < certificate.formulas.size := by
  have wf := structural.2.2.2.2.1 _ member
  cases link with
  | «axiom» _ _ => simp [Link.premises] at premise
  | tensor l r c =>
      simp only [Link.premises, List.mem_cons, List.not_mem_nil, or_false] at premise
      rcases premise with rfl | rfl
      · exact wf.2.2.2.1
      · exact wf.2.2.2.2.1
  | par l r c =>
      simp only [Link.premises, List.mem_cons, List.not_mem_nil, or_false] at premise
      rcases premise with rfl | rfl
      · exact wf.2.2.2.1
      · exact wf.2.2.2.2.1

private theorem produces_unique {link : Link} {a b : Vertex}
    (pa : link.produces a = true) (pb : link.produces b = true) : a = b := by
  cases link with
  | «axiom» _ _ => simp [Link.produces] at pa
  | tensor _ _ c =>
      simp only [Link.produces, beq_iff_eq] at pa pb
      exact pa.symm.trans pb
  | par _ _ c =>
      simp only [Link.produces, beq_iff_eq] at pa pb
      exact pa.symm.trans pb

/-- The subtrees below the two premises of one link are disjoint. -/
private theorem under_disjoint {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {link : Link} {top left right : Vertex}
    (member : link ∈ certificate.links) (produces : link.produces top = true)
    (leftMem : left ∈ link.premises) (rightMem : right ∈ link.premises) (ne : left ≠ right)
    {vertex : Vertex} (underLeft : Under certificate left vertex)
    (underRight : Under certificate right vertex) : False := by
  induction underLeft with
  | refl =>
      -- `left` is under `right`: then it descends from `right` through its own consumer
      cases underRight with
      | refl => exact ne rfl
      | step underRight' member' produces' premise' =>
          rename_i conclusion' link'
          have same := premise_unique structural member' member premise' leftMem
            (premise_bound structural member leftMem)
          subst same
          have topEq := produces_unique produces' produces
          subst topEq
          have le := Under.complexity_le structural underRight'
          have lt := premise_lt structural member produces rightMem
          omega
  | step underLeft' member' produces' premise' ih =>
      rename_i conclusion' premise'' link'
      cases underRight with
      | refl =>
          -- `right` is strictly under `left`: same contradiction with the roles swapped
          have same := premise_unique structural member' member premise' rightMem
            (premise_bound structural member rightMem)
          subst same
          have topEq := produces_unique produces' produces
          subst topEq
          have le := Under.complexity_le structural underLeft'
          have lt := premise_lt structural member produces leftMem
          omega
      | step underRight' member'' produces'' premise''' =>
          have same := premise_unique structural member' member'' premise' premise'''
            (premise_bound structural member' premise')
          subst same
          have concEq := produces_unique produces' produces''
          subst concEq
          exact ih underRight'

/-- Occurrences below a vertex, with an explicit fuel. -/
private def below (certificate : Certificate) : Nat → Vertex → List Vertex
  | 0, _ => []
  | fuel + 1, vertex =>
      match certificate.links.find? (Link.produces vertex) with
      | some (.tensor left right _) =>
          vertex :: (below certificate fuel left ++ below certificate fuel right)
      | some (.par left right _) =>
          vertex :: (below certificate fuel left ++ below certificate fuel right)
      | _ => [vertex]

private theorem Under.trans {certificate : Certificate} {top mid vertex : Vertex}
    (first : Under certificate top mid) (second : Under certificate mid vertex) :
    Under certificate top vertex := by
  induction second with
  | refl => exact first
  | step _ member produces premise_mem ih => exact .step ih member produces premise_mem

private theorem below_under {certificate : Certificate} :
    ∀ (fuel : Nat) (top vertex : Vertex), vertex ∈ below certificate fuel top →
      Under certificate top vertex := by
  intro fuel
  induction fuel with
  | zero => intro top vertex member; simp [below] at member
  | succ fuel ih =>
      intro top vertex member
      unfold below at member
      split at member
      all_goals first
        | (rename_i left right conclusion found
           have producer := List.find?_some found
           have linkMem := List.mem_of_find?_eq_some found
           simp only [List.mem_cons, List.mem_append] at member
           rcases member with rfl | inLeft | inRight
           · exact .refl
           · exact Under.trans (.step .refl linkMem producer (by simp [Link.premises])) (ih left vertex inLeft)
           · exact Under.trans (.step .refl linkMem producer (by simp [Link.premises])) (ih right vertex inRight))
        | (simp only [List.mem_singleton] at member
           subst member
           exact .refl)

/-- Under a structurally well-formed certificate, `below` visits distinct
occurrences and at least `complexity + 1` of them, given enough fuel. -/
private theorem below_spec {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) :
    ∀ (fuel : Nat) (top : Vertex), top < certificate.formulas.size →
      certificate.formulaComplexityAt top < fuel →
      (below certificate fuel top).Nodup ∧
        certificate.formulaComplexityAt top + 1 ≤ (below certificate fuel top).length ∧
        ∀ vertex ∈ below certificate fuel top, vertex < certificate.formulas.size := by
  intro fuel
  induction fuel with
  | zero => intro top _ lt; exact absurd lt (Nat.not_lt_zero _)
  | succ fuel ih =>
      intro top bound enough
      -- the producer of a connective occurrence, if any
      cases found : certificate.links.find? (Link.produces top) with
      | none =>
          -- no producer: the formula is an atom, complexity zero
          have zero : certificate.formulaComplexityAt top = 0 := by
            have node := structural.2.2.2.2.2 top bound
            unfold formulaComplexityAt
            cases formula : certificate.formula? top with
            | none => rfl
            | some value =>
                cases value with
                | atom _ _ => rfl
                | tensor _ _ | par _ _ =>
                    exfalso
                    have := node.1
                    rw [formula] at this
                    have count : (certificate.links.filter (Link.produces top)).length = 1 := this
                    have noneFilter := List.find?_eq_none.mp found
                    cases filtered : certificate.links.filter (Link.produces top) with
                    | nil => rw [filtered] at count; simp at count
                    | cons link _ =>
                        have linkMem : link ∈ certificate.links.filter (Link.produces top) := by
                          rw [filtered]; exact List.mem_cons_self ..
                        have := List.mem_filter.mp linkMem
                        exact noneFilter link this.1 this.2
          unfold below
          rw [found]
          simp only [List.nodup_cons, List.not_mem_nil, List.nodup_nil, and_true, List.length_singleton,
            List.mem_singleton, not_false_eq_true, true_and, zero, Nat.zero_add, Nat.le_refl]
          intro vertex eq; rw [eq]; exact bound
      | some link =>
          have producer := List.find?_some found
          have linkMem := List.mem_of_find?_eq_some found
          rcases produces_conclusion producer with ⟨left, right, linkEq⟩ | ⟨left, right, linkEq⟩ <;>
          · have wf := structural.2.2.2.2.1 _ linkMem
            rw [linkEq] at wf
            have leftMem : left ∈ link.premises := by rw [linkEq]; simp [Link.premises]
            have rightMem : right ∈ link.premises := by rw [linkEq]; simp [Link.premises]
            have leftLt := premise_lt structural linkMem producer leftMem
            have rightLt := premise_lt structural linkMem producer rightMem
            have leftBound := premise_bound structural linkMem leftMem
            have rightBound := premise_bound structural linkMem rightMem
            obtain ⟨leftNodup, leftLength, leftIn⟩ := ih left leftBound (by omega)
            obtain ⟨rightNodup, rightLength, rightIn⟩ := ih right rightBound (by omega)
            have ne : left ≠ right := wf.1
            -- complexity of the conclusion is the sum plus one
            have sum : certificate.formulaComplexityAt top =
                certificate.formulaComplexityAt left + certificate.formulaComplexityAt right + 1 := by
              obtain ⟨_, _, _, _, _, _, typing⟩ := wf
              unfold formulaComplexityAt
              split at typing
              · rename_i lf rf cf leftEq rightEq concEq
                rw [leftEq, rightEq, concEq, typing]
                simp [Formula.complexity]
              · exact typing.elim
            unfold below
            rw [found, linkEq]
            refine ⟨?_, ?_, ?_⟩
            · rw [List.nodup_cons, List.nodup_append]
              refine ⟨?_, leftNodup, rightNodup, ?_⟩
              · intro member
                rcases List.mem_append.mp member with inLeft | inRight
                · have := Under.complexity_le structural (below_under fuel left top inLeft)
                  omega
                · have := Under.complexity_le structural (below_under fuel right top inRight)
                  omega
              · intro a aMem b bMem same
                subst same
                exact under_disjoint structural linkMem producer leftMem rightMem ne
                  (below_under fuel left a aMem) (below_under fuel right a bMem)
            · simp only [List.length_cons, List.length_append]
              omega
            · intro vertex member
              simp only [List.mem_cons, List.mem_append] at member
              rcases member with rfl | inLeft | inRight
              · exact bound
              · exact leftIn vertex inLeft
              · exact rightIn vertex inRight

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

/-- The complexity of an in-bounds occurrence is below the carrier size. -/
theorem StructurallyWellFormed.formulaComplexityAt_lt_size {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {vertex : Vertex}
    (bound : vertex < certificate.formulas.size) :
    certificate.formulaComplexityAt vertex < certificate.formulas.size := by
  obtain ⟨nodup, length, bounded⟩ :=
    below_spec structural (certificate.formulaComplexityAt vertex + 1) vertex bound (Nat.lt_succ_self _)
  have := length_le_of_nodup_bounded nodup bounded
  omega

/-! ## Initialization totality -/

/-- In the empty reservation state every occurrence is untagged and unassigned. -/
private theorem empty_clearThrough (certificate : Certificate) (rank : Nat) :
    SequentialUnification.SearchClearThrough certificate
      (SequentialSchedulerBridge.ReservationState.empty certificate).core
      (SequentialSchedulerBridge.ReservationState.empty certificate).tags rank := by
  intro vertex bound _
  constructor
  · simp [SequentialSchedulerBridge.ReservationState.empty, bound]
  · simp [SequentialSchedulerBridge.ReservationState.empty, initialUnificationState,
      UnificationState.assignedToken?, bound]

/-- Initialization succeeds at every in-bounds start of a structurally
well-formed certificate. -/
theorem StructurallyWellFormed.initializeReservation?_isSome {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {start : Vertex}
    (bound : start < certificate.formulas.size) :
    ∃ state, SequentialSchedulerBridge.initializeReservation? certificate start = some state := by
  obtain ⟨result, search⟩ :=
    SequentialUnification.nextAxiomWithFuel?_exists_of_structural_clearThrough structural
      (initialUnificationState_abstractable certificate) bound
      (empty_clearThrough certificate _) (structural.formulaComplexityAt_lt_size bound)
  obtain ⟨reached, partner, route⟩ := SequentialUnification.nextAxiomWithFuel?_route search
  have oriented := route.orientedEndpoints?_eq
  -- the reserved axiom is well formed
  have linkMem : Link.axiom result.left result.right ∈ certificate.links :=
    List.mem_of_getElem? result.exactLink
  have wf := structural.2.2.2.2.1 _ linkMem
  have leftBound : result.left < certificate.formulas.size := wf.2.1
  have rightBound : result.right < certificate.formulas.size := wf.2.2.1
  have distinct : result.left ≠ result.right := wf.1
  have reachedBound : reached < certificate.formulas.size := by
    rcases route.storedEndpoints with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> assumption
  have partnerBound : partner < certificate.formulas.size := by
    rcases route.storedEndpoints with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
  have reachedNe : reached ≠ partner := by
    rcases route.storedEndpoints with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact distinct
    · exact distinct.symm
  -- delayed initialization
  have ready : SequentialSchedulerState.SequentialStackState.InitReady
      (SequentialSchedulerBridge.ReservationState.empty certificate).stack reached partner := by
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, reachedNe⟩
    · unfold SequentialSchedulerState.SequentialStackState.AllMarksUndefined
      rw [Array.all_eq_true]
      intro i hi
      simp [SequentialSchedulerBridge.ReservationState.empty,
        SequentialSchedulerState.SequentialStackState.empty]
    · unfold SequentialSchedulerState.SequentialStackState.AllWaitingUndefined
      rw [Array.all_eq_true]
      intro i hi
      simp [SequentialSchedulerBridge.ReservationState.empty,
        SequentialSchedulerState.SequentialStackState.empty]
    · simp [SequentialSchedulerBridge.ReservationState.empty, SequentialSchedulerState.SequentialStackState.empty]
      exact structural.1
    · simpa [SequentialSchedulerBridge.ReservationState.empty,
        SequentialSchedulerState.SequentialStackState.empty] using reachedBound
    · simpa [SequentialSchedulerBridge.ReservationState.empty,
        SequentialSchedulerState.SequentialStackState.empty] using partnerBound
  have enqueue := SequentialSchedulerState.SequentialStackState.initEnqueue?_some_iff.mpr ⟨ready, rfl⟩
  -- production reservation
  have atom : ∃ name positive, certificate.formula? result.left = some (.atom name positive) := by
    obtain ⟨_, _, _, typing⟩ := wf
    split at typing
    · rename_i name positive _ leftEq _
      exact ⟨name, positive, leftEq⟩
    · exact typing.elim
  obtain ⟨name, positive, leftFormula⟩ := atom
  have component : UnificationComponent.axiom? certificate result.left result.right =
      some { tree := .axiom name positive, frontier := [result.left, result.right] } := by
    simp [UnificationComponent.axiom?, leftFormula]
  have readyAxiom : certificate.AxiomReservationReady
      (SequentialSchedulerBridge.ReservationState.empty certificate).core result.left result.right := by
    refine ⟨(certificate.linkLocallyWellFormed_iff _).mpr wf, ?_, ?_, rfl⟩
    · simp [SequentialSchedulerBridge.ReservationState.empty, initialUnificationState, leftBound]
    · simp [SequentialSchedulerBridge.ReservationState.empty, initialUnificationState, rightBound]
  have reserve : (certificate.reserveAxiomAt?
      (SequentialSchedulerBridge.ReservationState.empty certificate).core result.linkIndex).isSome := by
    simp [Certificate.reserveAxiomAt?, result.exactLink, readyAxiom, component]
  obtain ⟨after, reserveEq⟩ := Option.isSome_iff_exists.mp reserve
  have search' : SequentialUnification.nextAxiom? certificate
      (SequentialSchedulerBridge.ReservationState.empty certificate).core
      (SequentialUnification.sourceIndex certificate) (SequentialUnification.sourceIndex_sound certificate)
      (SequentialSchedulerBridge.ReservationState.empty certificate).tags start = some result := search
  have isSome : (SequentialSchedulerBridge.initializeReservation? certificate start).isSome := by
    simp only [SequentialSchedulerBridge.initializeReservation?, Bind.bind, Option.bind]
    rw [search']
    dsimp only
    have oriented' : @SequentialUnification.NextAxiomResult.orientedEndpoints? certificate
        (SequentialSchedulerBridge.ReservationState.empty certificate).core certificate.formulas.size
        (SequentialSchedulerBridge.ReservationState.empty certificate).tags result =
        some (reached, partner) := oriented
    rw [oriented']
    dsimp only
    rw [enqueue]
    dsimp only
    rw [reserveEq]
    rfl
  exact Option.isSome_iff_exists.mp isSome

/-- Boolean acceptance of the sequential proof-bearing reconstruction. -/
def sequentialFastCheck (certificate : Certificate) : Bool :=
  certificate.sequentialReconstruct?.isSome

/-- Every accepted sequential candidate is accepted by the reference checker. -/
theorem sequentialFastCheck_sound (certificate : Certificate)
    (accepted : certificate.sequentialFastCheck = true) : certificate.check = true := by
  unfold sequentialFastCheck at accepted
  cases equation : certificate.sequentialReconstruct? with
  | none => simp [equation] at accepted
  | some result =>
      rw [← result.equivalent.check_eq]
      exact result.outputAccepted

end Certificate
end ProofNetIR
