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
At a fully marked reachable correct state the sole component owns the full
carrier, its frontier permutes the conclusions, and the final exchange
infers their formula sequent. The builder succeeds on that tree. Completeness
(D1) still requires equivalence of the built certificate to the input; the
exact numbering correspondence and its remaining induction cases are below.
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

private theorem allMarked_lookup {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state) (marked : state.core.allMarked = true)
    {vertex : Vertex} (bound : vertex < certificate.formulas.size) :
    ∃ raw, state.core.marks[vertex]? = some (some raw) := by
  have sizeBound : vertex < state.core.marks.size := by
    rwa [invariant.core_abstractable.markArraySize]
  have someMark := (Array.all_eq_true.mp marked) vertex sizeBound
  obtain ⟨raw, equation⟩ := Option.isSome_iff_exists.mp someMark
  exact ⟨raw, by rw [Array.getElem?_eq_getElem sizeBound, equation]⟩

private theorem occurrence_owned_ne_nil {certificate : Certificate} {tree : CutFreeDerivation}
    {frontier used owned : List Nat}
    (witness : certificate.OccurrenceDerivation tree frontier used owned) : owned ≠ [] := by
  induction witness <;> simp_all

private theorem filterMap_singleton_of_unique {α : Type} (items : List (Option α))
    {index : Nat} {value : α} (lookup : items[index]? = some (some value))
    (unique : ∀ i v, items[i]? = some (some v) → i = index) :
    items.filterMap id = [value] := by
  induction items generalizing index with
  | nil => simp at lookup
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
          subst head
          have empty : tail.filterMap id = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro v member
            obtain ⟨cell, member, equation⟩ := List.mem_filterMap.mp member
            have cellEq : cell = some v := equation
            subst cell
            obtain ⟨i, bound, eq⟩ := List.mem_iff_getElem.mp member
            have impossible := unique (i + 1) v (by simpa using
              (List.getElem?_eq_getElem bound).trans (congrArg some eq))
            omega
          simp [empty]
      | succ index =>
          have headEq : head = none := by
            cases head with
            | none => rfl
            | some v => have := unique 0 v rfl; omega
          subst head
          simpa using ih (by simpa using lookup) (fun i v eq ↦ by
            have := unique (i + 1) v (by simpa using eq)
            omega)

/-- A fully marked reachable correct state has exactly one live component,
at its active boundary, and that component owns every input occurrence. -/
theorem finalComponents_eq_singleton {certificate : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate state)
    (correct : certificate.DeclarativelyCorrect) (marked : state.core.allMarked = true) :
    ∃ age component used owned,
      state.stack.sigma.getLast? = some age ∧
      state.core.components[age]? = some (some component) ∧
      state.core.liveComponents = [component] ∧
      certificate.ComponentOccurrenceWitness component used owned ∧
      (∀ vertex, vertex ∈ owned ↔ vertex < certificate.formulas.size) := by
  have invariant := reachable.schedulerInvariant correct.1
  have marksEq := invariant.realizesSigma.marks_eq
  obtain ⟨raw, rawLookup⟩ := allMarked_lookup invariant marked correct.1.1
  have started : 0 < state.stack.nextAge := Nat.zero_lt_of_lt
    (invariant.stack_wellShaped.assigned_age_bound 0 raw (by rw [← marksEq]; exact rawLookup))
  have sigmaNonempty : state.stack.sigma ≠ [] := by
    intro empty
    have := invariant.stack_wellShaped.sigma_partition.empty_iff.mp empty
    exact (Nat.ne_of_gt started) this
  obtain ⟨age, sigmaLast⟩ := Option.isSome_iff_exists.mp
    (List.getLast?_isSome.mpr sigmaNonempty)
  obtain ⟨component, componentLookup⟩ :=
    (invariant.component_domain_exact age).mpr (List.mem_of_getLast? sigmaLast)
  have drained : ActiveTopDrained state := by
    refine ⟨age, component, sigmaLast, componentLookup, ?_⟩
    intro vertex _ unmarked
    have bound : vertex < certificate.formulas.size := by
      have := (Array.getElem?_eq_some_iff.mp unmarked).1
      rwa [invariant.core_abstractable.markArraySize] at this
    obtain ⟨raw, lookup⟩ := allMarked_lookup invariant marked bound
    rw [lookup] at unmarked
    cases unmarked
  obtain ⟨active, seed, activeLast, readyLast, seedClass, seedBound⟩ :=
    seed_of_drained invariant drained
  have activeEq : active = age := Option.some.inj (activeLast.symm.trans sigmaLast)
  subst active
  have classes : ∀ {vertex}, vertex < certificate.formulas.size →
      markClass? state.stack vertex = some age :=
    (reachable.regionClosure correct.1).class_of_empty_active invariant correct
      sigmaLast readyLast seedClass seedBound
  have representative : ∀ {vertex raw : Nat},
      state.core.marks[vertex]? = some (some raw) → state.core.representative raw = age := by
    intro vertex raw lookup
    have bound : vertex < certificate.formulas.size := by
      have := (Array.getElem?_eq_some_iff.mp lookup).1
      rwa [invariant.core_abstractable.markArraySize] at this
    have rawBound := invariant.stack_wellShaped.assigned_age_bound vertex raw
      (by rw [← marksEq]; exact lookup)
    have cls := classes bound
    unfold markClass? at cls
    rw [← marksEq, lookup] at cls
    change SequentialSchedulerState.sigmaBoundary?
      state.stack.sigma raw = some age at cls
    rw [invariant.realizesSigma.representative_eq_boundary rawBound] at cls
    exact Option.some.inj cls
  obtain ⟨usedAt, ownedAt, live, _, owns⟩ := invariant.component_forest_provenance
  have unique : ∀ i c, state.core.components[i]? = some (some c) → i = age := by
    intro i c lookup
    obtain ⟨witness, accounted⟩ := live lookup
    obtain ⟨vertex, member⟩ := List.exists_mem_of_ne_nil _
      (occurrence_owned_ne_nil witness.derivation)
    rcases accounted vertex member with ⟨raw, assigned, rep⟩ | ⟨unmarked, _⟩
    · exact rep.symm.trans (representative assigned)
    · obtain ⟨raw, assigned⟩ := allMarked_lookup invariant marked
        (witness.derivation.owned_inBounds correct.1 vertex member)
      rw [assigned] at unmarked
      cases unmarked
  refine ⟨age, component, usedAt age, ownedAt age, sigmaLast, componentLookup, ?_,
    (live componentLookup).1, ?_⟩
  · exact filterMap_singleton_of_unique state.core.components.toList
      (by simpa using componentLookup) (by simpa using unique)
  · intro vertex
    constructor
    · exact (live componentLookup).1.derivation.owned_inBounds correct.1 vertex
    · intro bound
      obtain ⟨raw, assigned⟩ := allMarked_lookup invariant marked bound
      obtain ⟨i, c, rep, _, member⟩ := owns assigned
      have eq : i = age := rep.symm.trans (representative assigned)
      simpa [eq] using member

end SequentialFigure7

namespace Certificate

open SequentialSchedulerBridge SequentialFigure7

/-- Find the source position of each requested occurrence, retaining target order. -/
def occurrenceOrder? (source : List Vertex) : List Vertex → Option (List Nat)
  | [] => some []
  | vertex :: rest => do
      let index ← source.findIdx? (· == vertex)
      let tail ← occurrenceOrder? source rest
      pure (index :: tail)

/-- Extract the sole live component and exchange it into the input conclusion order. -/
def sequentialFinalTree? (certificate : Certificate)
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

private def consumedOccurrences (certificate : Certificate) (used : List Nat) : List Vertex :=
  used.flatMap fun index ↦ (certificate.links[index]?.map Link.premises).getD []

private theorem occurrence_count_eq {certificate : Certificate} {tree : CutFreeDerivation}
    {frontier used owned : List Nat}
    (witness : certificate.OccurrenceDerivation tree frontier used owned) (vertex : Vertex) :
    owned.count vertex =
      frontier.count vertex + (consumedOccurrences certificate used).count vertex := by
  induction witness with
  | «axiom» index left right name positive lookup formula =>
      simp [consumedOccurrences, lookup, Link.premises]
  | par witness index left right conclusion lf rf afterLeft context lookup lp rp ih =>
      have lcount := (CutFreeDerivation.pick?_perm lp.positional).count_eq vertex
      have rcount := (CutFreeDerivation.pick?_perm rp.positional).count_eq vertex
      simp only [List.count_cons, beq_iff_eq] at lcount rcount
      simp [consumedOccurrences, lookup, Link.premises, List.count_append, List.count_cons] at ih ⊢
      omega
  | tensor lw rw index left right conclusion lf rf lc rc lookup lp rp lih rih =>
      have lcount := (CutFreeDerivation.pick?_perm lp.positional).count_eq vertex
      have rcount := (CutFreeDerivation.pick?_perm rp.positional).count_eq vertex
      simp only [List.count_cons, beq_iff_eq] at lcount rcount
      simp [consumedOccurrences, lookup, Link.premises, List.count_append, List.count_cons]
        at lih rih ⊢
      omega
  | exchange witness order reordered equation ih =>
      have counts := (CutFreeDerivation.reorder?_perm equation).count_eq vertex
      omega

private theorem owned_producer_used {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {tree : CutFreeDerivation}
    {frontier used owned : List Nat}
    (witness : certificate.OccurrenceDerivation tree frontier used owned)
    {vertex : Vertex} (member : vertex ∈ owned) {link : Link}
    (submitted : link ∈ certificate.links) (produces : link.produces vertex = true) :
    ∃ index ∈ used, certificate.links[index]? = some link := by
  induction witness with
  | «axiom» index left right name positive lookup formula =>
      have endpoint : vertex = left ∨ vertex = right := by simpa using member
      exact (structural.axiomEndpoint_ne_connectiveConclusion
        (List.mem_of_getElem? lookup) endpoint submitted produces).elim
  | par witness index left right conclusion lf rf afterLeft context lookup lp rp ih =>
      rcases List.mem_cons.mp member with rfl | member
      · have eq := UnificationState.StructurallyWellFormed.producerLink_unique structural
          (List.mem_of_getElem? lookup) (by simp [Link.produces]) submitted produces
        exact ⟨index, by simp, lookup.trans (congrArg some eq)⟩
      · obtain ⟨i, mem, eq⟩ := ih member
        exact ⟨i, by simp [mem], eq⟩
  | tensor lw rw index left right conclusion lf rf lc rc lookup lp rp lih rih =>
      rcases List.mem_cons.mp member with rfl | member
      · have eq := UnificationState.StructurallyWellFormed.producerLink_unique structural
          (List.mem_of_getElem? lookup) (by simp [Link.produces]) submitted produces
        exact ⟨index, by simp, lookup.trans (congrArg some eq)⟩
      · rcases List.mem_append.mp member with lm | rm
        · obtain ⟨i, mem, eq⟩ := lih lm
          exact ⟨i, by simp [mem], eq⟩
        · obtain ⟨i, mem, eq⟩ := rih rm
          exact ⟨i, by simp [mem], eq⟩
  | exchange witness order reordered equation ih => exact ih member

private theorem consumed_iff_premise {certificate : Certificate} {used : List Nat}
    {vertex : Vertex} :
    vertex ∈ consumedOccurrences certificate used ↔
      ∃ index ∈ used, ∃ link, certificate.links[index]? = some link ∧ vertex ∈ link.premises := by
  simp only [consumedOccurrences, List.mem_flatMap]
  constructor
  · rintro ⟨index, member, premise⟩
    cases lookup : certificate.links[index]? with
    | none => simp [lookup] at premise
    | some link => exact ⟨index, member, link, lookup, by simpa [lookup] using premise⟩
  · rintro ⟨index, member, link, lookup, premise⟩
    exact ⟨index, member, by simpa [lookup] using premise⟩

/-- A linear occurrence derivation covering the input carrier exposes exactly
the certificate conclusions, up to their order. -/
theorem finalFrontier_perm {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {component : UnificationComponent}
    {used owned : List Nat} (witness : certificate.ComponentOccurrenceWitness component used owned)
    (covers : ∀ vertex, vertex ∈ owned ↔ vertex < certificate.formulas.size) :
    component.frontier.Perm certificate.conclusions := by
  have boundary : ∀ vertex, vertex ∈ component.frontier ↔ vertex ∈ certificate.conclusions := by
    intro vertex
    have counts := occurrence_count_eq witness.derivation vertex
    constructor
    · intro frontier
      have owned := witness.derivation.frontier_subset_owned vertex frontier
      have bound := (covers vertex).mp owned
      apply Classical.byContradiction
      intro nonconclusion
      have uses := (structural.2.2.2.2.2 vertex bound).2
      rw [if_neg nonconclusion] at uses
      obtain ⟨link, eq⟩ := List.length_eq_one_iff.mp uses
      have inFilter : link ∈ certificate.links.filter (Link.usesAsPremise vertex) := by
        rw [eq]; simp
      obtain ⟨submitted, premise⟩ := List.mem_filter.mp inFilter
      have premiseMem : vertex ∈ link.premises := by simpa [Link.usesAsPremise] using premise
      have consumed : vertex ∈ consumedOccurrences certificate used := by
        cases link with
        | «axiom» left right => simp [Link.premises] at premiseMem
        | tensor left right conclusion | par left right conclusion =>
            have wf := structural.2.2.2.2.1 _ submitted
            obtain ⟨i, mem, lookup⟩ := owned_producer_used structural witness.derivation
              ((covers conclusion).mpr wf.2.2.2.2.2.1) submitted (by simp [Link.produces])
            exact consumed_iff_premise.mpr ⟨i, mem, _, lookup, premiseMem⟩
      have one := (List.nodup_iff_count.mp witness.owned_nodup) vertex
      have positive := List.count_pos_iff.mpr frontier
      have consumedPositive := List.count_pos_iff.mpr consumed
      omega
    · intro conclusion
      have owned := (covers vertex).mpr (structural.2.2.1 vertex conclusion)
      have notConsumed : vertex ∉ consumedOccurrences certificate used := by
        intro consumed
        obtain ⟨i, _, link, lookup, premise⟩ := consumed_iff_premise.mp consumed
        exact premise_not_conclusion structural (List.mem_of_getElem? lookup) premise
          (structural.2.2.1 vertex conclusion) conclusion
      have zero := List.count_eq_zero.mpr notConsumed
      have positive := List.count_pos_iff.mpr owned
      apply List.count_pos_iff.mp
      omega
  have conclusionsNodup := CutFreeDerivation.nodup_of_eraseDups_length_eq structural.2.2.2.1
  apply List.perm_iff_count.mpr
  intro vertex
  have leftLe := (List.nodup_iff_count.mp witness.frontier_nodup) vertex
  have rightLe := (List.nodup_iff_count.mp conclusionsNodup) vertex
  by_cases member : vertex ∈ component.frontier
  · have leftPos := List.count_pos_iff.mpr member
    have rightPos := List.count_pos_iff.mpr ((boundary vertex).mp member)
    omega
  · rw [List.count_eq_zero.mpr member, List.count_eq_zero.mpr
      (fun inConclusions ↦ member ((boundary vertex).mpr inConclusions))]

private theorem occurrenceOrder_spec {source target : List Vertex}
    (subset : target ⊆ source) (nodup : target.Nodup) :
    ∃ order, occurrenceOrder? source target = some order ∧
      order.mapM (fun index ↦ source[index]?) = some target ∧
      order.length = target.length ∧ order.Nodup ∧
      (∀ index ∈ order, ∃ vertex ∈ target, source[index]? = some vertex) := by
  induction target with
  | nil => exact ⟨[], rfl, rfl, rfl, .nil, by simp⟩
  | cons vertex tail ih =>
      have find := List.findIdx?_eq_some_of_exists
        (xs := source) (p := (· == vertex)) ⟨vertex, subset (by simp), by simp⟩
      obtain ⟨bound, eq, _⟩ := List.findIdx?_eq_some_iff_getElem.mp find
      have lookup : source[source.findIdx (· == vertex)]? = some vertex := by
        rw [List.getElem?_eq_getElem bound, beq_iff_eq.mp eq]
      obtain ⟨order, orderEq, mapped, length, orderNodup, members⟩ :=
        ih (fun _ mem ↦ subset (by simp [mem])) (List.nodup_cons.mp nodup).2
      refine ⟨source.findIdx (· == vertex) :: order, ?_, ?_, by simp [length], ?_, ?_⟩
      · simp [occurrenceOrder?, find, orderEq]
      · simp [lookup, mapped]
      · apply List.nodup_cons.mpr
        refine ⟨?_, orderNodup⟩
        intro member
        obtain ⟨v, mem, eq⟩ := members _ member
        have same : v = vertex := Option.some.inj (eq.symm.trans lookup)
        exact (List.nodup_cons.mp nodup).1 (same ▸ mem)
      · intro i mem
        rcases List.mem_cons.mp mem with rfl | mem
        · exact ⟨vertex, by simp, lookup⟩
        · obtain ⟨v, mem, eq⟩ := members i mem
          exact ⟨v, by simp [mem], eq⟩

private theorem eraseDups_eq_of_nodup {values : List Nat} (nodup : values.Nodup) :
    values.eraseDups = values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      obtain ⟨fresh, tailNodup⟩ := List.nodup_cons.mp nodup
      rw [List.eraseDups_cons]
      have filterEq : tail.filter (fun v ↦ !v == head) = tail := by
        apply List.filter_eq_self.mpr
        intro v member
        simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
        intro eq
        exact fresh (eq ▸ member)
      rw [filterEq, ih tailNodup]

/-- Final extraction succeeds with a duplicate-free occurrence order that
reorders the sole live component into the exact ordered input boundary. -/
theorem sequentialFinalTree?_eq_some {certificate : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate state)
    (correct : certificate.DeclarativelyCorrect) (marked : state.core.allMarked = true) :
    ∃ component order used owned,
      state.core.liveComponents = [component] ∧
      certificate.ComponentOccurrenceWitness component used owned ∧
      (∀ vertex, vertex ∈ owned ↔ vertex < certificate.formulas.size) ∧
      occurrenceOrder? component.frontier certificate.conclusions = some order ∧
      order.Nodup ∧
      CutFreeDerivation.reorder? component.frontier order = some certificate.conclusions ∧
      sequentialFinalTree? certificate state = some (.exchange order component.tree) := by
  obtain ⟨_, component, used, owned, _, _, live, witness, covers⟩ :=
    finalComponents_eq_singleton reachable correct marked
  have permutation := finalFrontier_perm correct.1 witness covers
  obtain ⟨order, orderEq, mapped, length, nodup, members⟩ := occurrenceOrder_spec
    (fun _ mem ↦ permutation.mem_iff.mpr mem) (permutation.nodup witness.frontier_nodup)
  have eraseEq := eraseDups_eq_of_nodup nodup
  have bounded : ∀ i ∈ order, i < component.frontier.length := by
    intro i mem
    obtain ⟨v, _, lookup⟩ := members i mem
    exact (List.getElem?_eq_some_iff.mp lookup).1
  have orderLength : order.length = component.frontier.length :=
    length.trans permutation.length_eq.symm
  refine ⟨component, order, used, owned, live, witness, covers, orderEq, nodup, ?_, ?_⟩
  · rw [CutFreeDerivation.reorder?_eq_reorderCandidate?]
    simpa [CutFreeDerivation.reorderCandidate?, orderLength, eraseEq, List.all_eq_true, mapped]
      using bounded
  · simp [sequentialFinalTree?, live, permutation.length_eq, orderEq, eraseEq, guard]

/-- Final extraction infers the exact input sequent and builds an accepted
certificate. Equivalence of that output to the input is a separate obligation. -/
theorem sequentialFinalTree?_infer_eq {certificate : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate state)
    (correct : certificate.DeclarativelyCorrect) (marked : state.core.allMarked = true) :
    ∃ tree sequent, sequentialFinalTree? certificate state = some tree ∧
      certificate.conclusionFormulas? = some sequent ∧ tree.infer? = some sequent ∧
      ∃ output, tree.desequentialize? = some output ∧ output.check = true := by
  obtain ⟨component, order, _, _, _, witness, _, _, _, reorder, finalEq⟩ :=
    sequentialFinalTree?_eq_some reachable correct marked
  obtain ⟨sequent, inferred, labels⟩ :=
    (witness.derivation.exchange order certificate.conclusions reorder).formulaConsistent correct.1
  obtain ⟨output, built, _, checked⟩ :=
    CutFreeDerivation.desequentialize?_exists_checked_of_infer? inferred
  exact ⟨.exchange order component.tree, sequent, finalEq, labels, inferred, output, built, checked⟩

/-- Rename the fresh indices of a builder link to the occurrences they represent. -/
def relabelLink (numbering : List Nat) : Link → Link
  | .axiom left right => .axiom (numbering[left]?.getD 0) (numbering[right]?.getD 0)
  | .tensor left right conclusion => .tensor (numbering[left]?.getD 0)
      (numbering[right]?.getD 0) (numbering[conclusion]?.getD 0)
  | .par left right conclusion => .par (numbering[left]?.getD 0)
      (numbering[right]?.getD 0) (numbering[conclusion]?.getD 0)

/-- Exact correspondence between fresh builder indices and submitted occurrences.
`numbering[i]` is the input occurrence represented by fresh vertex `i`.
The ordered roots are literal; only the link storage order may vary. -/
structure OccurrenceBuildMatch (certificate : Certificate) (fragment : NetFragment)
    (frontier used owned numbering : List Nat) : Prop where
  size_eq : numbering.length = fragment.formulas.size
  owned_perm : numbering.Perm owned
  labels_eq : ∀ index, index < fragment.formulas.size →
    certificate.formula? (numbering[index]?.getD 0) = fragment.formulas[index]?
  roots_eq : fragment.roots.map (fun index ↦ numbering[index]?.getD 0) = frontier
  links_perm : (fragment.links.map (relabelLink numbering)).Perm
    (used.filterMap fun index ↦ certificate.links[index]?)

/-- The axiom build uses fresh vertices zero and one for the exact submitted
endpoints, retaining their orientation even when other labels repeat. -/
theorem occurrenceBuild_axiom_eq {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {index left right : Nat}
    {name : String} {positive : Bool}
    (lookup : certificate.links[index]? = some (.axiom left right))
    (label : certificate.formula? left = some (.atom name positive)) :
    ∃ fragment, (CutFreeDerivation.axiom name positive).build? = some fragment ∧
      OccurrenceBuildMatch certificate fragment
        [left, right] [index] [left, right] [left, right] := by
  let formula : Formula := .atom name positive
  let fragment : NetFragment :=
    ⟨#[formula, formula.dual], [.axiom 0 1], [formula, formula.dual], [0, 1]⟩
  have wf := structural.2.2.2.2.1 _ (List.mem_of_getElem? lookup)
  have rightLabel : certificate.formula? right = some formula.dual := by
    have typing := wf.2.2.2
    rw [label] at typing
    cases rightEq : certificate.formula? right with
    | none => simp [rightEq] at typing
    | some rightFormula =>
        simp [rightEq] at typing
        simp [formula, typing]
  refine ⟨fragment, rfl, rfl, .refl _, ?_, rfl, ?_⟩
  · intro vertex bound
    have two : vertex < 2 := bound
    have cases : vertex = 0 ∨ vertex = 1 := by omega
    rcases cases with rfl | rfl
    · exact label
    · exact rightLabel
  · simp [fragment, lookup, relabelLink]

/-- An exact occurrence exchange preserves the same fresh-vertex numbering,
formula labels, and submitted links, changing only the ordered roots. -/
theorem occurrenceBuild_exchange_eq {certificate : Certificate} {tree : CutFreeDerivation}
    {fragment : NetFragment} {frontier used owned numbering order reordered : List Nat}
    (built : tree.build? = some fragment)
    (matched : OccurrenceBuildMatch certificate fragment frontier used owned numbering)
    (reorder : CutFreeDerivation.reorder? frontier order = some reordered) :
    ∃ output, (CutFreeDerivation.exchange order tree).build? = some output ∧
      OccurrenceBuildMatch certificate output reordered used owned numbering := by
  let project := fun entry : Formula × Vertex ↦ numbering[entry.2]?.getD 0
  have entriesEq : fragment.entries.map project = frontier := by
    rw [← matched.roots_eq, ← fragment.entries_map_snd (CutFreeDerivation.build?_balanced built)]
    simp [List.map_map, project]
  obtain ⟨entries, entriesReorder, entriesMapped⟩ :=
    CutFreeDerivation.reorder?_exists_of_map_eq_some project (by rwa [entriesEq])
  refine ⟨NetFragment.ofEntries fragment.formulas fragment.links entries, ?_,
    matched.size_eq, matched.owned_perm, matched.labels_eq, ?_, matched.links_perm⟩
  · simp [CutFreeDerivation.build?, built, entriesReorder]
  · simpa [NetFragment.ofEntries, List.map_map, Function.comp_def, project] using entriesMapped

/-- Every vertex of a well-formed link is inside the carrier. -/
private theorem LinkWellFormed.vertices_lt {certificate : Certificate} {link : Link}
    (wf : certificate.LinkWellFormed link) :
    ∀ vertex ∈ link.vertices, vertex < certificate.formulas.size := by
  intro vertex member
  cases link with
  | «axiom» left right =>
      simp [Link.vertices] at member
      rcases member with rfl | rfl
      · exact wf.2.1
      · exact wf.2.2.1
  | tensor left right conclusion | par left right conclusion =>
      simp [Link.vertices] at member
      rcases member with rfl | rfl | rfl
      · exact wf.2.2.2.1
      · exact wf.2.2.2.2.1
      · exact wf.2.2.2.2.2.1

/-- Extending a numbering does not change the relabelling of an in-bounds link. -/
private theorem relabelLink_append {numbering extra : List Nat} {link : Link}
    (bounded : ∀ vertex ∈ link.vertices, vertex < numbering.length) :
    relabelLink (numbering ++ extra) link = relabelLink numbering link := by
  cases link with
  | «axiom» left right =>
      simp only [Link.vertices, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq] at bounded
      simp [relabelLink, List.getElem?_append_left bounded.1, List.getElem?_append_left bounded.2]
  | tensor left right conclusion | par left right conclusion =>
      simp only [Link.vertices, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq] at bounded
      simp [relabelLink, List.getElem?_append_left bounded.1,
        List.getElem?_append_left bounded.2.1, List.getElem?_append_left bounded.2.2]

/-- A vertex shifted past a prefix numbering is looked up in the suffix numbering. -/
private theorem getElem?_append_shift {front back extra : List Nat} {vertex : Nat}
    (bound : vertex < back.length) :
    (front ++ (back ++ extra))[vertex + front.length]? = back[vertex]? := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel, List.getElem?_append_left bound]

/-- A link shifted past a prefix numbering is relabelled by the suffix numbering. -/
private theorem relabelLink_shift {front back extra : List Nat} {link : Link}
    (bounded : ∀ vertex ∈ link.vertices, vertex < back.length) :
    relabelLink (front ++ (back ++ extra)) (link.shift front.length) =
      relabelLink back link := by
  have lookup : ∀ vertex, vertex < back.length →
      (front ++ (back ++ extra))[vertex + front.length]? = back[vertex]? :=
    fun _ bound ↦ getElem?_append_shift bound
  cases link with
  | «axiom» left right =>
      simp only [Link.vertices, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq] at bounded
      simp [relabelLink, Link.shift, lookup _ bounded.1, lookup _ bounded.2]
  | tensor left right conclusion | par left right conclusion =>
      simp only [Link.vertices, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq] at bounded
      simp [relabelLink, Link.shift, lookup _ bounded.1, lookup _ bounded.2.1,
        lookup _ bounded.2.2]

/-- Every boundary entry of a built fragment is labelled and in bounds, so its
numbering image carries the entry's formula in the input. -/
private theorem entry_label {certificate : Certificate} {tree : CutFreeDerivation}
    {fragment : NetFragment} {frontier used owned numbering : List Nat}
    (built : tree.build? = some fragment)
    (matched : OccurrenceBuildMatch certificate fragment frontier used owned numbering)
    {entry : Formula × Vertex} (member : entry ∈ fragment.entries) :
    entry.2 < numbering.length ∧
      certificate.formula? (numbering[entry.2]?.getD 0) = some entry.1 := by
  have lookup := CutFreeDerivation.build?_formulaConsistent built entry member
  have bound := (Array.getElem?_eq_some_iff.mp lookup).1
  exact ⟨matched.size_eq ▸ bound, (matched.labels_eq entry.2 bound).trans lookup⟩

/-- Built links stay inside the fragment carrier. -/
private theorem built_link_bounded {tree : CutFreeDerivation} {fragment : NetFragment}
    (built : tree.build? = some fragment) {link : Link} (member : link ∈ fragment.links) :
    ∀ vertex ∈ link.vertices, vertex < fragment.formulas.size :=
  LinkWellFormed.vertices_lt
    ((CutFreeDerivation.build?_structurallyWellFormed built).2.2.2.2.1 link member)

/-- The par build appends one fresh conclusion vertex numbered by the submitted
conclusion, keeping the premise numbering for every older vertex. -/
theorem occurrenceBuild_par_eq {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {premise : CutFreeDerivation}
    {fragment : NetFragment} {frontier used owned numbering : List Nat}
    (built : premise.build? = some fragment)
    (matched : OccurrenceBuildMatch certificate fragment frontier used owned numbering)
    {index left right conclusion leftFocus rightFocus : Nat} {afterLeft context : List Nat}
    (lookup : certificate.links[index]? = some (.par left right conclusion))
    (leftPick : CutFreeDerivation.pick? frontier leftFocus = some (left, afterLeft))
    (rightPick : CutFreeDerivation.pick? afterLeft rightFocus = some (right, context)) :
    ∃ output, (CutFreeDerivation.par leftFocus rightFocus premise).build? = some output ∧
      OccurrenceBuildMatch certificate output (context ++ [conclusion]) (index :: used)
        (conclusion :: owned) (numbering ++ [conclusion]) := by
  let project := fun entry : Formula × Vertex ↦ numbering[entry.2]?.getD 0
  have entriesEq : fragment.entries.map project = frontier := by
    rw [← matched.roots_eq, ← fragment.entries_map_snd (CutFreeDerivation.build?_balanced built)]
    simp [List.map_map, project]
  obtain ⟨leftEntry, afterLeftEntries, leftPickEntries, leftProj, afterLeftEq⟩ :=
    CutFreeDerivation.pick?_exists_of_map_eq_some project (by rwa [entriesEq])
  obtain ⟨rightEntry, contextEntries, rightPickEntries, rightProj, contextEq⟩ :=
    CutFreeDerivation.pick?_exists_of_map_eq_some project
      (values := afterLeftEntries) (by rw [afterLeftEq]; exact rightPick)
  simp only [project] at leftProj rightProj
  have afterLeftSub : ∀ entry ∈ afterLeftEntries, entry ∈ fragment.entries := fun entry mem ↦
    (CutFreeDerivation.pick?_perm leftPickEntries).mem_iff.mpr (by simp [mem])
  have leftMem : leftEntry ∈ fragment.entries :=
    (CutFreeDerivation.pick?_perm leftPickEntries).mem_iff.mpr (by simp)
  have rightMem : rightEntry ∈ fragment.entries :=
    afterLeftSub _ ((CutFreeDerivation.pick?_perm rightPickEntries).mem_iff.mpr (by simp))
  have contextSub : ∀ entry ∈ contextEntries, entry ∈ fragment.entries := fun entry mem ↦
    afterLeftSub _ ((CutFreeDerivation.pick?_perm rightPickEntries).mem_iff.mpr (by simp [mem]))
  obtain ⟨leftBound, leftLabel⟩ := entry_label built matched leftMem
  obtain ⟨rightBound, rightLabel⟩ := entry_label built matched rightMem
  rw [leftProj] at leftLabel
  rw [rightProj] at rightLabel
  have wf := structural.2.2.2.2.1 _ (List.mem_of_getElem? lookup)
  have conclusionLabel :
      certificate.formula? conclusion = some (.par leftEntry.1 rightEntry.1) := by
    have typing := wf.2.2.2.2.2.2
    rw [leftLabel, rightLabel] at typing
    cases conclusionEq : certificate.formula? conclusion with
    | none => simp [conclusionEq] at typing
    | some formula =>
        simp [conclusionEq] at typing
        simp [typing]
  let conclusionFormula : Formula := .par leftEntry.1 rightEntry.1
  let output : NetFragment := NetFragment.ofEntries (fragment.formulas.push conclusionFormula)
    (fragment.links ++ [.par leftEntry.2 rightEntry.2 fragment.formulas.size])
    (contextEntries ++ [(conclusionFormula, fragment.formulas.size)])
  have sizeEq := matched.size_eq
  have rootLookup : (numbering ++ [conclusion])[fragment.formulas.size]? = some conclusion := by
    rw [← sizeEq]
    exact List.getElem?_concat_length
  refine ⟨output, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [CutFreeDerivation.build?, built, leftPickEntries, rightPickEntries, output,
      conclusionFormula]
  · simp [output, NetFragment.ofEntries, matched.size_eq]
  · exact (matched.owned_perm.append_right [conclusion]).trans List.perm_append_comm
  · intro i bound
    change certificate.formula? ((numbering ++ [conclusion])[i]?.getD 0) =
      (fragment.formulas.push conclusionFormula)[i]?
    have bound' : i < fragment.formulas.size + 1 := by
      simpa [output, NetFragment.ofEntries] using bound
    by_cases lt : i < fragment.formulas.size
    · rw [List.getElem?_append_left (by omega), Array.getElem?_push_lt lt,
        ← Array.getElem?_eq_getElem lt]
      exact matched.labels_eq i lt
    · have eq : i = fragment.formulas.size := by omega
      subst eq
      rw [rootLookup, Array.getElem?_push_size]
      exact conclusionLabel
  · change ((contextEntries ++ [(conclusionFormula, fragment.formulas.size)]).map Prod.snd).map
      (fun i ↦ (numbering ++ [conclusion])[i]?.getD 0) = context ++ [conclusion]
    rw [List.map_append, List.map_append]
    congr 1
    · rw [List.map_map, ← contextEq]
      apply List.map_congr_left
      intro entry member
      have bound := (entry_label built matched (contextSub entry member)).1
      simp [List.getElem?_append_left bound, project]
    · simp [rootLookup]
  · change ((fragment.links ++ [Link.par leftEntry.2 rightEntry.2 fragment.formulas.size]).map
      (relabelLink (numbering ++ [conclusion]))).Perm
      ((index :: used).filterMap fun i ↦ certificate.links[i]?)
    rw [List.map_append, List.filterMap_cons_some lookup]
    have oldLinks : fragment.links.map (relabelLink (numbering ++ [conclusion])) =
        fragment.links.map (relabelLink numbering) := by
      apply List.map_congr_left
      intro link member
      exact relabelLink_append fun vertex mem ↦
        matched.size_eq ▸ built_link_bounded built member vertex mem
    have newLink : [Link.par leftEntry.2 rightEntry.2 fragment.formulas.size].map
        (relabelLink (numbering ++ [conclusion])) = [.par left right conclusion] := by
      simp [relabelLink, List.getElem?_append_left leftBound,
        List.getElem?_append_left rightBound, leftProj, rightProj, rootLookup]
    rw [oldLinks, newLink]
    exact (matched.links_perm.append_right _).trans List.perm_append_comm

/-- The tensor build concatenates the left and right numberings, shifting the
right fragment's fresh vertices, and appends the submitted conclusion. -/
theorem occurrenceBuild_tensor_eq {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {leftTree rightTree : CutFreeDerivation} {leftFragment rightFragment : NetFragment}
    {leftFrontier leftUsed leftOwned leftNumbering : List Nat}
    {rightFrontier rightUsed rightOwned rightNumbering : List Nat}
    (leftBuilt : leftTree.build? = some leftFragment)
    (leftMatched : OccurrenceBuildMatch certificate leftFragment
      leftFrontier leftUsed leftOwned leftNumbering)
    (rightBuilt : rightTree.build? = some rightFragment)
    (rightMatched : OccurrenceBuildMatch certificate rightFragment
      rightFrontier rightUsed rightOwned rightNumbering)
    {index left right conclusion leftFocus rightFocus : Nat}
    {leftContext rightContext : List Nat}
    (lookup : certificate.links[index]? = some (.tensor left right conclusion))
    (leftPick : CutFreeDerivation.pick? leftFrontier leftFocus = some (left, leftContext))
    (rightPick : CutFreeDerivation.pick? rightFrontier rightFocus = some (right, rightContext)) :
    ∃ output,
      (CutFreeDerivation.tensor leftFocus rightFocus leftTree rightTree).build? = some output ∧
      OccurrenceBuildMatch certificate output (conclusion :: (leftContext ++ rightContext))
        (index :: (leftUsed ++ rightUsed)) (conclusion :: (leftOwned ++ rightOwned))
        (leftNumbering ++ rightNumbering ++ [conclusion]) := by
  let leftProject := fun entry : Formula × Vertex ↦ leftNumbering[entry.2]?.getD 0
  let rightProject := fun entry : Formula × Vertex ↦ rightNumbering[entry.2]?.getD 0
  have leftEntriesEq : leftFragment.entries.map leftProject = leftFrontier := by
    rw [← leftMatched.roots_eq,
      ← leftFragment.entries_map_snd (CutFreeDerivation.build?_balanced leftBuilt)]
    simp [List.map_map, leftProject]
  have rightEntriesEq : rightFragment.entries.map rightProject = rightFrontier := by
    rw [← rightMatched.roots_eq,
      ← rightFragment.entries_map_snd (CutFreeDerivation.build?_balanced rightBuilt)]
    simp [List.map_map, rightProject]
  obtain ⟨leftEntry, leftRemaining, leftPickEntries, leftProj, leftRemainingEq⟩ :=
    CutFreeDerivation.pick?_exists_of_map_eq_some leftProject (by rwa [leftEntriesEq])
  obtain ⟨rightEntry, rightRemaining, rightPickEntries, rightProj, rightRemainingEq⟩ :=
    CutFreeDerivation.pick?_exists_of_map_eq_some rightProject (by rwa [rightEntriesEq])
  simp only [leftProject] at leftProj
  simp only [rightProject] at rightProj
  have leftSub : ∀ entry ∈ leftRemaining, entry ∈ leftFragment.entries := fun entry mem ↦
    (CutFreeDerivation.pick?_perm leftPickEntries).mem_iff.mpr (by simp [mem])
  have rightSub : ∀ entry ∈ rightRemaining, entry ∈ rightFragment.entries := fun entry mem ↦
    (CutFreeDerivation.pick?_perm rightPickEntries).mem_iff.mpr (by simp [mem])
  have leftMem : leftEntry ∈ leftFragment.entries :=
    (CutFreeDerivation.pick?_perm leftPickEntries).mem_iff.mpr (by simp)
  have rightMem : rightEntry ∈ rightFragment.entries :=
    (CutFreeDerivation.pick?_perm rightPickEntries).mem_iff.mpr (by simp)
  obtain ⟨leftBound, leftLabel⟩ := entry_label leftBuilt leftMatched leftMem
  obtain ⟨rightBound, rightLabel⟩ := entry_label rightBuilt rightMatched rightMem
  rw [leftProj] at leftLabel
  rw [rightProj] at rightLabel
  have wf := structural.2.2.2.2.1 _ (List.mem_of_getElem? lookup)
  have conclusionLabel :
      certificate.formula? conclusion = some (.tensor leftEntry.1 rightEntry.1) := by
    have typing := wf.2.2.2.2.2.2
    rw [leftLabel, rightLabel] at typing
    cases conclusionEq : certificate.formula? conclusion with
    | none => simp [conclusionEq] at typing
    | some formula =>
        simp [conclusionEq] at typing
        simp [typing]
  have leftSizeEq := leftMatched.size_eq
  have rightSizeEq := rightMatched.size_eq
  let conclusionFormula : Formula := .tensor leftEntry.1 rightEntry.1
  let combined := leftFragment.formulas ++ rightFragment.formulas
  let output : NetFragment := NetFragment.ofEntries (combined.push conclusionFormula)
    (leftFragment.links ++ rightFragment.links.map (·.shift leftFragment.formulas.size) ++
      [.tensor leftEntry.2 (rightEntry.2 + leftFragment.formulas.size) combined.size])
    ((conclusionFormula, combined.size) ::
      (leftRemaining ++
        rightRemaining.map (CutFreeDerivation.shiftEntry leftFragment.formulas.size)))
  have combinedSize :
      combined.size = leftFragment.formulas.size + rightFragment.formulas.size :=
    Array.size_append
  have pairLength : (leftNumbering ++ rightNumbering).length = combined.size := by
    simp [combinedSize, leftSizeEq, rightSizeEq]
  have rootLookup :
      (leftNumbering ++ (rightNumbering ++ [conclusion]))[combined.size]? = some conclusion := by
    rw [← List.append_assoc, ← pairLength]
    exact List.getElem?_concat_length
  have leftLookup : ∀ vertex, vertex < leftNumbering.length →
      (leftNumbering ++ (rightNumbering ++ [conclusion]))[vertex]? = leftNumbering[vertex]? :=
    fun _ bound ↦ List.getElem?_append_left bound
  have rightLookup : ∀ vertex, vertex < rightNumbering.length →
      (leftNumbering ++ (rightNumbering ++ [conclusion]))[vertex + leftFragment.formulas.size]? =
        rightNumbering[vertex]? := by
    intro vertex bound
    rw [← leftSizeEq]
    exact getElem?_append_shift bound
  refine ⟨output, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [CutFreeDerivation.build?, leftBuilt, rightBuilt, leftPickEntries, rightPickEntries,
      output, conclusionFormula, combined]
  · simp [output, NetFragment.ofEntries, combined, leftSizeEq, rightSizeEq]
  · exact ((leftMatched.owned_perm.append rightMatched.owned_perm).append_right
      [conclusion]).trans List.perm_append_comm
  · intro i bound
    rw [List.append_assoc]
    change certificate.formula? ((leftNumbering ++ (rightNumbering ++ [conclusion]))[i]?.getD 0) =
      (combined.push conclusionFormula)[i]?
    have bound' : i < combined.size + 1 := by
      simpa [output, NetFragment.ofEntries] using bound
    by_cases lt : i < combined.size
    · rw [Array.getElem?_push_lt lt, ← Array.getElem?_eq_getElem lt]
      by_cases leftCase : i < leftFragment.formulas.size
      · rw [leftLookup i (by omega), Array.getElem?_append_left leftCase]
        exact leftMatched.labels_eq i leftCase
      · have shifted :
            i = (i - leftFragment.formulas.size) + leftFragment.formulas.size := by omega
        rw [shifted, rightLookup _ (by omega), Array.getElem?_append_right (by omega),
          Nat.add_sub_cancel]
        exact rightMatched.labels_eq _ (by omega)
    · have eq : i = combined.size := by omega
      subst eq
      rw [rootLookup, Array.getElem?_push_size]
      exact conclusionLabel
  · change ((combined.size :: (leftRemaining ++
        rightRemaining.map (CutFreeDerivation.shiftEntry leftFragment.formulas.size)).map
          Prod.snd).map
      (fun i ↦ (leftNumbering ++ rightNumbering ++ [conclusion])[i]?.getD 0)) =
      conclusion :: (leftContext ++ rightContext)
    simp only [List.map_cons, List.map_append, List.map_map, List.append_assoc]
    congr 1
    · simp [rootLookup]
    congr 1
    · rw [← leftRemainingEq]
      apply List.map_congr_left
      intro entry member
      have bound := (entry_label leftBuilt leftMatched (leftSub entry member)).1
      simp [Function.comp, leftLookup _ bound, leftProject]
    · rw [← rightRemainingEq]
      apply List.map_congr_left
      intro entry member
      have bound := (entry_label rightBuilt rightMatched (rightSub entry member)).1
      simp [Function.comp, CutFreeDerivation.shiftEntry, rightLookup _ bound, rightProject]
  · change ((leftFragment.links ++
        rightFragment.links.map (·.shift leftFragment.formulas.size) ++
        [Link.tensor leftEntry.2 (rightEntry.2 + leftFragment.formulas.size) combined.size]).map
      (relabelLink (leftNumbering ++ rightNumbering ++ [conclusion]))).Perm
      ((index :: (leftUsed ++ rightUsed)).filterMap fun i ↦ certificate.links[i]?)
    rw [List.map_append, List.map_append, List.map_map, List.filterMap_cons_some lookup,
      List.filterMap_append]
    have leftLinks : leftFragment.links.map
        (relabelLink (leftNumbering ++ rightNumbering ++ [conclusion])) =
        leftFragment.links.map (relabelLink leftNumbering) := by
      apply List.map_congr_left
      intro link member
      rw [List.append_assoc]
      exact relabelLink_append fun vertex mem ↦
        leftSizeEq ▸ built_link_bounded leftBuilt member vertex mem
    have rightLinks : rightFragment.links.map
        (relabelLink (leftNumbering ++ rightNumbering ++ [conclusion]) ∘
          (·.shift leftFragment.formulas.size)) =
        rightFragment.links.map (relabelLink rightNumbering) := by
      apply List.map_congr_left
      intro link member
      simp only [Function.comp]
      rw [List.append_assoc, ← leftSizeEq]
      exact relabelLink_shift fun vertex mem ↦
        rightSizeEq ▸ built_link_bounded rightBuilt member vertex mem
    have newLink : [Link.tensor leftEntry.2 (rightEntry.2 + leftFragment.formulas.size)
        combined.size].map (relabelLink (leftNumbering ++ rightNumbering ++ [conclusion])) =
        [.tensor left right conclusion] := by
      simp [relabelLink, leftLookup _ leftBound, rightLookup _ rightBound, leftProj, rightProj,
        rootLookup]
    rw [leftLinks, rightLinks, newLink]
    exact ((leftMatched.links_perm.append rightMatched.links_perm).append_right _).trans
      List.perm_append_comm

/-- Every occurrence derivation of a structurally well-formed certificate builds,
with its fresh vertices numbered exactly by the submitted occurrences. -/
theorem occurrenceBuild_exists {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {tree : CutFreeDerivation}
    {frontier used owned : List Nat}
    (witness : certificate.OccurrenceDerivation tree frontier used owned) :
    ∃ fragment numbering, tree.build? = some fragment ∧
      OccurrenceBuildMatch certificate fragment frontier used owned numbering := by
  induction witness with
  | «axiom» index left right name positive lookup label =>
      obtain ⟨fragment, built, matched⟩ := occurrenceBuild_axiom_eq structural lookup label
      exact ⟨fragment, _, built, matched⟩
  | par _ index left right conclusion leftFocus rightFocus afterLeft context lookup
      leftPick rightPick ih =>
      obtain ⟨fragment, numbering, built, matched⟩ := ih
      obtain ⟨output, builtOut, matchedOut⟩ := occurrenceBuild_par_eq structural built matched
        lookup leftPick.positional rightPick.positional
      exact ⟨output, _, builtOut, matchedOut⟩
  | tensor _ _ index left right conclusion leftFocus rightFocus leftContext rightContext
      lookup leftPick rightPick leftIH rightIH =>
      obtain ⟨leftFragment, leftNumbering, leftBuilt, leftMatched⟩ := leftIH
      obtain ⟨rightFragment, rightNumbering, rightBuilt, rightMatched⟩ := rightIH
      obtain ⟨output, builtOut, matchedOut⟩ := occurrenceBuild_tensor_eq structural leftBuilt
        leftMatched rightBuilt rightMatched lookup leftPick.positional rightPick.positional
      exact ⟨output, _, builtOut, matchedOut⟩
  | exchange _ order reordered reorderEq ih =>
      obtain ⟨fragment, numbering, built, matched⟩ := ih
      obtain ⟨output, builtOut, matchedOut⟩ := occurrenceBuild_exchange_eq built matched reorderEq
      exact ⟨output, _, builtOut, matchedOut⟩


/-- Two submitted axiom links sharing an endpoint are the same link. -/
private theorem axiom_link_unique {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {firstLeft firstRight secondLeft secondRight vertex : Vertex}
    (first : Link.axiom firstLeft firstRight ∈ certificate.links)
    (firstEndpoint : vertex = firstLeft ∨ vertex = firstRight)
    (second : Link.axiom secondLeft secondRight ∈ certificate.links)
    (secondEndpoint : vertex = secondLeft ∨ vertex = secondRight) :
    Link.axiom firstLeft firstRight = Link.axiom secondLeft secondRight := by
  have wf := structural.2.2.2.2.1 _ first
  obtain ⟨name, positive, lookup⟩ := wf.axiom_endpointFormula firstEndpoint
  have bound : vertex < certificate.formulas.size := by
    rcases firstEndpoint with rfl | rfl
    · exact wf.2.1
    · exact wf.2.2.1
  have count : certificate.axiomCount vertex = 1 := by
    simpa [NodeWellFormed, lookup] using (structural.2.2.2.2.2 vertex bound).1
  unfold axiomCount at count
  obtain ⟨link, eq⟩ := List.length_eq_one_iff.mp count
  have firstIn : Link.axiom firstLeft firstRight ∈
      certificate.links.filter (·.containsAxiomEndpoint vertex) :=
    List.mem_filter.mpr ⟨first, by rcases firstEndpoint with rfl | rfl <;>
      simp [Link.containsAxiomEndpoint]⟩
  have secondIn : Link.axiom secondLeft secondRight ∈
      certificate.links.filter (·.containsAxiomEndpoint vertex) :=
    List.mem_filter.mpr ⟨second, by rcases secondEndpoint with rfl | rfl <;>
      simp [Link.containsAxiomEndpoint]⟩
  rw [eq] at firstIn secondIn
  simp only [List.mem_singleton] at firstIn secondIn
  rw [firstIn, secondIn]

/-- An owned axiom endpoint's submitted axiom is a used link. -/
private theorem owned_axiom_used {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {tree : CutFreeDerivation}
    {frontier used owned : List Nat}
    (witness : certificate.OccurrenceDerivation tree frontier used owned)
    {vertex : Vertex} (member : vertex ∈ owned) {left right : Vertex}
    (submitted : Link.axiom left right ∈ certificate.links)
    (endpoint : vertex = left ∨ vertex = right) :
    ∃ index ∈ used, certificate.links[index]? = some (.axiom left right) := by
  induction witness with
  | «axiom» index l r name positive lookup formula =>
      have stored : vertex = l ∨ vertex = r := by simpa using member
      have eq := axiom_link_unique structural (List.mem_of_getElem? lookup) stored submitted
        endpoint
      exact ⟨index, by simp, lookup.trans (congrArg some eq)⟩
  | par _ index l r conclusion lf rf afterLeft context lookup lp rp ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact (structural.axiomEndpoint_ne_connectiveConclusion submitted endpoint
          (List.mem_of_getElem? lookup) (by simp [Link.produces])).elim
      · obtain ⟨i, mem, eq⟩ := ih member
        exact ⟨i, by simp [mem], eq⟩
  | tensor _ _ index l r conclusion lf rf lc rc lookup lp rp lih rih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact (structural.axiomEndpoint_ne_connectiveConclusion submitted endpoint
          (List.mem_of_getElem? lookup) (by simp [Link.produces])).elim
      · rcases List.mem_append.mp member with lm | rm
        · obtain ⟨i, mem, eq⟩ := lih lm
          exact ⟨i, by simp [mem], eq⟩
        · obtain ⟨i, mem, eq⟩ := rih rm
          exact ⟨i, by simp [mem], eq⟩
  | exchange _ order reordered equation ih => exact ih member

private theorem filterMap_getElem?_range {α : Type} (values : List α) :
    (List.range values.length).filterMap (fun index ↦ values[index]?) = values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp [List.range_succ_eq_map, List.filterMap_map, Function.comp_def, ih]

/-- A linear derivation covering the carrier uses every submitted link exactly
once, so its used links enumerate the input link list. -/
private theorem usedLinks_perm {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {tree : CutFreeDerivation}
    {frontier used owned : List Nat}
    (witness : certificate.OccurrenceDerivation tree frontier used owned)
    (usedNodup : used.Nodup)
    (covers : ∀ vertex, vertex ∈ owned ↔ vertex < certificate.formulas.size) :
    (used.filterMap fun index ↦ certificate.links[index]?).Perm certificate.links := by
  have range : used.Perm (List.range certificate.links.length) := by
    apply List.perm_iff_count.mpr
    intro index
    have iff : index ∈ used ↔ index < certificate.links.length := by
      refine ⟨witness.usedLinkIndex_lt, fun bound ↦ ?_⟩
      have lookup : certificate.links[index]? = some certificate.links[index] :=
        List.getElem?_eq_getElem bound
      have submitted := List.mem_of_getElem? lookup
      have wf := structural.2.2.2.2.1 _ submitted
      obtain ⟨j, memJ, lookupJ⟩ : ∃ j ∈ used,
          certificate.links[j]? = some certificate.links[index] := by
        cases linkEq : certificate.links[index] with
        | «axiom» left right =>
            rw [linkEq] at wf submitted
            exact owned_axiom_used structural witness ((covers left).mpr wf.2.1) submitted
              (.inl rfl)
        | tensor left right conclusion =>
            rw [linkEq] at wf submitted
            exact owned_producer_used structural witness
              ((covers conclusion).mpr wf.2.2.2.2.2.1) submitted (by simp [Link.produces])
        | par left right conclusion =>
            rw [linkEq] at wf submitted
            exact owned_producer_used structural witness
              ((covers conclusion).mpr wf.2.2.2.2.2.1) submitted (by simp [Link.produces])
      have eq : j = index := (List.getElem?_inj (witness.usedLinkIndex_lt memJ)
        structural.links_nodup).mp (lookupJ.trans lookup.symm)
      exact eq ▸ memJ
    simp only [usedNodup.count, List.nodup_range.count, List.mem_range, iff]
  exact (range.filterMap _).trans (by rw [filterMap_getElem?_range])

/-- The bounded vertex renaming induced by a duplicate-free numbering that
enumerates exactly the carrier below `bound`. -/
private def numberingRenaming (numbering : List Nat) (bound : Nat)
    (size : numbering.length = bound) (nodup : numbering.Nodup)
    (covers : ∀ vertex, vertex ∈ numbering ↔ vertex < bound) : VertexRenaming bound where
  forward vertex := if h : vertex < numbering.length then numbering[vertex] else vertex
  inverse vertex := (numbering.idxOf? vertex).getD vertex
  inverse_forward := by
    intro vertex
    by_cases h : vertex < numbering.length
    · simp only [dif_pos h]
      have mem : numbering[vertex] ∈ numbering := List.getElem_mem h
      obtain ⟨j, found⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr mem)
      obtain ⟨_, jEq, _⟩ := List.idxOf?_eq_some_iff.mp found
      rw [found, Option.getD_some]
      exact (List.getElem_inj nodup).mp jEq
    · simp only [dif_neg h]
      have notMem : vertex ∉ numbering := fun mem ↦ h (size ▸ (covers vertex).mp mem)
      rw [List.idxOf?_eq_none_iff.mpr notMem, Option.getD_none]
  forward_inverse := by
    intro vertex
    by_cases mem : vertex ∈ numbering
    · obtain ⟨j, found⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr mem)
      obtain ⟨jBound, jEq, _⟩ := List.idxOf?_eq_some_iff.mp found
      simp only [found, Option.getD_some, dif_pos jBound]
      exact jEq
    · rw [List.idxOf?_eq_none_iff.mpr mem, Option.getD_none]
      have notLt : ¬ vertex < numbering.length := fun h ↦ mem ((covers vertex).mpr (size ▸ h))
      simp only [dif_neg notLt]
  forward_lt_iff := by
    intro vertex
    by_cases h : vertex < numbering.length
    · simp only [dif_pos h]
      exact ⟨fun _ ↦ size ▸ h, fun _ ↦ (covers _).mp (List.getElem_mem h)⟩
    · simp only [dif_neg h]

private theorem numberingRenaming_forward {numbering : List Nat} {bound : Nat}
    {size : numbering.length = bound} {nodup : numbering.Nodup}
    {covers : ∀ vertex, vertex ∈ numbering ↔ vertex < bound} {vertex : Nat}
    (h : vertex < numbering.length) :
    (numberingRenaming numbering bound size nodup covers).forward vertex =
      numbering[vertex]?.getD 0 := by
  simp [numberingRenaming, dif_pos h, List.getElem?_eq_getElem h]

private theorem numberingRenaming_inverse {numbering : List Nat} {bound : Nat}
    {size : numbering.length = bound} {nodup : numbering.Nodup}
    {covers : ∀ vertex, vertex ∈ numbering ↔ vertex < bound} {vertex : Nat}
    (mem : vertex ∈ numbering) :
    ∃ index, index < numbering.length ∧ numbering[index]?.getD 0 = vertex ∧
      (numberingRenaming numbering bound size nodup covers).inverse vertex = index := by
  obtain ⟨index, found⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr mem)
  obtain ⟨bound', eq, _⟩ := List.idxOf?_eq_some_iff.mp found
  refine ⟨index, bound', by rw [List.getElem?_eq_getElem bound', Option.getD_some, eq], ?_⟩
  simp [numberingRenaming, found]

/-- Reindexing an in-bounds link by the numbering renaming is relabelling. -/
private theorem reindex_eq_relabelLink {numbering : List Nat} {bound : Nat}
    {size : numbering.length = bound} {nodup : numbering.Nodup}
    {covers : ∀ vertex, vertex ∈ numbering ↔ vertex < bound} {link : Link}
    (bounded : ∀ vertex ∈ link.vertices, vertex < numbering.length) :
    link.reindex (numberingRenaming numbering bound size nodup covers) =
      relabelLink numbering link := by
  cases link with
  | «axiom» left right =>
      simp only [Link.vertices, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at bounded
      simp [Link.reindex, relabelLink, numberingRenaming_forward bounded.1,
        numberingRenaming_forward bounded.2]
  | tensor left right conclusion | par left right conclusion =>
      simp only [Link.vertices, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at bounded
      simp [Link.reindex, relabelLink, numberingRenaming_forward bounded.1,
        numberingRenaming_forward bounded.2.1, numberingRenaming_forward bounded.2.2]

/-- The desequentialization of a linear occurrence derivation that covers the
carrier and exposes the input conclusions is proof-net equivalent to the input. -/
theorem occurrenceBuild_equivalent {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {tree : CutFreeDerivation}
    {used owned : List Nat}
    (witness : certificate.OccurrenceDerivation tree certificate.conclusions used owned)
    (usedNodup : used.Nodup) (ownedNodup : owned.Nodup)
    (covers : ∀ vertex, vertex ∈ owned ↔ vertex < certificate.formulas.size) :
    ∃ output, tree.desequentialize? = some output ∧ output.ProofNetEquivalent certificate := by
  obtain ⟨fragment, numbering, built, matched⟩ := occurrenceBuild_exists structural witness
  have ownedRange : owned.Perm (List.range certificate.formulas.size) := by
    apply List.perm_iff_count.mpr
    intro vertex
    simp only [ownedNodup.count, List.nodup_range.count, List.mem_range, covers]
  have sizesEq : certificate.formulas.size = fragment.formulas.size := by
    rw [← matched.size_eq, matched.owned_perm.length_eq, ownedRange.length_eq, List.length_range]
  have numberingNodup : numbering.Nodup := ownedNodup.perm matched.owned_perm.symm
  have numberingCovers : ∀ vertex, vertex ∈ numbering ↔ vertex < fragment.formulas.size := by
    intro vertex
    rw [matched.owned_perm.mem_iff, covers, sizesEq]
  let vertexMap := numberingRenaming numbering fragment.formulas.size matched.size_eq
    numberingNodup numberingCovers
  have sizeEq := matched.size_eq
  refine ⟨fragment.toCertificate, by simp [CutFreeDerivation.desequentialize?, built], ?_⟩
  apply DirectProofNetEquivalent.toProofNetEquivalent
  refine ⟨vertexMap, ?_, ?_, ?_⟩
  · apply Array.ext
    · simp [Certificate.reindex, NetFragment.toCertificate, sizesEq]
    · intro i bound₁ bound₂
      have mem : i ∈ numbering := (numberingCovers i).mpr (sizesEq ▸ bound₂)
      obtain ⟨j, jBound, jEq, inverseEq⟩ := numberingRenaming_inverse
        (size := matched.size_eq) (nodup := numberingNodup) (covers := numberingCovers) mem
      simp only [Certificate.reindex, Array.getElem_ofFn]
      have inverseBound : vertexMap.inverse i < fragment.toCertificate.formulas.size :=
        (vertexMap.inverse_lt_iff i).mpr (sizesEq ▸ bound₂)
      apply Option.some.inj
      rw [← Array.getElem?_eq_getElem inverseBound, ← Array.getElem?_eq_getElem bound₂]
      change fragment.formulas[vertexMap.inverse i]? = certificate.formulas[i]?
      rw [inverseEq, ← matched.labels_eq j (sizeEq ▸ jBound), jEq]
      rfl
  · change (fragment.links.map (Link.reindex vertexMap)).Perm certificate.links
    have linksEq : fragment.links.map (Link.reindex vertexMap) =
        fragment.links.map (relabelLink numbering) := by
      apply List.map_congr_left
      intro link member
      exact reindex_eq_relabelLink fun vertex mem ↦
        sizeEq ▸ built_link_bounded built member vertex mem
    rw [linksEq]
    exact matched.links_perm.trans (usedLinks_perm structural witness usedNodup covers)
  · change fragment.roots.map vertexMap.forward = certificate.conclusions
    rw [← matched.roots_eq]
    apply List.map_congr_left
    intro root member
    have rootsEq := fragment.entries_map_snd (CutFreeDerivation.build?_balanced built)
    rw [← rootsEq] at member
    obtain ⟨entry, entryMember, entryEq⟩ := List.mem_map.mp member
    subst entryEq
    exact numberingRenaming_forward (entry_label built matched entryMember).1

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

/-- Every certificate accepted by the reference checker is accepted by the
sequential fast path: initialization succeeds at the first conclusion, the
bounded run marks every occurrence, and the exchanged final derivation is
verified through the proof-net equivalence of its desequentialization. -/
theorem sequentialFastCheck_complete (certificate : Certificate)
    (accepted : certificate.check = true) : certificate.sequentialFastCheck = true := by
  have correct := certificate.check_iff_declarativelyCorrect.mp accepted
  have structural := correct.1
  have wellFormed : certificate.wellFormed = true :=
    certificate.wellFormed_iff_structurallyWellFormed.mpr structural
  obtain ⟨start, headEq, startMember⟩ : ∃ start, certificate.conclusions.head? = some start ∧
      start ∈ certificate.conclusions := by
    cases conclusionsEq : certificate.conclusions with
    | nil => exact absurd structural.2.1 (by simp [conclusionsEq])
    | cons first rest => exact ⟨first, rfl, by simp⟩
  obtain ⟨state, initEq⟩ :=
    structural.initializeReservation?_isSome (structural.2.2.1 start startMember)
  obtain ⟨step⟩ := initializeReservation?_some_iff.mp initEq
  have started : 0 < state.stack.nextAge := by
    have nextAgeEq :=
      (SequentialSchedulerState.SequentialStackState.initEnqueue?_exact step.stack_eq).2.1
    rw [step.output_eq]
    change 0 < step.stackAfter.nextAge
    rw [nextAgeEq]
    exact Nat.one_pos
  have reachable : ReachableByImplementedDispatcher certificate state := ⟨.init step⟩
  have invariant := initializeReservation?_schedulerInvariant structural initEq
  obtain ⟨finalReachable, _, _, marked⟩ := runDispatcher_spec invariant reachable correct started
  obtain ⟨component, order, used, owned, _, witness, covers, _, _, reorder, finalEq⟩ :=
    sequentialFinalTree?_eq_some finalReachable correct marked
  have derivation := witness.derivation.exchange order certificate.conclusions reorder
  obtain ⟨sequent, inferred, labels⟩ := derivation.formulaConsistent structural
  obtain ⟨output, built, equivalent⟩ := occurrenceBuild_equivalent structural derivation
    witness.usedLinks_nodup witness.owned_nodup covers
  obtain ⟨result, verified⟩ := verifyDerivation?_complete structural labels inferred built equivalent
  unfold sequentialFastCheck sequentialReconstruct?
  rw [dif_pos wellFormed]
  simp only [headEq, Option.bind_eq_bind, Option.bind_some]
  split
  · rename_i none
    rw [initEq] at none
    cases none
  · rename_i state' someEq
    obtain rfl : state = state' := Option.some.inj (initEq.symm.trans someEq)
    rw [finalEq, Option.bind_some, verified]
    rfl

/-- The sequential fast path decides exactly the reference checker. -/
theorem sequentialFastCheck_eq_check (certificate : Certificate) :
    certificate.sequentialFastCheck = certificate.check := by
  cases accepted : certificate.check with
  | true => exact certificate.sequentialFastCheck_complete accepted
  | false =>
      cases fast : certificate.sequentialFastCheck with
      | true => exact absurd (certificate.sequentialFastCheck_sound fast) (by simp [accepted])
      | false => rfl

/-- The exact public decision: the sequential Figures 7–8 fast path alone,
with no switching enumeration and no recursive reconstruction fallback. -/
def unificationCheck (certificate : Certificate) : Bool :=
  certificate.sequentialFastCheck

/-- The public decision is the sequential fast path with no fallback. -/
theorem unificationCheck_eq_sequentialFastCheck (certificate : Certificate) :
    certificate.unificationCheck = certificate.sequentialFastCheck := rfl

/-- The public decision is extensionally equal to the reference
all-switchings checker. -/
theorem unificationCheck_eq_check (certificate : Certificate) :
    certificate.unificationCheck = certificate.check :=
  certificate.sequentialFastCheck_eq_check

/-- Iff form of exact agreement between the public decision and the
reference checker. -/
theorem unificationCheck_eq_true_iff_check (certificate : Certificate) :
    certificate.unificationCheck = true ↔ certificate.check = true := by
  rw [certificate.unificationCheck_eq_check]

/-- Proposition-level correctness interface for the public decision. -/
theorem unificationCheck_eq_true_iff_declarativelyCorrect
    (certificate : Certificate) :
    certificate.unificationCheck = true ↔
      certificate.DeclarativelyCorrect := by
  rw [certificate.unificationCheck_eq_check,
    certificate.check_iff_declarativelyCorrect]

end Certificate
end ProofNetIR
