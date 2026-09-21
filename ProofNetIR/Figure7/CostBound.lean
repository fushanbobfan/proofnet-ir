import ProofNetIR.Figure7.Cost

/-!
# Bounds of the operation counters

The raw occurrence traversal has no duplicates on structurally well-formed
certificates, which bounds canonicalization; live component trees have no
exchange nodes, which bounds inference and desequentialization of the
extracted derivation; the remaining phases are bounded by the carrier. The
whole public decision is quadratic in the carrier, links, and conclusions of
a structurally well-formed certificate, and quadratic in the submitted text
of any certificate.
-/

namespace ProofNetIR
namespace Certificate

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
    (∃ left right, link = .tensor left right vertex) ∨
      ∃ left right, link = .par left right vertex := by
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
    (structural : certificate.StructurallyWellFormed) {link : Link}
    (member : link ∈ certificate.links) {vertex : Vertex} (premise : vertex ∈ link.premises)
    (bound : vertex < certificate.formulas.size) :
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
    (structural : certificate.StructurallyWellFormed) {link : Link}
    (member : link ∈ certificate.links)
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

private theorem Under.trans {certificate : Certificate} {top mid vertex : Vertex}
    (first : Under certificate top mid) (second : Under certificate mid vertex) :
    Under certificate top vertex := by
  induction second with
  | refl => exact first
  | step _ member produces premise_mem ih => exact .step ih member produces premise_mem

private theorem walk_under (certificate : Certificate) (formula : Formula) (top vertex : Vertex)
    (member : vertex ∈ certificate.occurrenceWalk top formula) : Under certificate top vertex := by
  induction formula generalizing top with
  | atom _ _ =>
      simp only [occurrenceWalk, List.mem_singleton] at member
      subst vertex
      exact .refl
  | tensor lf rf lih rih | par lf rf lih rih =>
      unfold occurrenceWalk at member
      split at member
      all_goals first
        | (rename_i left right conclusion selected
           have found := List.mem_filter.mp (ExactOne.mem_of_select?_eq_some selected)
           simp only [List.mem_cons, List.mem_append] at member
           rcases member with rfl | inLeft | inRight
           · exact .refl
           · exact Under.trans (.step .refl found.1 found.2 (by simp [Link.premises]))
               (lih left inLeft)
           · exact Under.trans (.step .refl found.1 found.2 (by simp [Link.premises]))
               (rih right inRight))
        | (simp only [List.mem_singleton] at member
           subst vertex
           exact .refl)

private theorem walk_nodup {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) (formula : Formula) {top : Vertex}
    (bound : top < certificate.formulas.size)
    (formulaAt : certificate.formula? top = some formula) :
    (certificate.occurrenceWalk top formula).Nodup := by
  induction formula generalizing top with
  | atom _ _ => simp [occurrenceWalk]
  | tensor lf rf lih rih | par lf rf lih rih =>
      obtain ⟨left, right, selected, leftAt, rightAt⟩ :=
        (by first | exact structural.uniqueTensorProducerData bound formulaAt
                  | exact structural.uniqueParProducerData bound formulaAt)
      have found := List.mem_filter.mp (ExactOne.mem_of_select?_eq_some selected)
      have wf := structural.2.2.2.2.1 _ found.1
      have leftLt := premise_lt structural found.1 found.2 (by simp [Link.premises] : left ∈ _)
      have rightLt := premise_lt structural found.1 found.2 (by simp [Link.premises] : right ∈ _)
      rw [occurrenceWalk, selected, List.nodup_cons, List.nodup_append]
      refine ⟨?_, lih (inBounds_of_formula?_eq_some leftAt) leftAt,
        rih (inBounds_of_formula?_eq_some rightAt) rightAt, ?_⟩
      · intro member
        rcases List.mem_append.mp member with inLeft | inRight
        · have := Under.complexity_le structural (walk_under certificate lf left top inLeft)
          omega
        · have := Under.complexity_le structural (walk_under certificate rf right top inRight)
          omega
      · intro a aMem b bMem same
        subst b
        exact under_disjoint structural found.1 found.2 (by simp [Link.premises])
          (by simp [Link.premises]) wf.1
          (walk_under certificate lf left a aMem) (walk_under certificate rf right a bMem)

private theorem under_conclusions_eq {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {left right vertex : Vertex}
    (leftMem : left ∈ certificate.conclusions) (rightMem : right ∈ certificate.conclusions)
    (underLeft : Under certificate left vertex) (underRight : Under certificate right vertex) :
    left = right := by
  induction underLeft with
  | refl =>
      cases underRight with
      | refl => rfl
      | step _ member _ premise =>
          exact False.elim (premise_not_conclusion structural member premise
            (structural.2.2.1 _ leftMem) leftMem)
  | step _ member produces premise ih =>
      cases underRight with
      | refl =>
          exact False.elim (premise_not_conclusion structural member premise
            (structural.2.2.1 _ rightMem) rightMem)
      | step underRight' member' produces' premise' =>
          have same := premise_unique structural member member' premise premise'
            (premise_bound structural member premise)
          subst same
          have sameTop := produces_unique produces produces'
          subst sameTop
          exact ih underRight'

/-- The raw preorder walks from the conclusions visit no occurrence twice. -/
theorem StructurallyWellFormed.intrinsicTraversalRaw_nodup {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) :
    certificate.intrinsicTraversalRaw.Nodup := by
  have conclusionsNodup := CutFreeDerivation.nodup_of_eraseDups_length_eq structural.2.2.2.1
  have walkSpec : ∀ root ∈ certificate.conclusions,
      (certificate.occurrenceWalk? root).Nodup ∧
      ∀ vertex ∈ certificate.occurrenceWalk? root, Under certificate root vertex := by
    intro root rootMem
    have bound := structural.2.2.1 root rootMem
    have atRoot : certificate.formula? root = some certificate.formulas[root] := by
      rw [formula?, Array.getElem?_eq_getElem bound]
    simp only [occurrenceWalk?, atRoot]
    exact ⟨walk_nodup structural _ bound atRoot, fun vertex member ↦ walk_under _ _ _ _ member⟩
  have flatNodup : ∀ roots : List Vertex, roots.Nodup →
      (∀ root ∈ roots, root ∈ certificate.conclusions) →
      (roots.flatMap certificate.occurrenceWalk?).Nodup := by
    intro roots nodup subset
    induction roots with
    | nil => simp
    | cons root roots ih =>
        have rootMem := subset root (by simp)
        have tailSubset : ∀ v ∈ roots, v ∈ certificate.conclusions :=
          fun v member ↦ subset v (by simp [member])
        rw [List.flatMap_cons, List.nodup_append]
        refine ⟨(walkSpec root rootMem).1, ih nodup.tail tailSubset, ?_⟩
        intro a aMem b bMem same
        subst b
        obtain ⟨other, otherMem, inOther⟩ := List.mem_flatMap.mp bMem
        have rootEq := under_conclusions_eq structural rootMem (tailSubset other otherMem)
          ((walkSpec root rootMem).2 a aMem)
          ((walkSpec other (tailSubset other otherMem)).2 a inOther)
        exact (List.nodup_cons.mp nodup).1 (rootEq ▸ otherMem)
  exact flatNodup certificate.conclusions conclusionsNodup (fun _ member ↦ member)

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

/-- The raw canonical traversal length is bounded by the formula carrier. -/
theorem StructurallyWellFormed.raw_length_le {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) :
    certificate.intrinsicTraversalRaw.length ≤ certificate.formulas.size := by
  have complete := structural.intrinsicTraversalComplete.length_eq
  simpa only [intrinsicTraversalVertices,
    eraseDups_eq_of_nodup structural.intrinsicTraversalRaw_nodup] using Nat.le_of_eq complete

private theorem linkVertices_length_le (links : List Link) :
    (links.flatMap Link.vertices).length ≤ 3 * links.length := by
  induction links with
  | nil => simp
  | cons link links ih =>
      cases link <;> simp only [List.flatMap_cons, Link.vertices, List.length_append,
        List.length_cons, List.length_nil] <;> omega

/-- Canonicalization of a well-formed certificate is quadratic. -/
theorem StructurallyWellFormed.canonicalizeCost_le {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) :
    SequentialCost.canonicalizeCost certificate ≤
      8 * (certificate.formulas.size + 1) *
        (certificate.formulas.size + certificate.links.length + 1) := by
  have raw := structural.raw_length_le
  have intrinsic := structural.intrinsicTraversalComplete.length_eq
  have traversal := (certificate.traversalComplete_of_structurallyWellFormed structural).length_eq
  have conclusions := SequentialCost.conclusions_length_le structural
  have vertices := linkVertices_length_le certificate.links
  have combined : (certificate.conclusions ++ certificate.links.flatMap Link.vertices).length ≤
      certificate.formulas.size + 3 * certificate.links.length := by
    simp only [List.length_append]
    omega
  have a := Nat.mul_le_mul_right (certificate.links.length + 1) raw
  have b := Nat.mul_le_mul raw raw
  have c := Nat.mul_le_mul_right (certificate.formulas.size + 1) raw
  have d := Nat.mul_le_mul_right (certificate.formulas.size + 1) combined
  have e := Nat.mul_le_mul_right certificate.formulas.size
    (Nat.add_le_add_left conclusions (3 * certificate.links.length))
  unfold SequentialCost.canonicalizeCost
  rw [intrinsic, traversal]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_one] at a b c d e ⊢
  simp only [Nat.mul_comm certificate.links.length certificate.formulas.size] at d e ⊢
  omega

end Certificate

namespace SequentialCost

open SequentialSchedulerBridge SequentialSchedulerState SequentialFigure7

/-! ## Live component trees have no exchange nodes -/

/-- A derivation built from axiom, tensor, and par nodes only. -/
def ExchangeFree : CutFreeDerivation → Prop
  | .axiom _ _ => True
  | .tensor _ _ leftTree rightTree => ExchangeFree leftTree ∧ ExchangeFree rightTree
  | .par _ _ premise => ExchangeFree premise
  | .exchange _ _ => False

/-- Every live component of the production state has an exchange-free tree. -/
def LiveTreesExchangeFree (core : UnificationState) : Prop :=
  ∀ {index : Nat} {component : UnificationComponent},
    core.components[index]? = some (some component) → ExchangeFree component.tree

private theorem liveTrees_of_components_eq {before after : UnificationState}
    (eq : after.components = before.components) (free : LiveTreesExchangeFree before) :
    LiveTreesExchangeFree after := by
  intro index component lookup
  rw [eq] at lookup
  exact free lookup

private theorem liveTrees_push {before after : UnificationState} {component : UnificationComponent}
    (eq : after.components = before.components.push (some component))
    (free : LiveTreesExchangeFree before) (fresh : ExchangeFree component.tree) :
    LiveTreesExchangeFree after := by
  intro index candidate lookup
  rw [eq, Array.getElem?_push] at lookup
  split at lookup
  · cases lookup
    exact fresh
  · exact free lookup

private theorem liveTrees_set {before after : UnificationState} {token : Nat}
    {cell : Option UnificationComponent}
    (eq : after.components = before.components.setIfInBounds token cell)
    (free : LiveTreesExchangeFree before)
    (fresh : ∀ component, cell = some component → ExchangeFree component.tree) :
    LiveTreesExchangeFree after := by
  intro index candidate lookup
  rw [eq, Array.getElem?_setIfInBounds] at lookup
  split at lookup
  · split at lookup
    · exact fresh candidate (Option.some.inj lookup)
    · cases lookup
  · exact free lookup

private theorem componentAt?_live {core : UnificationState} {token : Nat}
    {component : UnificationComponent} (lookup : core.componentAt? token = some component) :
    core.components[core.representative token]? = some (some component) := by
  unfold UnificationState.componentAt? at lookup
  cases cell : core.components[core.representative token]? with
  | none => simp [cell] at lookup
  | some inner =>
      cases inner with
      | none => simp [cell] at lookup
      | some found =>
          simp [cell] at lookup
          rw [lookup]

/-- A queued par keeps every live tree exchange-free. -/
private theorem queuePar?_liveTreesExchangeFree {before after : UnificationState}
    {left right conclusion : Vertex}
    (equation : Certificate.queuePar? before left right conclusion = some after)
    (free : LiveTreesExchangeFree before) : LiveTreesExchangeFree after := by
  obtain ⟨step⟩ := Certificate.queuePar?_some_iff.mp equation
  refine liveTrees_set (congrArg UnificationState.components step.after_eq) free ?_
  intro component eq
  cases eq
  have inner := free (componentAt?_live step.component_lookup)
  exact inner

/-- A queued tensor keeps every live tree exchange-free. -/
private theorem queueTensor?_liveTreesExchangeFree {before after : UnificationState}
    {left right conclusion : Vertex}
    (equation : Certificate.queueTensor? before left right conclusion = some after)
    (free : LiveTreesExchangeFree before) : LiveTreesExchangeFree after := by
  obtain ⟨step⟩ := Certificate.queueTensor?_some_iff.mp equation
  have leftFree := free (componentAt?_live step.left_component)
  have rightFree := free (componentAt?_live step.right_component)
  intro index candidate lookup
  rw [step.after_eq] at lookup
  simp only [Array.getElem?_setIfInBounds] at lookup
  split at lookup
  · split at lookup
    · cases lookup
    · cases lookup
  · split at lookup
    · split at lookup
      · cases lookup
        exact ⟨leftFree, rightFree⟩
      · cases lookup
    · exact free lookup

/-- Payload activation keeps every live tree exchange-free. -/
private theorem activateWaitingPayload?_liveTreesExchangeFree {certificate : Certificate}
    {before after : UnificationState} {payload : List Vertex}
    (equation : activateWaitingPayload? certificate before payload = some after)
    (free : LiveTreesExchangeFree before) : LiveTreesExchangeFree after := by
  obtain ⟨fold⟩ := activateWaitingPayload?_some_iff.mp equation
  clear equation
  induction fold with
  | nil _ => exact free
  | cons head _ ih => exact ih (queuePar?_liveTreesExchangeFree head.queue_eq free)

/-- An axiom reservation keeps every live tree exchange-free. -/
private theorem reserveAxiomAt?_liveTreesExchangeFree {certificate : Certificate}
    {before after : UnificationState} {linkIndex : Nat}
    (equation : certificate.reserveAxiomAt? before linkIndex = some after)
    (free : LiveTreesExchangeFree before) : LiveTreesExchangeFree after := by
  obtain ⟨left, right, component, _, _, axiomEq, _, _, _, componentsEq, _, _⟩ :=
    Certificate.reserveAxiomAt?_exact equation
  refine liveTrees_push componentsEq free ?_
  unfold Certificate.UnificationComponent.axiom? at axiomEq
  cases formula : certificate.formula? left with
  | none => simp [formula] at axiomEq
  | some value =>
      cases value with
      | atom name positive =>
          simp [formula] at axiomEq
          rw [← axiomEq]
          trivial
      | tensor _ _ => simp [formula] at axiomEq
      | par _ _ => simp [formula] at axiomEq

/-- A raw mark keeps every live tree exchange-free. -/
private theorem markReadyRaw?_liveTreesExchangeFree {before after : UnificationState}
    {vertex : Vertex} {rawAge : RawTokenAge}
    (equation : before.markReadyRaw? vertex rawAge = .ok after)
    (free : LiveTreesExchangeFree before) : LiveTreesExchangeFree after :=
  liveTrees_of_components_eq (UnificationState.markReadyRaw?_exact equation).2.2.2.1 free

/-- Every dispatcher-reachable state has exchange-free live trees. -/
theorem ExecutedHistory.liveTreesExchangeFree {certificate : Certificate}
    {state : ReservationState} (history : ExecutedHistory certificate state) :
    LiveTreesExchangeFree state.core := by
  induction history with
  | empty =>
      intro index component lookup
      simp [ReservationState.empty, Certificate.initialUnificationState] at lookup
  | init step =>
      rw [step.output_eq]
      exact reserveAxiomAt?_liveTreesExchangeFree step.core_eq
        (fun lookup ↦ by simp [ReservationState.empty, Certificate.initialUnificationState] at lookup)
  | later _ invariant step ih =>
      cases step with
      | concl conclEq =>
          obtain ⟨rule⟩ := (concl?_some_iff invariant.toReservationInvariant).mp conclEq
          rw [rule.output_eq]
          exact markReadyRaw?_liveTreesExchangeFree rule.prepared.core_mark_eq ih
      | nop _ nopEq =>
          obtain ⟨rule⟩ := (nop?_some_iff invariant.toReservationInvariant).mp nopEq
          rw [rule.output_eq]
          exact markReadyRaw?_liveTreesExchangeFree rule.prepared.core_mark_eq ih
      | new _ _ newEq =>
          obtain ⟨rule⟩ := (new?_some_iff invariant.toReservationInvariant).mp newEq
          rw [rule.output_eq]
          exact reserveAxiomAt?_liveTreesExchangeFree rule.core_reserve_eq
            (markReadyRaw?_liveTreesExchangeFree rule.core_mark_eq ih)
      | wait _ _ _ waitEq =>
          obtain ⟨rule⟩ := (wait?_some_iff invariant.toReservationInvariant).mp waitEq
          rw [rule.destination.output_eq]
          exact markReadyRaw?_liveTreesExchangeFree rule.prepared.core_mark_eq ih
      | forward _ _ _ _ forwardEq =>
          obtain ⟨rule⟩ := (forward?_some_iff invariant.toReservationInvariant).mp forwardEq
          rw [rule.output_eq]
          exact queuePar?_liveTreesExchangeFree rule.core_queue_eq
            (markReadyRaw?_liveTreesExchangeFree rule.prepared.core_mark_eq ih)
      | unifyPayload _ _ _ _ _ unifyEq =>
          obtain ⟨rule⟩ := (unifyPayload?_some_iff invariant.toReservationInvariant).mp unifyEq
          rw [rule.output_eq]
          exact activateWaitingPayload?_liveTreesExchangeFree rule.activation_fold_eq
            (queueTensor?_liveTreesExchangeFree rule.tensor_queue_eq
              (markReadyRaw?_liveTreesExchangeFree rule.prepared.core_mark_eq ih))

/-! ## Inference and desequentialization of a witnessed tree -/

private theorem length_of_mapM_eq_some {α β : Type} {f : α → Option β} :
    ∀ {values : List α} {results : List β}, values.mapM f = some results →
      results.length = values.length := by
  intro values
  induction values with
  | nil =>
      intro results equation
      simp at equation
      rw [equation]
      rfl
  | cons head tail ih =>
      intro results equation
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at equation
      cases headEq : f head with
      | none => simp [headEq] at equation
      | some value =>
          cases tailEq : tail.mapM f with
          | none => simp [headEq, tailEq] at equation
          | some rest =>
              simp [headEq, tailEq] at equation
              rw [← equation]
              simp [ih tailEq]

private theorem length_le_of_nodup_subset' {values ambient : List Nat} (nodup : values.Nodup)
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

private theorem length_le_of_nodup_bounded' {values : List Nat} {size : Nat}
    (nodup : values.Nodup) (bounded : ∀ value ∈ values, value < size) :
    values.length ≤ size := by
  have := length_le_of_nodup_subset' nodup (ambient := List.range size)
    (fun value member ↦ List.mem_range.mpr (bounded value member))
  simpa using this

/-- A duplicate-free owned list is inside the carrier. -/
private theorem owned_length_le {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {tree : CutFreeDerivation}
    {frontier used owned : List Nat}
    (witness : certificate.OccurrenceDerivation tree frontier used owned)
    (ownedNodup : owned.Nodup) : owned.length ≤ certificate.formulas.size :=
  length_le_of_nodup_bounded' ownedNodup (witness.owned_inBounds structural)

/-- The exposed frontier is inside the owned list. -/
private theorem frontier_length_le {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {tree : CutFreeDerivation}
    {frontier used owned : List Nat}
    (witness : certificate.OccurrenceDerivation tree frontier used owned)
    (ownedNodup : owned.Nodup) : frontier.length ≤ certificate.formulas.size :=
  Nat.le_trans (length_le_of_nodup_subset' (witness.frontier_nodup_of_owned_nodup ownedNodup)
    (fun vertex member ↦ witness.frontier_subset_owned vertex member))
    (owned_length_le structural witness ownedNodup)

/-- A duplicate-free used list is inside the link list. -/
private theorem used_length_le {certificate : Certificate} {tree : CutFreeDerivation}
    {frontier used owned : List Nat}
    (witness : certificate.OccurrenceDerivation tree frontier used owned)
    (usedNodup : used.Nodup) : used.length ≤ certificate.links.length :=
  length_le_of_nodup_bounded' usedNodup fun _ member ↦ witness.usedLinkIndex_lt member

/-- The sequent inferred below a witnessed tree has the frontier's length. -/
theorem sequentLength_le {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {tree : CutFreeDerivation}
    {frontier used owned : List Nat}
    (witness : certificate.OccurrenceDerivation tree frontier used owned)
    (ownedNodup : owned.Nodup) : sequentLength tree ≤ certificate.formulas.size := by
  obtain ⟨sequent, inferred, labels⟩ := witness.formulaConsistent structural
  unfold sequentLength
  rw [inferred, Option.map_some, Option.getD_some, length_of_mapM_eq_some labels]
  exact frontier_length_le structural witness ownedNodup

private theorem nodup_of_cons {a : Nat} {l : List Nat} (nodup : (a :: l).Nodup) : l.Nodup :=
  (List.nodup_cons.mp nodup).2

private theorem nodup_of_append_left {l r : List Nat} (nodup : (l ++ r).Nodup) : l.Nodup :=
  nodup.sublist (List.sublist_append_left l r)

private theorem nodup_of_append_right {l r : List Nat} (nodup : (l ++ r).Nodup) : r.Nodup :=
  nodup.sublist (List.sublist_append_right l r)

/-- Inference of an exchange-free witnessed tree costs a linear amount per used link. -/
theorem inferCost_le {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {tree : CutFreeDerivation}
    {frontier used owned : List Nat}
    (witness : certificate.OccurrenceDerivation tree frontier used owned)
    (ownedNodup : owned.Nodup) (free : ExchangeFree tree) :
    inferCost tree ≤ used.length * (4 * certificate.formulas.size + 1) := by
  induction witness with
  | «axiom» index left right name positive lookup label =>
      simp [inferCost]
  | par premiseWitness index left right conclusion lf rf afterLeft context lookup lp rp ih =>
      have inner := ih (nodup_of_cons ownedNodup) free
      have sequent := sequentLength_le structural premiseWitness (nodup_of_cons ownedNodup)
      simp only [inferCost, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  | tensor lw rw index left right conclusion lf rf lc rc lookup lp rp lih rih =>
      have leftNodup := nodup_of_append_left (nodup_of_cons ownedNodup)
      have rightNodup := nodup_of_append_right (nodup_of_cons ownedNodup)
      have leftInner := lih leftNodup free.1
      have rightInner := rih rightNodup free.2
      have leftSequent := sequentLength_le structural lw leftNodup
      have rightSequent := sequentLength_le structural rw rightNodup
      simp only [inferCost, List.length_cons, List.length_append, Nat.add_mul, Nat.one_mul]
      omega
  | exchange _ _ _ _ _ => exact free.elim

/-- The fragment built below a witnessed tree has the owned occurrences as
carrier, the used links as links, and the frontier as boundary. -/
private theorem fragment_sizes_le {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {tree : CutFreeDerivation}
    {frontier used owned : List Nat}
    (witness : certificate.OccurrenceDerivation tree frontier used owned)
    (ownedNodup : owned.Nodup) (usedNodup : used.Nodup) :
    fragmentSize tree ≤ certificate.formulas.size ∧
      fragmentLinks tree ≤ certificate.links.length ∧
      fragmentEntries tree ≤ certificate.formulas.size := by
  obtain ⟨fragment, numbering, built, matched⟩ :=
    Certificate.occurrenceBuild_exists structural witness
  unfold fragmentSize fragmentLinks fragmentEntries
  rw [built]
  simp only [Option.map_some, Option.getD_some]
  refine ⟨?_, ?_, ?_⟩
  · rw [← matched.size_eq, matched.owned_perm.length_eq]
    exact owned_length_le structural witness ownedNodup
  · have perm := matched.links_perm.length_eq
    rw [List.length_map] at perm
    rw [perm]
    exact Nat.le_trans (List.length_filterMap_le _ _) (used_length_le witness usedNodup)
  · have balanced := CutFreeDerivation.build?_balanced built
    have entries : fragment.entries.length = fragment.roots.length := by
      unfold NetFragment.entries
      rw [List.length_zip, balanced, Nat.min_self]
    rw [entries]
    have roots : fragment.roots.length = frontier.length := by
      rw [← matched.roots_eq, List.length_map]
    rw [roots]
    exact frontier_length_le structural witness ownedNodup

/-- Desequentialization of an exchange-free witnessed tree costs a linear
amount per used link. -/
theorem buildCost_le {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {tree : CutFreeDerivation}
    {frontier used owned : List Nat}
    (witness : certificate.OccurrenceDerivation tree frontier used owned)
    (ownedNodup : owned.Nodup) (usedNodup : used.Nodup) (free : ExchangeFree tree) :
    buildCost tree ≤
      used.length * (6 * certificate.formulas.size + 3 * certificate.links.length + 2) := by
  induction witness with
  | «axiom» index left right name positive lookup label =>
      simp [buildCost]
  | par premiseWitness index left right conclusion lf rf afterLeft context lookup lp rp ih =>
      have inner := ih (nodup_of_cons ownedNodup) (nodup_of_cons usedNodup) free
      obtain ⟨_, links, entries⟩ := fragment_sizes_le structural premiseWitness
        (nodup_of_cons ownedNodup) (nodup_of_cons usedNodup)
      simp only [buildCost, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  | tensor lw rw index left right conclusion lf rf lc rc lookup lp rp lih rih =>
      have leftOwned := nodup_of_append_left (nodup_of_cons ownedNodup)
      have rightOwned := nodup_of_append_right (nodup_of_cons ownedNodup)
      have leftUsed := nodup_of_append_left (nodup_of_cons usedNodup)
      have rightUsed := nodup_of_append_right (nodup_of_cons usedNodup)
      have leftInner := lih leftOwned leftUsed free.1
      have rightInner := rih rightOwned rightUsed free.2
      obtain ⟨leftSize, leftLinks, leftEntries⟩ := fragment_sizes_le structural lw leftOwned leftUsed
      obtain ⟨rightSize, rightLinks, rightEntries⟩ :=
        fragment_sizes_le structural rw rightOwned rightUsed
      simp only [buildCost, List.length_cons, List.length_append, Nat.add_mul, Nat.one_mul]
      omega
  | exchange _ _ _ _ _ => exact free.elim

/-! ## The remaining phases -/

/-- Size of a certificate as submitted: occurrences, links, and conclusions. -/
def submittedSize (certificate : Certificate) : Nat :=
  certificate.formulas.size + certificate.links.length + certificate.conclusions.length + 1

private theorem expand_bound (n m k : Nat) :
    (n + 1) * (n + m + k + 1) = n * n + n * m + n * k + n + n + m + k + 1 := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

/-- Initialization is linear in the submitted size. -/
theorem initializationCost_le (certificate : Certificate) :
    initializationCost certificate ≤ 13 * (certificate.formulas.size + 1) * submittedSize certificate := by
  unfold initializationCost indexCost submittedSize
  rw [Nat.mul_assoc, expand_bound]
  omega

/-- The bounded run visits reachable states. -/
theorem runDispatcherWithStats_reachable {certificate : Certificate} (fuel : Nat)
    (state : ReservationState) (invariant : SchedulerInvariant certificate state)
    (reachable : ReachableByImplementedDispatcher certificate state) :
    ReachableByImplementedDispatcher certificate
      (runDispatcherWithStats certificate fuel state invariant).state := by
  induction fuel generalizing state invariant with
  | zero => exact reachable
  | succ fuel ih =>
      unfold runDispatcherWithStats
      split
      · exact reachable
      · rename_i result equation
        obtain ⟨history⟩ := reachable
        obtain ⟨step⟩ := (dispatch?_some_iff invariant).mp equation
        exact ih _ _ ⟨.later history invariant step⟩

/-- `occurrenceOrder?` returns one position per requested occurrence. -/
private theorem occurrenceOrder?_length {source : List Vertex} :
    ∀ {target : List Vertex} {order : List Nat},
      Certificate.occurrenceOrder? source target = some order → order.length = target.length := by
  intro target
  induction target with
  | nil =>
      intro order equation
      simp [Certificate.occurrenceOrder?] at equation
      simp [← equation]
  | cons vertex rest ih =>
      intro order equation
      simp only [Certificate.occurrenceOrder?, Option.bind_eq_bind] at equation
      cases found : source.findIdx? (· == vertex) with
      | none => simp [found] at equation
      | some index =>
          cases tailEq : Certificate.occurrenceOrder? source rest with
          | none => simp [found, tailEq] at equation
          | some tail =>
              simp [found, tailEq] at equation
              rw [← equation]
              simp only [List.length_cons, ih tailEq]

/-- A live component of an invariant state carries a duplicate-free witness. -/
private theorem live_component_witness {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state) {component : UnificationComponent}
    (live : component ∈ state.core.liveComponents) :
    ∃ used owned, certificate.ComponentOccurrenceWitness component used owned := by
  obtain ⟨usedAt, ownedAt, witnesses, _, _⟩ := invariant.component_forest_provenance
  unfold UnificationState.liveComponents at live
  obtain ⟨cell, member, cellEq⟩ := List.mem_filterMap.mp live
  obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
  rw [Array.getElem?_toList] at lookup
  cases cell with
  | none => cases cellEq
  | some found =>
      cases cellEq
      exact ⟨usedAt index, ownedAt index, (witnesses lookup).1⟩

/-- Final extraction is quadratic in the submitted size at every invariant state. -/
theorem extractionCost_le {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state) :
    extractionCost certificate state ≤
      3 * (certificate.formulas.size + 1) * submittedSize certificate := by
  have components : state.core.components.size ≤ certificate.formulas.size :=
    invariant.core_carriers_aligned ▸ parents_size_le invariant.toReservationInvariant
  have conclusions := conclusions_length_le invariant.structural
  unfold extractionCost submittedSize
  rw [Nat.mul_assoc, expand_bound]
  split
  · rename_i component live
    obtain ⟨used, owned, witness⟩ := live_component_witness invariant
      (component := component) (by rw [live]; simp)
    have frontier := frontier_length_le invariant.structural witness.derivation witness.owned_nodup
    have product : certificate.conclusions.length * component.frontier.length ≤
        certificate.formulas.size * certificate.formulas.size :=
      Nat.mul_le_mul conclusions frontier
    have square : certificate.conclusions.length * (certificate.conclusions.length + 1) ≤
        certificate.formulas.size * certificate.formulas.size + certificate.formulas.size := by
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add (Nat.mul_le_mul conclusions conclusions) conclusions
    omega
  · omega

/-! ## Formula symbols and the structural check -/

/-- Size of a certificate as submitted: occurrences, links, conclusions, and
formula symbols. -/
def inputSize (certificate : Certificate) : Nat :=
  certificate.formulas.size + certificate.links.length + certificate.conclusions.length +
    formulaTextTotal certificate + 1

private theorem sum_map_le_length_mul {α : Type} {f : α → Nat} {bound : Nat} :
    ∀ {l : List α}, (∀ x ∈ l, f x ≤ bound) → (l.map f).sum ≤ l.length * bound := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons head tail ih =>
      intro bounded
      have headBound := bounded head (by simp)
      have tailBound := ih fun x member ↦ bounded x (by simp [member])
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

private theorem le_sum_of_mem {a : Nat} : ∀ {l : List Nat}, a ∈ l → a ≤ l.sum := by
  intro l
  induction l with
  | nil => intro member; cases member
  | cons head tail ih =>
      intro member
      simp only [List.sum_cons]
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_add_right _ _
      · exact Nat.le_trans (ih member) (Nat.le_add_left _ _)

/-- Every stored formula of a well-formed certificate has fewer symbols than
twice the carrier plus one. -/
private theorem formulaText_le {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) (vertex : Vertex) :
    formulaText certificate vertex ≤ 2 * certificate.formulas.size + 1 := by
  unfold formulaText
  by_cases bound : vertex < certificate.formulas.size
  · have := structural.formulaComplexityAt_lt_size bound
    omega
  · have missing : certificate.formula? vertex = none := by
      unfold Certificate.formula?
      exact Array.getElem?_eq_none (Nat.le_of_not_lt bound)
    unfold Certificate.formulaComplexityAt
    rw [missing]
    simp

/-- The symbols of all stored formulas of a well-formed certificate are quadratic
in the carrier. -/
theorem formulaTextTotal_le {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) :
    formulaTextTotal certificate ≤
      certificate.formulas.size * (2 * certificate.formulas.size + 1) := by
  unfold formulaTextTotal
  have := sum_map_le_length_mul (l := List.range certificate.formulas.size)
    (f := formulaText certificate) (bound := 2 * certificate.formulas.size + 1)
    (fun vertex _ ↦ formulaText_le structural vertex)
  simpa using this

private theorem linkCheckCost_le {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) (link : Link) :
    linkCheckCost certificate link ≤ 1 + 3 * (2 * certificate.formulas.size + 1) := by
  unfold linkCheckCost
  have := sum_map_le_length_mul (l := link.vertices) (f := formulaText certificate)
    (bound := 2 * certificate.formulas.size + 1) (fun vertex _ ↦ formulaText_le structural vertex)
  have vertices : link.vertices.length ≤ 3 := by cases link <;> simp [Link.vertices]
  have := Nat.mul_le_mul_right (2 * certificate.formulas.size + 1) vertices
  omega

/-- The structural check of a well-formed certificate is quadratic. -/
theorem structuralCost_le_of_structural {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) :
    structuralCost certificate ≤
      9 * (certificate.formulas.size + 1) * submittedSize certificate := by
  have links := sum_map_le_length_mul (l := certificate.links) (f := linkCheckCost certificate)
    (bound := 1 + 3 * (2 * certificate.formulas.size + 1))
    (fun link _ ↦ linkCheckCost_le structural link)
  have conclusions := conclusions_length_le structural
  have linksBound := structural.links_length_le_formulas_size
  unfold structuralCost submittedSize
  rw [Nat.mul_assoc, expand_bound]
  have distribute : certificate.formulas.size *
      (2 * certificate.links.length + certificate.conclusions.length + 1) =
      2 * (certificate.formulas.size * certificate.links.length) +
        certificate.formulas.size * certificate.conclusions.length + certificate.formulas.size := by
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
  have conclusionsTerm : certificate.conclusions.length * (certificate.formulas.size + 1) =
      certificate.formulas.size * certificate.conclusions.length + certificate.conclusions.length := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
  have linksTerm : certificate.links.length * (1 + 3 * (2 * certificate.formulas.size + 1)) =
      6 * (certificate.formulas.size * certificate.links.length) + certificate.links.length * 4 := by
    have inner : 1 + 3 * (2 * certificate.formulas.size + 1) = 6 * certificate.formulas.size + 4 := by
      omega
    rw [inner, Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm certificate.links.length
      certificate.formulas.size]
  have square : certificate.formulas.size * certificate.links.length ≤
      certificate.formulas.size * certificate.formulas.size :=
    Nat.mul_le_mul_left _ linksBound
  omega

/-- The structural check of any certificate is quadratic in the submitted text. -/
theorem structuralCost_le_inputSize (certificate : Certificate) :
    structuralCost certificate ≤ 8 * inputSize certificate * inputSize certificate := by
  have textBound : ∀ link ∈ certificate.links,
      linkCheckCost certificate link ≤ 1 + 3 * (formulaTextTotal certificate + 1) := by
    intro link _
    unfold linkCheckCost
    have each : ∀ vertex ∈ link.vertices,
        formulaText certificate vertex ≤ formulaTextTotal certificate + 1 := by
      intro vertex _
      by_cases bound : vertex < certificate.formulas.size
      · have member : vertex ∈ List.range certificate.formulas.size := List.mem_range.mpr bound
        unfold formulaTextTotal
        exact Nat.le_trans (le_sum_of_mem (List.mem_map_of_mem member)) (Nat.le_succ _)
      · have missing : certificate.formula? vertex = none := by
          unfold Certificate.formula?
          exact Array.getElem?_eq_none (Nat.le_of_not_lt bound)
        unfold formulaText Certificate.formulaComplexityAt
        rw [missing]
        simp
    have := sum_map_le_length_mul (l := link.vertices) (f := formulaText certificate)
      (bound := formulaTextTotal certificate + 1) each
    have vertices : link.vertices.length ≤ 3 := by cases link <;> simp [Link.vertices]
    have := Nat.mul_le_mul_right (formulaTextTotal certificate + 1) vertices
    omega
  have links := sum_map_le_length_mul (l := certificate.links) (f := linkCheckCost certificate)
    (bound := 1 + 3 * (formulaTextTotal certificate + 1)) textBound
  unfold structuralCost inputSize
  generalize certificate.formulas.size = n at *
  generalize certificate.links.length = m at *
  generalize certificate.conclusions.length = k at *
  generalize formulaTextTotal certificate = t at *
  generalize (certificate.links.map (linkCheckCost certificate)).sum = c at *
  have expand : (n + m + k + t + 1) * (n + m + k + t + 1) =
      n * n + n * m + n * k + n * t + n + m * n + m * m + m * k + m * t + m +
        k * n + k * m + k * k + k * t + k + t * n + t * m + t * k + t * t + t +
        n + m + k + t + 1 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  rw [Nat.mul_assoc, expand]
  have h1 : m * (1 + 3 * (t + 1)) = 3 * (m * t) + 4 * m := by
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
    omega
  have h2 : n * (2 * m + k + 1) = 2 * (n * m) + n * k + n := by
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
  have h3 : k * (n + 1) = k * n + k := by rw [Nat.mul_add, Nat.mul_one]
  have comm1 : m * n = n * m := Nat.mul_comm m n
  have comm2 : k * n = n * k := Nat.mul_comm k n
  omega

/-! ## Verification of the extracted derivation -/

/-- Successful extraction is the exchange of the single live component. -/
private theorem sequentialFinalTree?_eq_some_iff {certificate : Certificate} {state : ReservationState}
    {tree : CutFreeDerivation} (equation : Certificate.sequentialFinalTree? certificate state = some tree) :
    ∃ component order, state.core.liveComponents = [component] ∧
      Certificate.occurrenceOrder? component.frontier certificate.conclusions = some order ∧
      tree = .exchange order component.tree := by
  unfold Certificate.sequentialFinalTree? at equation
  split at equation
  · rename_i component live
    cases orderEq : Certificate.occurrenceOrder? component.frontier certificate.conclusions with
    | none => simp [orderEq] at equation
    | some order =>
        refine ⟨component, order, live, orderEq, ?_⟩
        by_cases lengthEq : component.frontier.length = certificate.conclusions.length
        · by_cases dupEq : order.eraseDups.length = order.length
          · simp [orderEq, lengthEq, dupEq, guard] at equation
            exact equation.symm
          · simp [orderEq, lengthEq, dupEq, guard,
              show (failure : Option Unit) = none from rfl] at equation
        · simp [orderEq, lengthEq, guard, show (failure : Option Unit) = none from rfl] at equation
  · cases equation

/-- The comparison of a well-formed certificate is quadratic. -/
theorem compareCost_le {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) :
    compareCost certificate ≤ 3 * (certificate.formulas.size + 1) * submittedSize certificate := by
  have text := formulaTextTotal_le structural
  have conclusions := conclusions_length_le structural
  have links := structural.links_length_le_formulas_size
  unfold compareCost submittedSize
  rw [Nat.mul_assoc, expand_bound]
  have expand : certificate.formulas.size * (2 * certificate.formulas.size + 1) =
      2 * (certificate.formulas.size * certificate.formulas.size) + certificate.formulas.size := by
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
  omega

/-- `reorder?` over a bounded list by a bounded order is quadratic. -/
private theorem reorderCost_le {length : Nat} {order : List Nat} {n : Nat}
    (lengthBound : length ≤ n) (orderBound : order.length ≤ n) :
    reorderCost length order ≤ 3 * (n * n) + 2 * n + 1 := by
  unfold reorderCost
  have a : order.length * (order.length + 1) ≤ n * n + n := by
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_le_add (Nat.mul_le_mul orderBound orderBound) orderBound
  have b : order.length * length ≤ n * n := Nat.mul_le_mul orderBound lengthBound
  have c : length * length ≤ n * n := Nat.mul_le_mul lengthBound lengthBound
  omega

/-- The exchange of a built tree keeps its carrier and links and reorders its boundary. -/
private theorem build?_exchange_sizes {order : List Nat} {tree : CutFreeDerivation}
    {output : NetFragment} (built : (CutFreeDerivation.exchange order tree).build? = some output) :
    ∃ fragment, tree.build? = some fragment ∧ output.formulas = fragment.formulas ∧
      output.links = fragment.links ∧ output.roots.length = fragment.entries.length := by
  simp only [CutFreeDerivation.build?, Option.bind_eq_bind] at built
  cases premiseEq : tree.build? with
  | none => simp [premiseEq] at built
  | some fragment =>
      cases reorderEq : CutFreeDerivation.reorder? fragment.entries order with
      | none => simp [premiseEq, reorderEq] at built
      | some reordered =>
          simp [premiseEq, reorderEq] at built
          refine ⟨fragment, rfl, ?_, ?_, ?_⟩
          · rw [← built]; rfl
          · rw [← built]; rfl
          · rw [← built]
            simp only [NetFragment.ofEntries, List.length_map]
            exact (CutFreeDerivation.reorder?_perm reorderEq).length_eq.symm

/-- Verification of the extracted derivation at a reachable invariant state is
quadratic: the tree has one node per used link plus the root exchange, the
fragments stay inside the carrier, and both canonicalizations and the
comparison are quadratic. -/
theorem verificationCost_le {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    (reachable : ReachableByImplementedDispatcher certificate state)
    {tree : CutFreeDerivation}
    (extracted : Certificate.sequentialFinalTree? certificate state = some tree) :
    verificationCost certificate tree ≤
      54 * (certificate.formulas.size + 1) * submittedSize certificate := by
  obtain ⟨component, order, live, orderEq, treeEq⟩ := sequentialFinalTree?_eq_some_iff extracted
  obtain ⟨used, owned, witness⟩ := live_component_witness invariant
    (component := component) (by rw [live]; simp)
  obtain ⟨history⟩ := reachable
  have free : ExchangeFree component.tree := by
    unfold UnificationState.liveComponents at live
    have member : component ∈ state.core.components.toList.filterMap id := by rw [live]; simp
    obtain ⟨cell, cellMember, cellEq⟩ := List.mem_filterMap.mp member
    obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp cellMember
    rw [Array.getElem?_toList] at lookup
    cases cell with
    | none => cases cellEq
    | some found =>
        cases cellEq
        exact ExecutedHistory.liveTreesExchangeFree history lookup
  have structural : certificate.StructurallyWellFormed := invariant.structural
  have orderLength : order.length = certificate.conclusions.length :=
    occurrenceOrder?_length orderEq
  have conclusions := conclusions_length_le structural
  have linksBound := structural.links_length_le_formulas_size
  have usedBound := used_length_le witness.derivation witness.usedLinks_nodup
  have infer := inferCost_le structural witness.derivation witness.owned_nodup free
  have build := buildCost_le structural witness.derivation witness.owned_nodup
    witness.usedLinks_nodup free
  have sequent := sequentLength_le structural witness.derivation witness.owned_nodup
  obtain ⟨size, links, entries⟩ := fragment_sizes_le structural witness.derivation
    witness.owned_nodup witness.usedLinks_nodup
  have inferReorder := reorderCost_le (n := certificate.formulas.size) sequent
    (orderLength ▸ conclusions)
  have buildReorder := reorderCost_le (n := certificate.formulas.size) entries
    (orderLength ▸ conclusions)
  have structuralBound := structuralCost_le_of_structural structural
  have canonInput := structural.canonicalizeCost_le
  have compareInput := compareCost_le structural
  subst treeEq
  -- the desequentialized output
  have outputBound : outputCost (CutFreeDerivation.exchange order component.tree) ≤
      8 * (certificate.formulas.size + 1) *
          (certificate.formulas.size + certificate.links.length + 1) +
        (certificate.formulas.size * (2 * certificate.formulas.size + 1) +
          certificate.links.length + certificate.formulas.size) := by
    unfold outputCost
    split
    · rename_i output outputEq
      unfold CutFreeDerivation.desequentialize? at outputEq
      cases builtEq : (CutFreeDerivation.exchange order component.tree).build? with
      | none => simp [builtEq] at outputEq
      | some fragment' =>
          simp [builtEq] at outputEq
          obtain ⟨fragment, premiseBuilt, formulasEq, linksEq, rootsEq⟩ :=
            build?_exchange_sizes builtEq
          have outputStructural : output.StructurallyWellFormed := by
            rw [← outputEq]
            exact CutFreeDerivation.build?_structurallyWellFormed builtEq
          have sizeEq : output.formulas.size = fragmentSize component.tree := by
            rw [← outputEq]
            show fragment'.formulas.size = _
            rw [formulasEq]
            unfold fragmentSize
            rw [premiseBuilt]
            rfl
          have linksEq' : output.links.length = fragmentLinks component.tree := by
            rw [← outputEq]
            show fragment'.links.length = _
            rw [linksEq]
            unfold fragmentLinks
            rw [premiseBuilt]
            rfl
          have conclusionsEq : output.conclusions.length = fragmentEntries component.tree := by
            rw [← outputEq]
            show fragment'.roots.length = _
            rw [rootsEq]
            unfold fragmentEntries
            rw [premiseBuilt]
            rfl
          have canon := outputStructural.canonicalizeCost_le
          have canonMono : 8 * (output.formulas.size + 1) *
              (output.formulas.size + output.links.length + 1) ≤
              8 * (certificate.formulas.size + 1) *
                (certificate.formulas.size + certificate.links.length + 1) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 8 (by omega)) (by omega)
          have text := formulaTextTotal_le outputStructural
          have textMono : output.formulas.size * (2 * output.formulas.size + 1) ≤
              certificate.formulas.size * (2 * certificate.formulas.size + 1) :=
            Nat.mul_le_mul (by omega) (by omega)
          unfold compareCost
          have linksOut : output.links.length ≤ certificate.links.length := by omega
          have conclusionsOut : output.conclusions.length ≤ certificate.formulas.size := by omega
          exact Nat.add_le_add (Nat.le_trans canon canonMono)
            (Nat.add_le_add (Nat.add_le_add (Nat.le_trans text textMono) linksOut) conclusionsOut)
    · exact Nat.zero_le _
  unfold verificationCost submittedSize at *
  simp only [inferCost, buildCost] at *
  have expandEight : 8 * (certificate.formulas.size + 1) *
      (certificate.formulas.size + certificate.links.length + 1) =
      8 * (certificate.formulas.size * certificate.formulas.size +
        certificate.formulas.size * certificate.links.length + certificate.formulas.size +
        certificate.formulas.size + certificate.links.length + 1) := by
    rw [Nat.mul_assoc]
    congr 1
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  have inferTerm : used.length * (4 * certificate.formulas.size + 1) ≤
      4 * (certificate.formulas.size * certificate.links.length) + certificate.links.length := by
    have := Nat.mul_le_mul_right (4 * certificate.formulas.size + 1) usedBound
    have expand : certificate.links.length * (4 * certificate.formulas.size + 1) =
        4 * (certificate.formulas.size * certificate.links.length) + certificate.links.length := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, Nat.mul_comm certificate.links.length]
    omega
  have buildTerm : used.length *
      (6 * certificate.formulas.size + 3 * certificate.links.length + 2) ≤
      9 * (certificate.formulas.size * certificate.links.length) + 2 * certificate.links.length := by
    have := Nat.mul_le_mul_right
      (6 * certificate.formulas.size + 3 * certificate.links.length + 2) usedBound
    have expand : certificate.links.length *
        (6 * certificate.formulas.size + 3 * certificate.links.length + 2) =
        6 * (certificate.formulas.size * certificate.links.length) +
          3 * (certificate.links.length * certificate.links.length) +
          certificate.links.length * 2 := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_left_comm certificate.links.length 6,
        Nat.mul_comm certificate.links.length certificate.formulas.size,
        Nat.mul_left_comm certificate.links.length 3]
    have square : certificate.links.length * certificate.links.length ≤
        certificate.formulas.size * certificate.links.length :=
      Nat.mul_le_mul_right _ linksBound
    omega
  have textExpand : certificate.formulas.size * (2 * certificate.formulas.size + 1) =
      2 * (certificate.formulas.size * certificate.formulas.size) + certificate.formulas.size := by
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
  have square : certificate.formulas.size * certificate.links.length ≤
      certificate.formulas.size * certificate.formulas.size :=
    Nat.mul_le_mul_left _ linksBound
  have target := expand_bound certificate.formulas.size certificate.links.length
    certificate.conclusions.length
  rw [Nat.mul_assoc, target]
  rw [Nat.mul_assoc, expand_bound] at structuralBound compareInput
  rw [expandEight] at canonInput outputBound
  omega

/-! ## The whole decision -/

/-- Every phase of the public decision on a structurally well-formed certificate
is quadratic in the carrier, the links, and the conclusions. -/
theorem decisionStats_total_le_of_structural {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) :
    certificate.sequentialDecisionWithStats.stats.total ≤
      152 * (certificate.formulas.size + 1) * submittedSize certificate := by
  have wellFormed : certificate.wellFormed = true :=
    certificate.wellFormed_iff_structurallyWellFormed.mpr structural
  have structuralBound := structuralCost_le_of_structural structural
  have initBound := initializationCost_le certificate
  have callsBound : certificate.formulas.size + 1 ≤
      (certificate.formulas.size + 1) * submittedSize certificate := by
    unfold submittedSize
    exact Nat.le_mul_of_pos_right _ (by omega)
  have sizeBound : (certificate.formulas.size + 1) *
      (certificate.formulas.size + certificate.links.length + 1) ≤
      (certificate.formulas.size + 1) * submittedSize certificate := by
    unfold submittedSize
    exact Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_assoc] at structuralBound initBound
  unfold Certificate.sequentialDecisionWithStats
  rw [dif_pos wellFormed, Nat.mul_assoc]
  cases headEq : certificate.conclusions.head? with
  | none =>
      simp only [SequentialDecisionStats.total, SequentialDecisionStats.early]
      omega
  | some start =>
      dsimp only
      split
      · simp only [SequentialDecisionStats.total, SequentialDecisionStats.early]
        omega
      · rename_i state initEq
        have invariant := initializeReservation?_schedulerInvariant structural initEq
        have dispatch := dispatchPhase_le initEq invariant
        have calls := runDispatcherWithStats_calls_le certificate
          (certificate.formulas.size + 1) state invariant
        have extraction := extractionCost_le
          (runDispatcherWithStats certificate (certificate.formulas.size + 1) state invariant).invariant
        obtain ⟨step⟩ := initializeReservation?_some_iff.mp initEq
        have reachable := runDispatcherWithStats_reachable (certificate.formulas.size + 1) state
          invariant ⟨.init step⟩
        have dispatchBound : (runDispatcherWithStats certificate (certificate.formulas.size + 1)
            state invariant).cost ≤ 72 * (certificate.formulas.size + 1) * submittedSize certificate := by
          rw [Nat.mul_assoc] at dispatch ⊢
          exact Nat.le_trans dispatch (Nat.mul_le_mul_left 72 sizeBound)
        rw [Nat.mul_assoc] at dispatchBound extraction
        split
        · simp only [SequentialDecisionStats.total]
          omega
        · rename_i tree extracted
          have verification := verificationCost_le
            (runDispatcherWithStats certificate (certificate.formulas.size + 1) state invariant).invariant
            reachable extracted
          rw [Nat.mul_assoc] at verification
          simp only [SequentialDecisionStats.total]
          omega

/-- The public decision on any certificate is quadratic in the submitted text:
a structurally well-formed input runs every phase within the quadratic bound
above, and any other input stops after the structural check. -/
theorem decisionStats_total_le (certificate : Certificate) :
    certificate.sequentialDecisionWithStats.stats.total ≤
      152 * inputSize certificate * inputSize certificate := by
  by_cases wellFormed : certificate.wellFormed = true
  · have structural := certificate.wellFormed_iff_structurallyWellFormed.mp wellFormed
    have bound := decisionStats_total_le_of_structural structural
    have carrier : certificate.formulas.size + 1 ≤ inputSize certificate := by
      unfold inputSize
      omega
    have submitted : submittedSize certificate ≤ inputSize certificate := by
      unfold submittedSize inputSize
      omega
    exact Nat.le_trans bound (Nat.mul_le_mul (Nat.mul_le_mul_left 152 carrier) submitted)
  · have structural := structuralCost_le_inputSize certificate
    unfold Certificate.sequentialDecisionWithStats
    rw [dif_neg wellFormed]
    simp only [SequentialDecisionStats.total, SequentialDecisionStats.early]
    have := Nat.mul_le_mul_right (inputSize certificate)
      (Nat.mul_le_mul_right (inputSize certificate) (show 8 ≤ 152 by omega))
    omega

end SequentialCost
end ProofNetIR
