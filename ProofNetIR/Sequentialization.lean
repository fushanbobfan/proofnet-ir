import Lean.Elab.Tactic.Omega
import ProofNetIR.DerivationTree
import ProofNetIR.NetEquivalence

namespace ProofNetIR

private theorem eq_of_mem_filter_length_one {α : Type}
    {values : List α} {predicate : α → Bool} {first second : α}
    (count : (values.filter predicate).length = 1)
    (firstMembership : first ∈ values) (firstAccepted : predicate first = true)
    (secondMembership : second ∈ values)
    (secondAccepted : predicate second = true) :
    first = second := by
  have firstFiltered : first ∈ values.filter predicate := by
    simp [firstMembership, firstAccepted]
  have secondFiltered : second ∈ values.filter predicate := by
    simp [secondMembership, secondAccepted]
  rcases List.length_eq_one_iff.mp count with ⟨only, filterEquation⟩
  rw [filterEquation] at firstFiltered secondFiltered
  simp at firstFiltered secondFiltered
  exact firstFiltered.trans secondFiltered.symm

private theorem false_of_mem_filter_length_zero {α : Type}
    {values : List α} {predicate : α → Bool} {value : α}
    (count : (values.filter predicate).length = 0)
    (membership : value ∈ values) (accepted : predicate value = true) :
    False := by
  have filtered : value ∈ values.filter predicate := by
    simp [membership, accepted]
  have positive := List.length_pos_of_mem filtered
  rw [count] at positive
  exact Nat.not_lt_zero 0 positive

private theorem length_eraseDups_le [BEq α] (values : List α) :
    values.eraseDups.length ≤ values.length := by
  cases values with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons, Nat.add_le_add_iff_right]
      exact Nat.le_trans
        (length_eraseDups_le (tail.filter fun value => !value == head))
        (List.length_filter_le _ tail)
termination_by values.length
decreasing_by
  exact Nat.lt_add_one_of_le (List.length_filter_le _ tail)

private theorem nodup_of_eraseDups_length_eq [BEq α] [LawfulBEq α]
    {values : List α}
    (sameLength : values.eraseDups.length = values.length) :
    values.Nodup := by
  induction values with
  | nil => exact .nil
  | cons head tail ih =>
      rw [List.eraseDups_cons] at sameLength
      simp only [List.length_cons] at sameLength
      let retained := tail.filter fun value => !value == head
      have erasedEqualsTail : retained.eraseDups.length = tail.length := by
        change (tail.filter fun value => !value == head).eraseDups.length =
          tail.length
        exact Nat.add_right_cancel sameLength
      have retainedAtMost : retained.length ≤ tail.length :=
        List.length_filter_le _ tail
      have erasedAtMost : retained.eraseDups.length ≤ retained.length :=
        length_eraseDups_le retained
      have retainedAtLeast : tail.length ≤ retained.length := by
        rw [← erasedEqualsTail]
        exact erasedAtMost
      have retainedLength : retained.length = tail.length :=
        Nat.le_antisymm retainedAtMost retainedAtLeast
      have allRetained : ∀ value ∈ tail, value != head :=
        List.length_filter_eq_length_iff.mp retainedLength
      have retainedEquation : retained = tail :=
        List.filter_eq_self.mpr allRetained
      have headFresh : head ∉ tail := by
        intro membership
        have rejected := allRetained head membership
        simp at rejected
      apply List.nodup_cons.mpr
      refine ⟨headFresh, ih ?_⟩
      simpa only [retainedEquation] using erasedEqualsTail

private theorem eraseDups_eq_self_of_nodup [BEq α] [LawfulBEq α]
    {values : List α} (nodup : values.Nodup) :
    values.eraseDups = values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      rcases List.nodup_cons.mp nodup with ⟨headFresh, tailNodup⟩
      rw [List.eraseDups_cons]
      have allDifferent : ∀ value ∈ tail, !(value == head) := by
        intro value membership
        have different : value ≠ head := by
          intro same
          subst value
          exact headFresh membership
        simp [beq_eq_false_iff_ne.mpr different]
      rw [List.filter_eq_self.mpr allDifferent, ih tailNodup]

private theorem nodup_map_of_injective_on {α β : Type}
    {values : List α} {function : α → β}
    (nodup : values.Nodup)
    (injectiveOn : ∀ first ∈ values, ∀ second ∈ values,
      function first = function second → first = second) :
    (values.map function).Nodup := by
  induction values with
  | nil => exact .nil
  | cons head tail ih =>
      rcases List.nodup_cons.mp nodup with ⟨headFresh, tailNodup⟩
      apply List.nodup_cons.mpr
      constructor
      · intro headImageInTail
        rcases List.mem_map.mp headImageInTail with
          ⟨value, valueMembership, imageEqual⟩
        have same := injectiveOn value (by simp [valueMembership]) head
          (by simp) imageEqual
        subst value
        exact headFresh valueMembership
      · apply ih tailNodup
        intro first firstMembership second secondMembership same
        exact injectiveOn first (by simp [firstMembership]) second
          (by simp [secondMembership]) same

private theorem length_filter_filterMap_eq {α β : Type}
    (values : List α) (transform : α → Option β)
    (after : β → Bool) (before : α → Bool)
    (compatible : ∀ value ∈ values,
      match transform value with
      | none => before value = false
      | some transformed => after transformed = before value) :
    ((values.filterMap transform).filter after).length =
      (values.filter before).length := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      have headCompatible := compatible head (by simp)
      have tailCompatible : ∀ value ∈ tail,
          match transform value with
          | none => before value = false
          | some transformed => after transformed = before value := by
        intro value membership
        exact compatible value (by simp [membership])
      cases equation : transform head with
      | none =>
          have rejected : before head = false := by
            simpa [equation] using headCompatible
          simp [equation, rejected, ih tailCompatible]
      | some transformed =>
          have agrees : after transformed = before head := by
            simpa [equation] using headCompatible
          cases accepted : before head with
          | false =>
              have afterRejected : after transformed = false :=
                agrees.trans accepted
              simp [equation, accepted, afterRejected, ih tailCompatible]
          | true =>
              have afterAccepted : after transformed = true :=
                agrees.trans accepted
              simp [equation, accepted, afterAccepted, ih tailCompatible]

/-- Evidence returned by the future general sequentializer. The result is
deliberately stronger than an `Option CutFreeDerivation`: it connects
first-order inference, desequentialization, ordered boundary labels, and the
semantic proof-net equivalence relation. -/
structure SequentializationResult (input : Certificate) where
  tree : CutFreeDerivation
  sequent : List Formula
  output : Certificate
  inferred : tree.infer? = some sequent
  desequentialized : tree.desequentialize? = some output
  outputLabels : output.conclusionFormulas? = some sequent
  equivalent : output.ProofNetEquivalent input

namespace SequentializationResult

/-- A sequentialization result always contains a kernel-typed object-logic
derivation; this does not trust the proof-net checker. -/
theorem kernelDerivation {input : Certificate}
    (result : SequentializationResult input) :
    Nonempty (Derivation result.sequent) :=
  result.tree.infer?_sound result.inferred

/-- Proof-net equivalence transports the ordered conclusion formulas from the
desequentialized output back to the input certificate. -/
theorem inputLabels {input : Certificate}
    (result : SequentializationResult input) :
    input.conclusionFormulas? = some result.sequent := by
  calc
    input.conclusionFormulas? = result.output.conclusionFormulas? :=
      result.equivalent.conclusionFormulas?_eq.symm
    _ = some result.sequent := result.outputLabels

/-- If the input was accepted, the reconstructed proof net is accepted as
well. This follows from proved equivalence invariance, not from rerunning and
assuming the checker. -/
theorem outputAccepted {input : Certificate}
    (result : SequentializationResult input)
    (accepted : input.check = true) :
    result.output.check = true := by
  rw [result.equivalent.check_eq]
  exact accepted

/-- Package a successful general sequentialization in the existing checked
derivation/certificate API. -/
def toElaboratedCertificate {input : Certificate}
    (result : SequentializationResult input)
    (accepted : input.check = true) :
    CutFreeDerivation.ElaboratedCertificate where
  sequent := result.sequent
  derivation := result.kernelDerivation
  certificate := result.output
  conclusionLabels := result.outputLabels
  accepted := result.outputAccepted accepted

end SequentializationResult

/-- The exact macro theorem still to be constructed by terminal-par peeling,
splitting-tensor decomposition, and well-founded recursion. Keeping it as a
named proposition prevents a search routine from being mistaken for the
mathematical theorem. -/
def GenerallySequentializable : Prop :=
  ∀ input : Certificate,
    input.check = true → Nonempty (SequentializationResult input)

namespace Certificate

/-- Total compaction map used once the deleted occurrence is known not to be
the input vertex. -/
def compactVertex (removed vertex : Nat) : Nat :=
  if vertex < removed then vertex else vertex - 1

/-- Order-preserving embedding from compacted names back into the original
vertex interval. -/
def expandVertex (removed vertex : Nat) : Nat :=
  if vertex < removed then vertex else vertex + 1

/-- Compact an old vertex name after deleting one formula occurrence. -/
def deleteVertex? (removed vertex : Vertex) : Option Vertex :=
  if vertex = removed then
    none
  else
    some (compactVertex removed vertex)

@[simp] theorem deleteVertex?_self (vertex : Vertex) :
    deleteVertex? vertex vertex = none := by
  simp [deleteVertex?]

theorem deleteVertex?_of_lt {removed vertex : Vertex}
    (before : vertex < removed) :
    deleteVertex? removed vertex = some vertex := by
  simp [deleteVertex?, compactVertex, Nat.ne_of_lt before, before]

theorem deleteVertex?_of_gt {removed vertex : Vertex}
    (after : removed < vertex) :
    deleteVertex? removed vertex = some (vertex - 1) := by
  simp [deleteVertex?, compactVertex, Nat.ne_of_gt after,
    Nat.not_lt.mpr (Nat.le_of_lt after)]

theorem deleteVertex?_eq_some_of_ne {removed vertex : Vertex}
    (different : vertex ≠ removed) :
    deleteVertex? removed vertex = some (compactVertex removed vertex) := by
  simp [deleteVertex?, different]

@[simp] theorem compactVertex_expandVertex (removed vertex : Nat) :
    compactVertex removed (expandVertex removed vertex) = vertex := by
  by_cases before : vertex < removed
  · simp [compactVertex, expandVertex, before]
  · have notBefore : ¬vertex + 1 < removed := by omega
    simp [compactVertex, expandVertex, before, notBefore]

theorem expandVertex_compactVertex_of_ne {removed vertex : Nat}
    (different : vertex ≠ removed) :
    expandVertex removed (compactVertex removed vertex) = vertex := by
  by_cases before : vertex < removed
  · simp [compactVertex, expandVertex, before]
  · have after : removed < vertex := by omega
    have compactNotBefore : ¬vertex - 1 < removed := by omega
    simp [compactVertex, expandVertex, before, compactNotBefore]
    omega

theorem compactVertex_injective_of_ne {removed first second : Nat}
    (firstNotRemoved : first ≠ removed)
    (secondNotRemoved : second ≠ removed)
    (same : compactVertex removed first = compactVertex removed second) :
    first = second := by
  have expanded := congrArg (expandVertex removed) same
  simpa [expandVertex_compactVertex_of_ne firstNotRemoved,
    expandVertex_compactVertex_of_ne secondNotRemoved] using expanded

theorem compactVertex_lt {removed vertex bound : Nat}
    (removedInBounds : removed < bound) (vertexInBounds : vertex < bound)
    (different : vertex ≠ removed) :
    compactVertex removed vertex < bound - 1 := by
  by_cases before : vertex < removed
  · simp [compactVertex, before]
    omega
  · simp [compactVertex, before]
    omega

theorem expandVertex_lt {removed vertex bound : Nat}
    (removedInBounds : removed < bound)
    (vertexInBounds : vertex < bound - 1) :
    expandVertex removed vertex < bound := by
  by_cases before : vertex < removed
  · simp [expandVertex, before]
    omega
  · simp [expandVertex, before]
    omega

theorem expandVertex_ne (removed vertex : Nat) :
    expandVertex removed vertex ≠ removed := by
  by_cases before : vertex < removed
  · simp [expandVertex, before]
    omega
  · simp [expandVertex, before]
    omega

end Certificate

namespace Link

/-- Delete one formula occurrence and compact every remaining endpoint. A
link incident to the deleted occurrence is removed. -/
def deleteVertex? (removed : Vertex) : Link → Option Link
  | .axiom left right => do
      let left' ← Certificate.deleteVertex? removed left
      let right' ← Certificate.deleteVertex? removed right
      pure (.axiom left' right')
  | .tensor left right conclusion => do
      let left' ← Certificate.deleteVertex? removed left
      let right' ← Certificate.deleteVertex? removed right
      let conclusion' ← Certificate.deleteVertex? removed conclusion
      pure (.tensor left' right' conclusion')
  | .par left right conclusion => do
      let left' ← Certificate.deleteVertex? removed left
      let right' ← Certificate.deleteVertex? removed right
      let conclusion' ← Certificate.deleteVertex? removed conclusion
      pure (.par left' right' conclusion')

def compactVertices (removed : Vertex) : Link → Link
  | .axiom first second =>
      .axiom (Certificate.compactVertex removed first)
        (Certificate.compactVertex removed second)
  | .tensor first second result =>
      .tensor (Certificate.compactVertex removed first)
        (Certificate.compactVertex removed second)
        (Certificate.compactVertex removed result)
  | .par first second result =>
      .par (Certificate.compactVertex removed first)
        (Certificate.compactVertex removed second)
        (Certificate.compactVertex removed result)

theorem deleteVertex?_eq_some_iff (link compacted : Link)
    (removed : Vertex) :
    link.deleteVertex? removed = some compacted ↔
      removed ∉ link.vertices ∧ compacted = link.compactVertices removed := by
  cases link with
  | «axiom» first second =>
      by_cases firstRemoved : removed = first <;>
      by_cases secondRemoved : removed = second <;>
        simp [deleteVertex?, Certificate.deleteVertex?, compactVertices,
          vertices, firstRemoved, secondRemoved, eq_comm]
  | tensor first second result =>
      by_cases firstRemoved : removed = first <;>
      by_cases secondRemoved : removed = second <;>
      by_cases resultRemoved : removed = result <;>
        simp [deleteVertex?, Certificate.deleteVertex?, compactVertices,
          vertices, firstRemoved, secondRemoved, resultRemoved, eq_comm]
  | par first second result =>
      by_cases firstRemoved : removed = first <;>
      by_cases secondRemoved : removed = second <;>
      by_cases resultRemoved : removed = result <;>
        simp [deleteVertex?, Certificate.deleteVertex?, compactVertices,
          vertices, firstRemoved, secondRemoved, resultRemoved, eq_comm]

theorem deleteVertex?_eq_none_iff (link : Link) (removed : Vertex) :
    link.deleteVertex? removed = none ↔ removed ∈ link.vertices := by
  cases link with
  | «axiom» first second =>
      by_cases firstRemoved : removed = first <;>
      by_cases secondRemoved : removed = second <;>
        simp [deleteVertex?, Certificate.deleteVertex?, vertices,
          firstRemoved, secondRemoved, eq_comm]
  | tensor first second result =>
      by_cases firstRemoved : removed = first <;>
      by_cases secondRemoved : removed = second <;>
      by_cases resultRemoved : removed = result <;>
        simp [deleteVertex?, Certificate.deleteVertex?, vertices,
          firstRemoved, secondRemoved, resultRemoved, eq_comm]
  | par first second result =>
      by_cases firstRemoved : removed = first <;>
      by_cases secondRemoved : removed = second <;>
      by_cases resultRemoved : removed = result <;>
        simp [deleteVertex?, Certificate.deleteVertex?, vertices,
          firstRemoved, secondRemoved, resultRemoved, eq_comm]

theorem containsAxiomEndpoint_deleteVertex?_eq_some
    {link compacted : Link} {removed vertex : Vertex}
    (vertexNotRemoved : vertex ≠ removed)
    (deleted : link.deleteVertex? removed = some compacted) :
    compacted.containsAxiomEndpoint (Certificate.compactVertex removed vertex) =
      link.containsAxiomEndpoint vertex := by
  rcases (deleteVertex?_eq_some_iff link compacted removed).mp deleted with
    ⟨avoids, rfl⟩
  cases link with
  | «axiom» first second =>
      simp [vertices] at avoids
      have firstNotRemoved : first ≠ removed := Ne.symm avoids.1
      have secondNotRemoved : second ≠ removed := Ne.symm avoids.2
      apply Bool.eq_iff_iff.mpr
      simp only [compactVertices, containsAxiomEndpoint, Bool.or_eq_true,
        beq_iff_eq]
      constructor
      · intro membership
        rcases membership with same | same
        · exact Or.inl (Certificate.compactVertex_injective_of_ne
            firstNotRemoved vertexNotRemoved same)
        · exact Or.inr (Certificate.compactVertex_injective_of_ne
            secondNotRemoved vertexNotRemoved same)
      · intro membership
        rcases membership with rfl | rfl <;> simp
  | tensor first second result => rfl
  | par first second result => rfl

theorem produces_deleteVertex?_eq_some
    {link compacted : Link} {removed vertex : Vertex}
    (vertexNotRemoved : vertex ≠ removed)
    (deleted : link.deleteVertex? removed = some compacted) :
    compacted.produces (Certificate.compactVertex removed vertex) =
      link.produces vertex := by
  rcases (deleteVertex?_eq_some_iff link compacted removed).mp deleted with
    ⟨avoids, rfl⟩
  cases link with
  | «axiom» first second => rfl
  | tensor first second result =>
      simp [vertices] at avoids
      have resultNotRemoved : result ≠ removed := Ne.symm avoids.2.2
      apply Bool.eq_iff_iff.mpr
      simp only [compactVertices, produces, beq_iff_eq]
      constructor
      · exact Certificate.compactVertex_injective_of_ne
          resultNotRemoved vertexNotRemoved
      · intro same
        subst result
        rfl
  | par first second result =>
      simp [vertices] at avoids
      have resultNotRemoved : result ≠ removed := Ne.symm avoids.2.2
      apply Bool.eq_iff_iff.mpr
      simp only [compactVertices, produces, beq_iff_eq]
      constructor
      · exact Certificate.compactVertex_injective_of_ne
          resultNotRemoved vertexNotRemoved
      · intro same
        subst result
        rfl

theorem usesAsPremise_deleteVertex?_eq_some
    {link compacted : Link} {removed vertex : Vertex}
    (vertexNotRemoved : vertex ≠ removed)
    (deleted : link.deleteVertex? removed = some compacted) :
    compacted.usesAsPremise (Certificate.compactVertex removed vertex) =
      link.usesAsPremise vertex := by
  rcases (deleteVertex?_eq_some_iff link compacted removed).mp deleted with
    ⟨avoids, rfl⟩
  cases link with
  | «axiom» first second => rfl
  | tensor first second result =>
      simp [vertices] at avoids
      have firstNotRemoved : first ≠ removed := Ne.symm avoids.1
      have secondNotRemoved : second ≠ removed := Ne.symm avoids.2.1
      apply Bool.eq_iff_iff.mpr
      simp only [compactVertices, usesAsPremise, premises,
        List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
        beq_iff_eq]
      constructor
      · intro membership
        rcases membership with same | same
        · exact Or.inl (Certificate.compactVertex_injective_of_ne
            vertexNotRemoved firstNotRemoved same)
        · exact Or.inr (Certificate.compactVertex_injective_of_ne
            vertexNotRemoved secondNotRemoved same)
      · intro membership
        rcases membership with rfl | rfl <;> simp
  | par first second result =>
      simp [vertices] at avoids
      have firstNotRemoved : first ≠ removed := Ne.symm avoids.1
      have secondNotRemoved : second ≠ removed := Ne.symm avoids.2.1
      apply Bool.eq_iff_iff.mpr
      simp only [compactVertices, usesAsPremise, premises,
        List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
        beq_iff_eq]
      constructor
      · intro membership
        rcases membership with same | same
        · exact Or.inl (Certificate.compactVertex_injective_of_ne
            vertexNotRemoved firstNotRemoved same)
        · exact Or.inr (Certificate.compactVertex_injective_of_ne
            vertexNotRemoved secondNotRemoved same)
      · intro membership
        rcases membership with rfl | rfl <;> simp

/-- Reindex a link into a listed vertex subset. Links crossing the subset
boundary are rejected. -/
def restrictTo? (vertices : List Vertex) : Link → Option Link
  | .axiom left right => do
      let left' ← vertices.idxOf? left
      let right' ← vertices.idxOf? right
      pure (.axiom left' right')
  | .tensor left right conclusion => do
      let left' ← vertices.idxOf? left
      let right' ← vertices.idxOf? right
      let conclusion' ← vertices.idxOf? conclusion
      pure (.tensor left' right' conclusion')
  | .par left right conclusion => do
      let left' ← vertices.idxOf? left
      let right' ← vertices.idxOf? right
      let conclusion' ← vertices.idxOf? conclusion
      pure (.par left' right' conclusion')

end Link

namespace Edge

def incident (edge : Edge) (vertex : Vertex) : Bool :=
  edge.first == vertex || edge.second == vertex

@[simp] theorem incident_mk (first second vertex : Vertex) :
    (Edge.mk first second).incident vertex =
      (first == vertex || second == vertex) := rfl

def deleteVertex? (removed : Vertex) (edge : Edge) : Option Edge := do
  let first ← Certificate.deleteVertex? removed edge.first
  let second ← Certificate.deleteVertex? removed edge.second
  pure { first, second }

def expandVertex (removed : Vertex) (edge : Edge) : Edge :=
  { first := Certificate.expandVertex removed edge.first
    second := Certificate.expandVertex removed edge.second }

theorem deleteVertex?_eq_some {removed : Vertex} {edge compacted : Edge}
    (accepted : edge.deleteVertex? removed = some compacted) :
    edge.first ≠ removed ∧ edge.second ≠ removed ∧
      compacted = {
        first := Certificate.compactVertex removed edge.first
        second := Certificate.compactVertex removed edge.second } := by
  rcases edge with ⟨first, second⟩
  by_cases firstDeleted : first = removed
  · simp [deleteVertex?, Certificate.deleteVertex?, firstDeleted] at accepted
  · by_cases secondDeleted : second = removed
    · simp [deleteVertex?, Certificate.deleteVertex?, firstDeleted,
        secondDeleted] at accepted
    · simp [deleteVertex?, Certificate.deleteVertex?, firstDeleted,
        secondDeleted] at accepted
      subst compacted
      exact ⟨firstDeleted, secondDeleted, rfl⟩

theorem deleteVertex?_eq_some_of_ne (edge : Edge) (removed : Vertex)
    (firstNotRemoved : edge.first ≠ removed)
    (secondNotRemoved : edge.second ≠ removed) :
    edge.deleteVertex? removed = some {
      first := Certificate.compactVertex removed edge.first
      second := Certificate.compactVertex removed edge.second } := by
  rcases edge with ⟨first, second⟩
  simp [deleteVertex?, Certificate.deleteVertex?, firstNotRemoved,
    secondNotRemoved]

theorem deleteVertex?_isSome (edge : Edge) (removed : Vertex) :
    (edge.deleteVertex? removed).isSome = !edge.incident removed := by
  rcases edge with ⟨first, second⟩
  by_cases firstRemoved : first = removed <;>
  by_cases secondRemoved : second = removed <;>
    simp [deleteVertex?, Certificate.deleteVertex?, incident,
      firstRemoved, secondRemoved]

end Edge

namespace ParChoice

/-- Delete one occurrence from both alternatives of a par switching choice.
The choice survives only when both alternative edges survive. -/
def deleteVertex? (removed : Vertex) (choice : Edge × Edge) :
    Option (Edge × Edge) := do
  let first ← choice.1.deleteVertex? removed
  let second ← choice.2.deleteVertex? removed
  pure (first, second)

end ParChoice

namespace Graph

/-- Delete a graph vertex, drop all incident edges, and compact larger vertex
names. -/
def deleteVertex (graph : Graph) (removed : Vertex) : Graph where
  vertexCount := graph.vertexCount - 1
  edges := graph.edges.filterMap (Edge.deleteVertex? removed)

@[simp] theorem deleteVertex_vertexCount (graph : Graph) (removed : Vertex) :
    (graph.deleteVertex removed).vertexCount = graph.vertexCount - 1 := rfl

def incidentCount (graph : Graph) (vertex : Vertex) : Nat :=
  (graph.edges.filter (·.incident vertex)).length

def Leaf (graph : Graph) (vertex : Vertex) : Prop :=
  vertex < graph.vertexCount ∧ graph.incidentCount vertex = 1

theorem Leaf.incidentEdge_eq {graph : Graph} {vertex : Vertex}
    (leaf : graph.Leaf vertex) {first second : Edge}
    (firstMembership : first ∈ graph.edges)
    (secondMembership : second ∈ graph.edges)
    (firstIncident : first.incident vertex = true)
    (secondIncident : second.incident vertex = true) :
    first = second := by
  have firstFiltered : first ∈ graph.edges.filter (·.incident vertex) := by
    simp [firstMembership, firstIncident]
  have secondFiltered : second ∈ graph.edges.filter (·.incident vertex) := by
    simp [secondMembership, secondIncident]
  rcases List.length_eq_one_iff.mp leaf.2 with ⟨only, filterEquation⟩
  rw [filterEquation] at firstFiltered secondFiltered
  simp at firstFiltered secondFiltered
  exact firstFiltered.trans secondFiltered.symm

theorem Leaf.adjacent_through_eq {graph : Graph} {vertex first second : Vertex}
    (leaf : graph.Leaf vertex)
    (enter : graph.Adjacent first vertex)
    (leave : graph.Adjacent vertex second) :
    first = second := by
  rcases enter with ⟨enterEdge, enterMembership, enterDirection⟩
  rcases leave with ⟨leaveEdge, leaveMembership, leaveDirection⟩
  have enterIncident : enterEdge.incident vertex = true := by
    rcases enterDirection with forward | backward
    · simp [Edge.incident, forward]
    · simp [Edge.incident, backward]
  have leaveIncident : leaveEdge.incident vertex = true := by
    rcases leaveDirection with forward | backward
    · simp [Edge.incident, forward]
    · simp [Edge.incident, backward]
  have sameEdge := leaf.incidentEdge_eq enterMembership leaveMembership
    enterIncident leaveIncident
  subst leaveEdge
  rcases enterDirection with enterForward | enterBackward <;>
  rcases leaveDirection with leaveForward | leaveBackward <;>
    simp_all

theorem Leaf.two_le_vertexCount {graph : Graph} {vertex : Vertex}
    (leaf : graph.Leaf vertex) (bounded : graph.Bounded) :
    2 ≤ graph.vertexCount := by
  rcases List.length_eq_one_iff.mp leaf.2 with ⟨edge, filterEquation⟩
  have filteredMembership : edge ∈ graph.edges.filter (·.incident vertex) := by
    rw [filterEquation]
    simp
  simp only [List.mem_filter] at filteredMembership
  rcases bounded edge filteredMembership.1 with
    ⟨firstInBounds, secondInBounds, distinct⟩
  cases countEquation : graph.vertexCount with
  | zero => simp [countEquation] at firstInBounds
  | succ remaining =>
      cases remaining with
      | zero =>
          have firstZero : edge.first = 0 := by
            simpa [countEquation] using firstInBounds
          have secondZero : edge.second = 0 := by
            simpa [countEquation] using secondInBounds
          exact False.elim (distinct (firstZero.trans secondZero.symm))
      | succ extra => simp

theorem SimpleWalk.finish_mem {graph : Graph} {start finish : Vertex}
    {steps : Nat} {visited : List Vertex}
    (walk : graph.SimpleWalk start steps visited finish) :
    finish ∈ visited := by
  induction walk with
  | refl => simp
  | step prior adjacency fresh ih => simp

theorem SimpleWalk.avoidsLeaf {graph : Graph} {start finish removed : Vertex}
    {steps : Nat} {visited : List Vertex}
    (walk : graph.SimpleWalk start steps visited finish)
    (leaf : graph.Leaf removed)
    (startNotRemoved : start ≠ removed)
    (finishNotRemoved : finish ≠ removed) :
    removed ∉ visited := by
  induction walk with
  | refl => simpa [eq_comm] using startNotRemoved
  | @step priorSteps priorVisited middle current prior adjacency fresh ih =>
      have middleNotRemoved : middle ≠ removed := by
        intro middleIsRemoved
        subst middle
        cases prior with
        | refl => exact startNotRemoved rfl
        | @step earlierSteps earlierVisited previous _ earlier enter
            removedFresh =>
            have sameEndpoint := leaf.adjacent_through_eq enter adjacency
            subst current
            exact fresh (by
              simp only [List.mem_append, List.mem_singleton]
              exact .inl earlier.finish_mem)
      have priorAvoids := ih middleNotRemoved
      intro membership
      simp only [List.mem_append, List.mem_singleton] at membership
      rcases membership with priorMembership | finalEqual
      · exact priorAvoids priorMembership
      · exact finishNotRemoved finalEqual.symm

theorem deleteVertex_edges_length_add_incidentCount
    (graph : Graph) (removed : Vertex) :
    (graph.deleteVertex removed).edges.length + graph.incidentCount removed =
      graph.edges.length := by
  cases graph with
  | mk vertexCount edges =>
      simp only [deleteVertex, incidentCount]
      induction edges with
      | nil => rfl
      | cons edge rest ih =>
          rcases edge with ⟨first, second⟩
          by_cases firstDeleted : first = removed <;>
          by_cases secondDeleted : second = removed <;>
            simp [Edge.deleteVertex?,
              Certificate.deleteVertex?, firstDeleted, secondDeleted,
              ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem IsTree.deleteVertex_edgeCount {graph : Graph} (tree : graph.IsTree)
    {removed : Vertex} (leaf : graph.Leaf removed) :
    (graph.deleteVertex removed).edges.length + 1 =
      (graph.deleteVertex removed).vertexCount := by
  have accounting := graph.deleteVertex_edges_length_add_incidentCount removed
  rw [leaf.2] at accounting
  have originalCount := tree.2.2
  simp only [deleteVertex_vertexCount]
  omega

/-- Adjacency in the compacted graph is exactly adjacency between the embedded
old vertex names. -/
theorem adjacent_deleteVertex_iff (graph : Graph) (removed : Vertex)
    (left right : Vertex) :
    (graph.deleteVertex removed).Adjacent left right ↔
      graph.Adjacent (Certificate.expandVertex removed left)
        (Certificate.expandVertex removed right) := by
  constructor
  · rintro ⟨compacted, compactedMembership, direction⟩
    change compacted ∈ graph.edges.filterMap (Edge.deleteVertex? removed) at compactedMembership
    simp only [List.mem_filterMap] at compactedMembership
    rcases compactedMembership with
      ⟨edge, edgeMembership, compactedEquation⟩
    rcases Edge.deleteVertex?_eq_some compactedEquation with
      ⟨firstNotRemoved, secondNotRemoved, rfl⟩
    refine ⟨edge, edgeMembership, ?_⟩
    rcases direction with forward | backward
    · left
      constructor
      · have expanded := congrArg (Certificate.expandVertex removed) forward.1
        simpa [Certificate.expandVertex_compactVertex_of_ne firstNotRemoved]
          using expanded
      · have expanded := congrArg (Certificate.expandVertex removed) forward.2
        simpa [Certificate.expandVertex_compactVertex_of_ne secondNotRemoved]
          using expanded
    · right
      constructor
      · have expanded := congrArg (Certificate.expandVertex removed) backward.1
        simpa [Certificate.expandVertex_compactVertex_of_ne firstNotRemoved]
          using expanded
      · have expanded := congrArg (Certificate.expandVertex removed) backward.2
        simpa [Certificate.expandVertex_compactVertex_of_ne secondNotRemoved]
          using expanded
  · rintro ⟨edge, edgeMembership, direction⟩
    have firstNotRemoved : edge.first ≠ removed := by
      intro same
      rcases direction with forward | backward
      · exact Certificate.expandVertex_ne removed left (forward.1 ▸ same)
      · exact Certificate.expandVertex_ne removed right (backward.1 ▸ same)
    have secondNotRemoved : edge.second ≠ removed := by
      intro same
      rcases direction with forward | backward
      · exact Certificate.expandVertex_ne removed right (forward.2 ▸ same)
      · exact Certificate.expandVertex_ne removed left (backward.2 ▸ same)
    let compacted : Edge := {
      first := Certificate.compactVertex removed edge.first
      second := Certificate.compactVertex removed edge.second }
    refine ⟨compacted, ?_, ?_⟩
    · change compacted ∈ graph.edges.filterMap (Edge.deleteVertex? removed)
      simp only [List.mem_filterMap]
      exact ⟨edge, edgeMembership,
        edge.deleteVertex?_eq_some_of_ne removed firstNotRemoved
          secondNotRemoved⟩
    · rcases direction with forward | backward
      · left
        constructor
        · change Certificate.compactVertex removed edge.first = left
          simp [forward.1]
        · change Certificate.compactVertex removed edge.second = right
          simp [forward.2]
      · right
        constructor
        · change Certificate.compactVertex removed edge.first = right
          simp [backward.1]
        · change Certificate.compactVertex removed edge.second = left
          simp [backward.2]

theorem SimpleWalk.deleteVertex {graph : Graph}
    {start finish removed : Vertex} {steps : Nat} {visited : List Vertex}
    (walk : graph.SimpleWalk start steps visited finish)
    (avoids : removed ∉ visited) :
    (graph.deleteVertex removed).Walk
      (Certificate.compactVertex removed start)
      (Certificate.compactVertex removed finish) := by
  induction walk with
  | refl => exact .refl _
  | @step priorSteps priorVisited middle current prior adjacency fresh ih =>
      have priorAvoids : removed ∉ priorVisited := by
        intro membership
        exact avoids (by simp [membership])
      have currentNotRemoved : current ≠ removed := by
        intro same
        subst current
        exact avoids (by simp)
      have middleNotRemoved : middle ≠ removed := by
        intro same
        subst middle
        exact priorAvoids prior.finish_mem
      have compactedAdjacency :
          (graph.deleteVertex removed).Adjacent
            (Certificate.compactVertex removed middle)
            (Certificate.compactVertex removed current) := by
        apply (graph.adjacent_deleteVertex_iff removed _ _).mpr
        simpa [Certificate.expandVertex_compactVertex_of_ne middleNotRemoved,
          Certificate.expandVertex_compactVertex_of_ne currentNotRemoved]
          using adjacency
      exact .step (ih priorAvoids) compactedAdjacency

theorem Walk.expandDelete {graph : Graph} {removed start finish : Vertex}
    (walk : (graph.deleteVertex removed).Walk start finish) :
    graph.Walk (Certificate.expandVertex removed start)
      (Certificate.expandVertex removed finish) := by
  induction walk with
  | refl => exact .refl _
  | step prior adjacency ih =>
      exact .step ih
        ((graph.adjacent_deleteVertex_iff removed _ _).mp adjacency)

theorem Connected.deleteLeaf {graph : Graph} (connected : graph.Connected)
    (bounded : graph.Bounded) {removed : Vertex} (leaf : graph.Leaf removed) :
    (graph.deleteVertex removed).Connected := by
  have remainingPositive : 0 < graph.vertexCount - 1 := by
    have atLeastTwo := leaf.two_le_vertexCount bounded
    omega
  refine ⟨by simpa using remainingPositive, ?_⟩
  intro vertex vertexInBounds
  have oldStartInBounds :
      Certificate.expandVertex removed 0 < graph.vertexCount :=
    Certificate.expandVertex_lt leaf.1 remainingPositive
  have oldFinishInBounds :
      Certificate.expandVertex removed vertex < graph.vertexCount :=
    Certificate.expandVertex_lt leaf.1 (by simpa using vertexInBounds)
  have between : graph.Walk
      (Certificate.expandVertex removed 0)
      (Certificate.expandVertex removed vertex) :=
    (connected.2 _ oldStartInBounds).reverse.trans
      (connected.2 _ oldFinishInBounds)
  rcases between.toSimple with ⟨steps, visited, simple⟩
  have avoids := simple.avoidsLeaf leaf
    (Certificate.expandVertex_ne removed 0)
    (Certificate.expandVertex_ne removed vertex)
  simpa using simple.deleteVertex avoids

theorem Bounded.deleteVertex {graph : Graph} (bounded : graph.Bounded)
    {removed : Vertex} (removedInBounds : removed < graph.vertexCount) :
    (graph.deleteVertex removed).Bounded := by
  intro compacted compactedMembership
  change compacted ∈ graph.edges.filterMap (Edge.deleteVertex? removed) at compactedMembership
  simp only [List.mem_filterMap] at compactedMembership
  rcases compactedMembership with
    ⟨edge, edgeMembership, compactedEquation⟩
  rcases Edge.deleteVertex?_eq_some compactedEquation with
    ⟨firstNotRemoved, secondNotRemoved, rfl⟩
  rcases bounded edge edgeMembership with
    ⟨firstInBounds, secondInBounds, endpointsDistinct⟩
  refine ⟨Certificate.compactVertex_lt removedInBounds firstInBounds
      firstNotRemoved,
    Certificate.compactVertex_lt removedInBounds secondInBounds
      secondNotRemoved, ?_⟩
  intro compactedEqual
  have expandedEqual := congrArg (Certificate.expandVertex removed)
    compactedEqual
  rw [Certificate.expandVertex_compactVertex_of_ne firstNotRemoved,
    Certificate.expandVertex_compactVertex_of_ne secondNotRemoved] at expandedEqual
  exact endpointsDistinct expandedEqual

theorem IsTree.deleteLeaf {graph : Graph} (tree : graph.IsTree)
    {removed : Vertex} (leaf : graph.Leaf removed) :
    (graph.deleteVertex removed).IsTree :=
  ⟨tree.1.deleteVertex leaf.1,
    tree.2.1.deleteLeaf tree.1 leaf,
    tree.deleteVertex_edgeCount leaf⟩

end Graph

namespace Certificate

/-- The unswitched occurrence graph contains both premise edges of every
logical link. It is used only to discover candidate tensor components; the
authoritative correctness definition continues to quantify over switchings. -/
def fullEdges (certificate : Certificate) : List Edge :=
  certificate.links.flatMap fun
    | .axiom left right => [{ first := left, second := right }]
    | .tensor left right conclusion =>
        [{ first := left, second := conclusion },
         { first := right, second := conclusion }]
    | .par left right conclusion =>
        [{ first := left, second := conclusion },
         { first := right, second := conclusion }]

def fullGraphWithoutVertex (certificate : Certificate)
    (removed : Vertex) : Graph where
  vertexCount := certificate.formulas.size
  edges := certificate.fullEdges.filter fun edge => !edge.incident removed

/-- Induce a locally numbered certificate on a listed subset and an explicitly
chosen boundary. Crossing links are omitted, so callers must separately prove
or check that the proposed partition covers every remaining link. -/
def restrictTo? (certificate : Certificate) (vertices boundary : List Vertex) :
    Option Certificate := do
  let formulas ← vertices.mapM certificate.formula?
  let conclusions ← boundary.mapM vertices.idxOf?
  pure {
    formulas := formulas.toArray
    links := certificate.links.filterMap (Link.restrictTo? vertices)
    conclusions }

/-- A par link is terminal when its conclusion occurrence is on the ordered
public boundary. Such a link is the unary inverse-rule case of
sequentialization. -/
def TerminalPar (certificate : Certificate)
    (left right conclusion : Vertex) : Prop :=
  Link.par left right conclusion ∈ certificate.links ∧
    conclusion ∈ certificate.conclusions

/-- A tensor link is terminal when its conclusion occurrence is on the public
boundary. Sequentialization additionally needs the tensor to split the
remaining proof structure into two correct components. -/
def TerminalTensor (certificate : Certificate)
    (left right conclusion : Vertex) : Prop :=
  Link.tensor left right conclusion ∈ certificate.links ∧
    conclusion ∈ certificate.conclusions

theorem LinkWellFormed.par_conclusionFormula
    {certificate : Certificate} {left right conclusion : Vertex}
    (wellFormed : certificate.LinkWellFormed (.par left right conclusion)) :
    ∃ leftFormula rightFormula,
      certificate.formula? conclusion =
        some (.par leftFormula rightFormula) := by
  rcases wellFormed with ⟨_, _, _, _, _, _, typing⟩
  cases leftEquation : certificate.formula? left with
  | none => simp [leftEquation] at typing
  | some leftFormula =>
      cases rightEquation : certificate.formula? right with
      | none => simp [leftEquation, rightEquation] at typing
      | some rightFormula =>
          cases conclusionEquation : certificate.formula? conclusion with
          | none =>
              simp [leftEquation, rightEquation, conclusionEquation] at typing
          | some conclusionFormula =>
              simp [leftEquation, rightEquation, conclusionEquation] at typing
              subst conclusionFormula
              exact ⟨leftFormula, rightFormula, rfl⟩

theorem LinkWellFormed.axiom_endpointFormula
    {certificate : Certificate} {left right vertex : Vertex}
    (wellFormed : certificate.LinkWellFormed (.axiom left right))
    (endpoint : vertex = left ∨ vertex = right) :
    ∃ name positive,
      certificate.formula? vertex = some (.atom name positive) := by
  rcases wellFormed with ⟨_, _, _, typing⟩
  cases leftEquation : certificate.formula? left with
  | none => simp [leftEquation] at typing
  | some leftFormula =>
      cases leftFormula with
      | tensor first second => simp [leftEquation] at typing
      | par first second => simp [leftEquation] at typing
      | atom name positive =>
          cases rightEquation : certificate.formula? right with
          | none => simp [leftEquation, rightEquation] at typing
          | some rightFormula =>
              simp [leftEquation, rightEquation] at typing
              rcases endpoint with rfl | rfl
              · exact ⟨name, positive, by simpa using leftEquation⟩
              · subst rightFormula
                exact ⟨name, !positive, by
                  simpa [Formula.dual] using rightEquation⟩

namespace TerminalPar

theorem ownership {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    certificate.producerCount conclusion = 1 ∧
      certificate.parentUseCount conclusion = 0 ∧
      ∃ leftFormula rightFormula,
        certificate.formula? conclusion =
          some (.par leftFormula rightFormula) := by
  rcases structural with ⟨_, _, conclusionsInBounds, _, linksWellFormed,
    nodesWellFormed⟩
  have terminalWellFormed := linksWellFormed _ terminal.1
  rcases terminalWellFormed.par_conclusionFormula with
    ⟨leftFormula, rightFormula, conclusionFormula⟩
  have node := nodesWellFormed conclusion
    (conclusionsInBounds conclusion terminal.2)
  simp [NodeWellFormed, conclusionFormula, terminal.2] at node
  exact ⟨node.1, node.2, leftFormula, rightFormula, conclusionFormula⟩

theorem premises_not_conclusions
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    left ∉ certificate.conclusions ∧ right ∉ certificate.conclusions := by
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  rcases terminalWellFormed with
    ⟨_, _, _, leftInBounds, rightInBounds, _, _⟩
  constructor
  · intro leftConclusion
    have node := structural.2.2.2.2.2 left leftInBounds
    have parentZero := node.2
    simp [leftConclusion] at parentZero
    change (certificate.links.filter (·.usesAsPremise left)).length = 0 at parentZero
    exact false_of_mem_filter_length_zero parentZero terminal.1
      (by simp [Link.usesAsPremise, Link.premises])
  · intro rightConclusion
    have node := structural.2.2.2.2.2 right rightInBounds
    have parentZero := node.2
    simp [rightConclusion] at parentZero
    change (certificate.links.filter (·.usesAsPremise right)).length = 0 at parentZero
    exact false_of_mem_filter_length_zero parentZero terminal.1
      (by simp [Link.usesAsPremise, Link.premises])

theorem producer_unique {certificate : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    {link : Link} (membership : link ∈ certificate.links)
    (produces : link.produces conclusion = true) :
    link = .par left right conclusion := by
  have producerCount := (TerminalPar.ownership structural terminal).1
  change (certificate.links.filter (·.produces conclusion)).length = 1 at producerCount
  apply eq_of_mem_filter_length_one
    (predicate := (·.produces conclusion))
    producerCount
    membership produces terminal.1
  simp [Link.produces]

theorem no_parentUse {certificate : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    {link : Link} (membership : link ∈ certificate.links)
    (uses : link.usesAsPremise conclusion = true) : False := by
  have parentCount := (TerminalPar.ownership structural terminal).2.1
  change (certificate.links.filter (·.usesAsPremise conclusion)).length = 0 at parentCount
  exact false_of_mem_filter_length_zero
    (predicate := (·.usesAsPremise conclusion))
    parentCount membership uses

theorem unique_incident {certificate : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    {link : Link} (membership : link ∈ certificate.links)
    (incident : conclusion ∈ link.vertices) :
    link = .par left right conclusion := by
  have conclusionFormula :=
    (TerminalPar.ownership structural terminal).2.2
  cases link with
  | «axiom» first second =>
      have endpoint : conclusion = first ∨ conclusion = second := by
        simpa [Link.vertices] using incident
      have axiomWellFormed := structural.2.2.2.2.1 _ membership
      rcases axiomWellFormed.axiom_endpointFormula endpoint with
        ⟨name, positive, atomFormula⟩
      rcases conclusionFormula with
        ⟨leftFormula, rightFormula, parFormula⟩
      rw [parFormula] at atomFormula
      cases atomFormula
  | tensor first second result =>
      simp [Link.vertices] at incident
      rcases incident with same | same | same
      · subst first
        exact False.elim (TerminalPar.no_parentUse structural terminal
          membership (by simp [Link.usesAsPremise, Link.premises]))
      · subst second
        exact False.elim (TerminalPar.no_parentUse structural terminal
          membership (by simp [Link.usesAsPremise, Link.premises]))
      · subst result
        exact TerminalPar.producer_unique structural terminal membership
          (by simp [Link.produces])
  | par first second result =>
      simp [Link.vertices] at incident
      rcases incident with same | same | same
      · subst first
        exact False.elim (TerminalPar.no_parentUse structural terminal
          membership (by simp [Link.usesAsPremise, Link.premises]))
      · subst second
        exact False.elim (TerminalPar.no_parentUse structural terminal
          membership (by simp [Link.usesAsPremise, Link.premises]))
      · subst result
        exact TerminalPar.producer_unique structural terminal membership
          (by simp [Link.produces])

theorem deletion_none_iff_eq
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    {link : Link} (membership : link ∈ certificate.links) :
    link.deleteVertex? conclusion = none ↔
      link = .par left right conclusion := by
  constructor
  · intro deleted
    exact TerminalPar.unique_incident structural terminal membership
      ((Link.deleteVertex?_eq_none_iff link conclusion).mp deleted)
  · intro same
    subst link
    simp [Link.deleteVertex?, Certificate.deleteVertex?]

end TerminalPar

theorem ChoiceSelection.filter_length_eq_of_pair_agreement
    {choices : List (Edge × Edge)} {selected : List Edge}
    (selection : ChoiceSelection choices selected)
    (predicate : Edge → Bool)
    (pairAgreement : ∀ choice ∈ choices,
      predicate choice.1 = predicate choice.2) :
    (selected.filter predicate).length =
      (choices.filter fun choice => predicate choice.1).length := by
  induction selection with
  | nil => rfl
  | @left left right rest selected prior ih =>
      have restAgreement : ∀ choice ∈ rest,
          predicate choice.1 = predicate choice.2 := by
        intro choice membership
        exact pairAgreement choice (by simp [membership])
      by_cases accepted : predicate left = true <;>
        simp [accepted, ih restAgreement]
  | @right left right rest selected prior ih =>
      have headAgreement : predicate left = predicate right :=
        pairAgreement (left, right) (by simp)
      have restAgreement : ∀ choice ∈ rest,
          predicate choice.1 = predicate choice.2 := by
        intro choice membership
        exact pairAgreement choice (by simp [membership])
      by_cases accepted : predicate left = true <;>
        simp [accepted, ← headAgreement, ih restAgreement]

theorem ChoiceSelection.liftDelete
    {removed : Vertex} {choices : List (Edge × Edge)} {selected : List Edge}
    (selection : ChoiceSelection
      (choices.filterMap (ParChoice.deleteVertex? removed)) selected)
    (agreement : ∀ choice ∈ choices,
      (choice.1.deleteVertex? removed).isSome =
        (choice.2.deleteVertex? removed).isSome) :
    ∃ lifted,
      ChoiceSelection choices lifted ∧
      selected = lifted.filterMap (Edge.deleteVertex? removed) := by
  induction choices generalizing selected with
  | nil =>
      cases selection
      exact ⟨[], .nil, rfl⟩
  | cons choice rest ih =>
      have headAgreement := agreement choice (by simp)
      have restAgreement : ∀ candidate ∈ rest,
          (candidate.1.deleteVertex? removed).isSome =
            (candidate.2.deleteVertex? removed).isSome := by
        intro candidate membership
        exact agreement candidate (by simp [membership])
      cases firstEquation : choice.1.deleteVertex? removed with
      | none =>
          have secondNone : choice.2.deleteVertex? removed = none := by
            cases secondEquation : choice.2.deleteVertex? removed with
            | none => rfl
            | some second =>
                simp [firstEquation, secondEquation] at headAgreement
          have restSelection : ChoiceSelection
              (rest.filterMap (ParChoice.deleteVertex? removed)) selected := by
            simpa [ParChoice.deleteVertex?, firstEquation, secondNone]
              using selection
          rcases ih restSelection restAgreement with
            ⟨lifted, liftedSelection, selectedEquation⟩
          exact ⟨choice.1 :: lifted, .left liftedSelection, by
            simp [firstEquation, selectedEquation]⟩
      | some first =>
          have secondSome : ∃ second,
              choice.2.deleteVertex? removed = some second := by
            cases secondEquation : choice.2.deleteVertex? removed with
            | none => simp [firstEquation, secondEquation] at headAgreement
            | some second => exact ⟨second, rfl⟩
          rcases secondSome with ⟨second, secondEquation⟩
          have expandedSelection : ChoiceSelection
              ((first, second) ::
                rest.filterMap (ParChoice.deleteVertex? removed)) selected := by
            simpa [ParChoice.deleteVertex?, firstEquation, secondEquation]
              using selection
          cases expandedSelection with
          | left prior =>
              rcases ih prior restAgreement with
                ⟨lifted, liftedSelection, selectedEquation⟩
              exact ⟨choice.1 :: lifted, .left liftedSelection, by
                simp [firstEquation, selectedEquation]⟩
          | right prior =>
              rcases ih prior restAgreement with
                ⟨lifted, liftedSelection, selectedEquation⟩
              exact ⟨choice.2 :: lifted, .right liftedSelection, by
                simp [secondEquation, selectedEquation]⟩

theorem TerminalPar.parChoice_incident_agreement
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    {choice : Edge × Edge} (membership : choice ∈ certificate.parChoices) :
    choice.1.incident conclusion = choice.2.incident conclusion := by
  simp only [parChoices, List.mem_filterMap] at membership
  rcases membership with ⟨link, linkMembership, emitted⟩
  cases link with
  | «axiom» first second => simp at emitted
  | tensor first second result => simp at emitted
  | par first second result =>
      simp at emitted
      subst choice
      have firstNotConclusion : first ≠ conclusion := by
        intro same
        subst first
        exact TerminalPar.no_parentUse structural terminal linkMembership
          (by simp [Link.usesAsPremise, Link.premises])
      have secondNotConclusion : second ≠ conclusion := by
        intro same
        subst second
        exact TerminalPar.no_parentUse structural terminal linkMembership
          (by simp [Link.usesAsPremise, Link.premises])
      have firstBoolean : (first == conclusion) = false :=
        beq_eq_false_iff_ne.mpr firstNotConclusion
      have secondBoolean : (second == conclusion) = false :=
        beq_eq_false_iff_ne.mpr secondNotConclusion
      simp [Edge.incident, firstBoolean, secondBoolean]

theorem TerminalPar.parChoice_deletion_agreement
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    {choice : Edge × Edge} (membership : choice ∈ certificate.parChoices) :
    (choice.1.deleteVertex? conclusion).isSome =
      (choice.2.deleteVertex? conclusion).isSome := by
  rw [Edge.deleteVertex?_isSome, Edge.deleteVertex?_isSome,
    TerminalPar.parChoice_incident_agreement structural terminal membership]

theorem TerminalPar.parChoices_incidentCount
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    (certificate.parChoices.filter fun choice =>
      choice.1.incident conclusion).length =
        certificate.producerCount conclusion := by
  let emitChoice : Link → Option (Edge × Edge) := fun
    | .par first second result =>
        some ({ first := first, second := result },
          { first := second, second := result })
    | _ => none
  change
    ((certificate.links.filterMap emitChoice).filter fun choice =>
      choice.1.incident conclusion).length =
        (certificate.links.filter (·.produces conclusion)).length
  suffices general : ∀ links : List Link,
      (∀ link ∈ links, link ∈ certificate.links) →
      ((links.filterMap emitChoice).filter fun choice =>
        choice.1.incident conclusion).length =
        (links.filter (·.produces conclusion)).length by
    exact general certificate.links (by simp)
  intro links subset
  induction links with
  | nil => rfl
  | cons head tail ih =>
      have headMembership : head ∈ certificate.links :=
        subset head (by simp)
      have tailSubset : ∀ link ∈ tail, link ∈ certificate.links := by
        intro link membership
        exact subset link (by simp [membership])
      have tailEquality := ih tailSubset
      cases head with
      | «axiom» first second => simpa [emitChoice, Link.produces] using tailEquality
      | tensor first second result =>
          have resultNotConclusion : result ≠ conclusion := by
            intro same
            subst result
            have impossible := TerminalPar.producer_unique structural terminal
              headMembership (by simp [Link.produces])
            cases impossible
          simpa [emitChoice, Link.produces, resultNotConclusion] using tailEquality
      | par first second result =>
          simp only [emitChoice, Edge.incident, Link.produces] at tailEquality
          have firstNotConclusion : first ≠ conclusion := by
            intro same
            subst first
            exact TerminalPar.no_parentUse structural terminal headMembership
              (by simp [Link.usesAsPremise, Link.premises])
          have firstBoolean : (first == conclusion) = false :=
            beq_eq_false_iff_ne.mpr firstNotConclusion
          cases resultBoolean : (result == conclusion) <;>
            simp [emitChoice, Link.produces, Edge.incident,
              firstBoolean, resultBoolean, tailEquality]

theorem TerminalPar.selected_incidentCount
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    {selected : List Edge}
    (selection : ChoiceSelection certificate.parChoices selected) :
    (selected.filter (·.incident conclusion)).length = 1 := by
  rw [selection.filter_length_eq_of_pair_agreement
    (·.incident conclusion) (by
      intro choice membership
      exact TerminalPar.parChoice_incident_agreement structural terminal
        membership)]
  rw [TerminalPar.parChoices_incidentCount structural terminal]
  exact (TerminalPar.ownership structural terminal).1

theorem TerminalPar.fixedEdges_incidentCount
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    (certificate.fixedEdges.filter (·.incident conclusion)).length = 0 := by
  let emitFixed : Link → List Edge := fun
    | .axiom first second => [{ first, second }]
    | .tensor first second result =>
        [{ first := first, second := result },
         { first := second, second := result }]
    | .par _ _ _ => []
  change
    ((certificate.links.flatMap emitFixed).filter
      (·.incident conclusion)).length = 0
  suffices general : ∀ links : List Link,
      (∀ link ∈ links, link ∈ certificate.links) →
      ((links.flatMap emitFixed).filter
        (·.incident conclusion)).length = 0 by
    exact general certificate.links (by simp)
  intro links subset
  induction links with
  | nil => rfl
  | cons head tail ih =>
      have headMembership : head ∈ certificate.links :=
        subset head (by simp)
      have tailSubset : ∀ link ∈ tail, link ∈ certificate.links := by
        intro link membership
        exact subset link (by simp [membership])
      have tailEquality := ih tailSubset
      cases head with
      | «axiom» first second =>
          have firstNotConclusion : first ≠ conclusion := by
            intro same
            subst first
            have impossible := TerminalPar.unique_incident structural terminal
              headMembership (by simp [Link.vertices])
            cases impossible
          have secondNotConclusion : second ≠ conclusion := by
            intro same
            subst second
            have impossible := TerminalPar.unique_incident structural terminal
              headMembership (by simp [Link.vertices])
            cases impossible
          have firstBoolean : (first == conclusion) = false :=
            beq_eq_false_iff_ne.mpr firstNotConclusion
          have secondBoolean : (second == conclusion) = false :=
            beq_eq_false_iff_ne.mpr secondNotConclusion
          simpa [emitFixed, Edge.incident, firstBoolean, secondBoolean]
            using tailEquality
      | tensor first second result =>
          have firstNotConclusion : first ≠ conclusion := by
            intro same
            subst first
            exact TerminalPar.no_parentUse structural terminal headMembership
              (by simp [Link.usesAsPremise, Link.premises])
          have secondNotConclusion : second ≠ conclusion := by
            intro same
            subst second
            exact TerminalPar.no_parentUse structural terminal headMembership
              (by simp [Link.usesAsPremise, Link.premises])
          have resultNotConclusion : result ≠ conclusion := by
            intro same
            subst result
            have impossible := TerminalPar.producer_unique structural terminal
              headMembership (by simp [Link.produces])
            cases impossible
          have firstBoolean : (first == conclusion) = false :=
            beq_eq_false_iff_ne.mpr firstNotConclusion
          have secondBoolean : (second == conclusion) = false :=
            beq_eq_false_iff_ne.mpr secondNotConclusion
          have resultBoolean : (result == conclusion) = false :=
            beq_eq_false_iff_ne.mpr resultNotConclusion
          simpa [emitFixed, Edge.incident, firstBoolean, secondBoolean,
            resultBoolean] using tailEquality
      | par first second result => simpa [emitFixed] using tailEquality

theorem TerminalPar.graphForSelection_leaf
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    {selected : List Edge}
    (selection : ChoiceSelection certificate.parChoices selected) :
    (certificate.graphForSelection selected).Leaf conclusion := by
  constructor
  · exact structural.2.2.1 conclusion terminal.2
  · unfold Graph.incidentCount
    change ((certificate.fixedEdges ++ selected).filter
      (·.incident conclusion)).length = 1
    rw [List.filter_append, List.length_append,
      TerminalPar.fixedEdges_incidentCount structural terminal,
      TerminalPar.selected_incidentCount structural terminal selection]

/-- Executable list of terminal par links. It is only a candidate finder; the
subnet construction and preservation theorem remain proof obligations. -/
def terminalPars (certificate : Certificate) :
    List (Vertex × Vertex × Vertex) :=
  certificate.links.filterMap fun
    | .par left right conclusion =>
        if conclusion ∈ certificate.conclusions then
          some (left, right, conclusion)
        else
          none
    | _ => none

def terminalTensors (certificate : Certificate) :
    List (Vertex × Vertex × Vertex) :=
  certificate.links.filterMap fun
    | .tensor left right conclusion =>
        if conclusion ∈ certificate.conclusions then
          some (left, right, conclusion)
        else
          none
    | _ => none

/-- Candidate inverse of a terminal par rule. The produced premise removes the
par conclusion occurrence and its incident link, compacts all vertex names,
and puts the two premises at the tail of the ordered boundary. This function
does not itself assert preservation; `peelTerminalParChecked?` supplies the
safe executable boundary and the general preservation theorem is the next
formal obligation. -/
def peelTerminalParCandidate? (certificate : Certificate)
    (left right conclusion : Vertex) : Option Certificate := do
  if !certificate.links.contains (.par left right conclusion) then none
  if !certificate.conclusions.contains conclusion then none
  let left' ← deleteVertex? conclusion left
  let right' ← deleteVertex? conclusion right
  let context ← (certificate.conclusions.filter (· != conclusion)).mapM
    (deleteVertex? conclusion)
  pure {
    formulas := certificate.formulas.eraseIdxIfInBounds conclusion
    links := certificate.links.filterMap (Link.deleteVertex? conclusion)
    conclusions := context ++ [left', right'] }

/-- Proposition-friendly form of terminal-par peeling. It agrees with the
optional candidate on every structurally well-formed terminal par. -/
def peelTerminalPar (certificate : Certificate)
    (left right conclusion : Vertex) : Certificate where
  formulas := certificate.formulas.eraseIdxIfInBounds conclusion
  links := certificate.links.filterMap (Link.deleteVertex? conclusion)
  conclusions :=
    (certificate.conclusions.filter (· != conclusion)).map
      (compactVertex conclusion) ++
    [compactVertex conclusion left, compactVertex conclusion right]

theorem mapM_deleteVertex?_eq_of_avoids (removed : Vertex)
    (values : List Vertex)
    (avoids : ∀ vertex ∈ values, vertex ≠ removed) :
    values.mapM (deleteVertex? removed) =
      some (values.map (compactVertex removed)) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      have headNotRemoved := avoids head (by simp)
      have tailAvoids : ∀ vertex ∈ tail, vertex ≠ removed := by
        intro vertex membership
        exact avoids vertex (by simp [membership])
      simp [deleteVertex?_eq_some_of_ne headNotRemoved, ih tailAvoids]

theorem peelTerminalParCandidate?_eq_some
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    certificate.peelTerminalParCandidate? left right conclusion =
      some (certificate.peelTerminalPar left right conclusion) := by
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  rcases terminalWellFormed with
    ⟨_, leftNotConclusion, rightNotConclusion, _, _, _, _⟩
  have filteredAvoids : ∀ vertex ∈
      certificate.conclusions.filter (· != conclusion),
      vertex ≠ conclusion := by
    intro vertex membership
    simp only [List.mem_filter] at membership
    simpa using membership.2
  have contextMap := mapM_deleteVertex?_eq_of_avoids conclusion
    (certificate.conclusions.filter (· != conclusion)) filteredAvoids
  simp [peelTerminalParCandidate?, peelTerminalPar, terminal.1, terminal.2,
    deleteVertex?_eq_some_of_ne leftNotConclusion,
    deleteVertex?_eq_some_of_ne rightNotConclusion,
    contextMap]

theorem peelTerminalPar_formula?_compact
    {certificate : Certificate} {left right conclusion vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    (vertexNotConclusion : vertex ≠ conclusion) :
    (certificate.peelTerminalPar left right conclusion).formula?
      (compactVertex conclusion vertex) = certificate.formula? vertex := by
  have conclusionInBounds := structural.2.2.1 conclusion terminal.2
  by_cases before : vertex < conclusion
  · simp [peelTerminalPar, formula?, Array.eraseIdxIfInBounds,
      conclusionInBounds, compactVertex, before, Array.getElem?_eraseIdx]
  · have conclusionLeVertex : conclusion ≤ vertex := Nat.le_of_not_gt before
    have conclusionNotVertex : conclusion ≠ vertex := Ne.symm vertexNotConclusion
    have after : conclusion < vertex :=
      Nat.lt_of_le_of_ne conclusionLeVertex conclusionNotVertex
    have compactAtOrAfter : conclusion ≤ vertex - 1 :=
      Nat.le_sub_one_of_lt after
    have compactNotBefore : ¬vertex - 1 < conclusion :=
      Nat.not_lt.mpr compactAtOrAfter
    have vertexPositive : 1 ≤ vertex :=
      Nat.succ_le_of_lt (Nat.zero_lt_of_lt after)
    have restore : vertex - 1 + 1 = vertex :=
      Nat.sub_add_cancel vertexPositive
    simp [peelTerminalPar, formula?, Array.eraseIdxIfInBounds,
      conclusionInBounds, compactVertex, before, Array.getElem?_eraseIdx,
      compactNotBefore, restore]

theorem peelTerminalPar_conclusions_nodup
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    (certificate.peelTerminalPar left right conclusion).conclusions.Nodup := by
  let remaining := certificate.conclusions.filter (· != conclusion)
  let context := remaining.map (compactVertex conclusion)
  have originalNodup : certificate.conclusions.Nodup :=
    nodup_of_eraseDups_length_eq structural.2.2.2.1
  have remainingNodup : remaining.Nodup :=
    List.filter_sublist.nodup originalNodup
  have contextNodup : context.Nodup := by
    apply nodup_map_of_injective_on remainingNodup
    intro first firstMembership second secondMembership same
    have firstNotConclusion : first ≠ conclusion := by
      have filtered := List.mem_filter.mp firstMembership
      simpa using filtered.2
    have secondNotConclusion : second ≠ conclusion := by
      have filtered := List.mem_filter.mp secondMembership
      simpa using filtered.2
    exact compactVertex_injective_of_ne firstNotConclusion
      secondNotConclusion same
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  rcases terminalWellFormed with
    ⟨leftNotRight, leftNotConclusion, rightNotConclusion, _, _, _, _⟩
  have premiseBoundaries := TerminalPar.premises_not_conclusions
    structural terminal
  have compactLeftFresh : compactVertex conclusion left ∉ context := by
    intro membership
    rcases List.mem_map.mp membership with
      ⟨vertex, vertexMembership, same⟩
    have filtered := List.mem_filter.mp vertexMembership
    have vertexNotConclusion : vertex ≠ conclusion := by
      simpa using filtered.2
    have oldSame := compactVertex_injective_of_ne vertexNotConclusion
      leftNotConclusion same
    subst vertex
    exact premiseBoundaries.1 filtered.1
  have compactRightFresh : compactVertex conclusion right ∉ context := by
    intro membership
    rcases List.mem_map.mp membership with
      ⟨vertex, vertexMembership, same⟩
    have filtered := List.mem_filter.mp vertexMembership
    have vertexNotConclusion : vertex ≠ conclusion := by
      simpa using filtered.2
    have oldSame := compactVertex_injective_of_ne vertexNotConclusion
      rightNotConclusion same
    subst vertex
    exact premiseBoundaries.2 filtered.1
  have compactDistinct :
      compactVertex conclusion left ≠ compactVertex conclusion right := by
    intro same
    exact leftNotRight (compactVertex_injective_of_ne leftNotConclusion
      rightNotConclusion same)
  change (context ++ [compactVertex conclusion left,
    compactVertex conclusion right]).Nodup
  rw [List.nodup_append]
  refine ⟨contextNodup, by simp [compactDistinct], ?_⟩
  intro vertex vertexMembership boundary boundaryMembership
  simp at boundaryMembership
  rcases boundaryMembership with rfl | rfl
  · intro same
    subst vertex
    exact compactLeftFresh vertexMembership
  · intro same
    subst vertex
    exact compactRightFresh vertexMembership

theorem peelTerminalPar_conclusions_eraseDups_length
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    (certificate.peelTerminalPar left right conclusion).conclusions.eraseDups.length =
      (certificate.peelTerminalPar left right conclusion).conclusions.length := by
  rw [eraseDups_eq_self_of_nodup
    (peelTerminalPar_conclusions_nodup structural terminal)]

theorem LinkWellFormed.deleteVertex
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    {link compacted : Link}
    (wellFormed : certificate.LinkWellFormed link)
    (deleted : link.deleteVertex? conclusion = some compacted) :
    (certificate.peelTerminalPar left right conclusion).LinkWellFormed
      compacted := by
  have conclusionInBounds := structural.2.2.1 conclusion terminal.2
  have formulaSize :
      (certificate.peelTerminalPar left right conclusion).formulas.size =
        certificate.formulas.size - 1 := by
    simp [peelTerminalPar, Array.eraseIdxIfInBounds, conclusionInBounds]
  cases link with
  | «axiom» first second =>
      by_cases firstDeleted : first = conclusion
      · subst first
        simp [Link.deleteVertex?, Certificate.deleteVertex?] at deleted
      · by_cases secondDeleted : second = conclusion
        · subst second
          simp [Link.deleteVertex?, Certificate.deleteVertex?] at deleted
        · simp [Link.deleteVertex?, Certificate.deleteVertex?, firstDeleted,
            secondDeleted] at deleted
          subst compacted
          rcases wellFormed with
            ⟨different, firstInBounds, secondInBounds, typing⟩
          refine ⟨?_, ?_, ?_, ?_⟩
          · exact fun same => different
              (compactVertex_injective_of_ne firstDeleted secondDeleted same)
          · rw [formulaSize]
            exact compactVertex_lt conclusionInBounds firstInBounds firstDeleted
          · rw [formulaSize]
            exact compactVertex_lt conclusionInBounds secondInBounds secondDeleted
          · rw [peelTerminalPar_formula?_compact structural terminal firstDeleted,
              peelTerminalPar_formula?_compact structural terminal secondDeleted]
            exact typing
  | tensor first second result =>
      by_cases firstDeleted : first = conclusion
      · subst first
        simp [Link.deleteVertex?, Certificate.deleteVertex?] at deleted
      · by_cases secondDeleted : second = conclusion
        · subst second
          simp [Link.deleteVertex?, Certificate.deleteVertex?, firstDeleted] at deleted
        · by_cases resultDeleted : result = conclusion
          · subst result
            simp [Link.deleteVertex?, Certificate.deleteVertex?, firstDeleted,
              secondDeleted] at deleted
          · simp [Link.deleteVertex?, Certificate.deleteVertex?, firstDeleted,
              secondDeleted, resultDeleted] at deleted
            subst compacted
            rcases wellFormed with
              ⟨firstSecond, firstResult, secondResult, firstInBounds,
                secondInBounds, resultInBounds, typing⟩
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact fun same => firstSecond
                (compactVertex_injective_of_ne firstDeleted secondDeleted same)
            · exact fun same => firstResult
                (compactVertex_injective_of_ne firstDeleted resultDeleted same)
            · exact fun same => secondResult
                (compactVertex_injective_of_ne secondDeleted resultDeleted same)
            · rw [formulaSize]
              exact compactVertex_lt conclusionInBounds firstInBounds firstDeleted
            · rw [formulaSize]
              exact compactVertex_lt conclusionInBounds secondInBounds secondDeleted
            · rw [formulaSize]
              exact compactVertex_lt conclusionInBounds resultInBounds resultDeleted
            · rw [peelTerminalPar_formula?_compact structural terminal firstDeleted,
                peelTerminalPar_formula?_compact structural terminal secondDeleted,
                peelTerminalPar_formula?_compact structural terminal resultDeleted]
              exact typing
  | par first second result =>
      by_cases firstDeleted : first = conclusion
      · subst first
        simp [Link.deleteVertex?, Certificate.deleteVertex?] at deleted
      · by_cases secondDeleted : second = conclusion
        · subst second
          simp [Link.deleteVertex?, Certificate.deleteVertex?, firstDeleted] at deleted
        · by_cases resultDeleted : result = conclusion
          · subst result
            simp [Link.deleteVertex?, Certificate.deleteVertex?, firstDeleted,
              secondDeleted] at deleted
          · simp [Link.deleteVertex?, Certificate.deleteVertex?, firstDeleted,
              secondDeleted, resultDeleted] at deleted
            subst compacted
            rcases wellFormed with
              ⟨firstSecond, firstResult, secondResult, firstInBounds,
                secondInBounds, resultInBounds, typing⟩
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact fun same => firstSecond
                (compactVertex_injective_of_ne firstDeleted secondDeleted same)
            · exact fun same => firstResult
                (compactVertex_injective_of_ne firstDeleted resultDeleted same)
            · exact fun same => secondResult
                (compactVertex_injective_of_ne secondDeleted resultDeleted same)
            · rw [formulaSize]
              exact compactVertex_lt conclusionInBounds firstInBounds firstDeleted
            · rw [formulaSize]
              exact compactVertex_lt conclusionInBounds secondInBounds secondDeleted
            · rw [formulaSize]
              exact compactVertex_lt conclusionInBounds resultInBounds resultDeleted
            · rw [peelTerminalPar_formula?_compact structural terminal firstDeleted,
                peelTerminalPar_formula?_compact structural terminal secondDeleted,
                peelTerminalPar_formula?_compact structural terminal resultDeleted]
              exact typing

theorem peelTerminalPar_links_wellFormed
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    ∀ link ∈ (certificate.peelTerminalPar left right conclusion).links,
      (certificate.peelTerminalPar left right conclusion).LinkWellFormed link := by
  intro link membership
  change link ∈ certificate.links.filterMap
    (Link.deleteVertex? conclusion) at membership
  simp only [List.mem_filterMap] at membership
  rcases membership with ⟨original, originalMembership, deleted⟩
  exact LinkWellFormed.deleteVertex structural terminal
    (structural.2.2.2.2.1 original originalMembership) deleted

/-- Every structural obligation for terminal-par peeling except global node
ownership. The omitted final field is isolated explicitly so that this result
cannot be mistaken for full structural preservation. -/
theorem peelTerminalPar_structural_prefix
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    0 < (certificate.peelTerminalPar left right conclusion).formulas.size ∧
    0 < (certificate.peelTerminalPar left right conclusion).conclusions.length ∧
    (∀ vertex ∈
      (certificate.peelTerminalPar left right conclusion).conclusions,
      vertex <
        (certificate.peelTerminalPar left right conclusion).formulas.size) ∧
    (certificate.peelTerminalPar left right conclusion).conclusions.eraseDups.length =
      (certificate.peelTerminalPar left right conclusion).conclusions.length ∧
    (∀ link ∈ (certificate.peelTerminalPar left right conclusion).links,
      (certificate.peelTerminalPar left right conclusion).LinkWellFormed link) := by
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  rcases terminalWellFormed with
    ⟨_, leftNotConclusion, rightNotConclusion, leftInBounds,
      rightInBounds, conclusionInBounds, _⟩
  have formulaSize :
      (certificate.peelTerminalPar left right conclusion).formulas.size =
        certificate.formulas.size - 1 := by
    simp [peelTerminalPar, Array.eraseIdxIfInBounds, conclusionInBounds]
  refine ⟨?_, ?_, ?_,
    peelTerminalPar_conclusions_eraseDups_length structural terminal,
    peelTerminalPar_links_wellFormed structural terminal⟩
  · rw [formulaSize]
    have onePremisePositive : 0 < left ∨ 0 < conclusion := by
      by_cases leftZero : left = 0
      · right
        exact Nat.pos_of_ne_zero fun conclusionZero =>
          leftNotConclusion (leftZero.trans conclusionZero.symm)
      · exact Or.inl (Nat.pos_of_ne_zero leftZero)
    have oneLtSize : 1 < certificate.formulas.size := by
      rcases onePremisePositive with leftPositive | conclusionPositive
      · exact Nat.lt_of_le_of_lt leftPositive leftInBounds
      · exact Nat.lt_of_le_of_lt conclusionPositive conclusionInBounds
    exact Nat.sub_pos_of_lt oneLtSize
  · simp [peelTerminalPar]
  · intro vertex membership
    change vertex ∈
      (certificate.conclusions.filter (· != conclusion)).map
          (compactVertex conclusion) ++
        [compactVertex conclusion left,
          compactVertex conclusion right] at membership
    rw [List.mem_append] at membership
    rcases membership with contextMembership | premiseMembership
    · rcases List.mem_map.mp contextMembership with
        ⟨original, originalMembership, rfl⟩
      have filtered := List.mem_filter.mp originalMembership
      have originalNotConclusion : original ≠ conclusion := by
        simpa using filtered.2
      rw [formulaSize]
      exact compactVertex_lt conclusionInBounds
        (structural.2.2.1 original filtered.1) originalNotConclusion
    · simp at premiseMembership
      rcases premiseMembership with rfl | rfl
      · rw [formulaSize]
        exact compactVertex_lt conclusionInBounds leftInBounds
          leftNotConclusion
      · rw [formulaSize]
        exact compactVertex_lt conclusionInBounds rightInBounds
          rightNotConclusion

theorem peelTerminalPar_axiomCount_compact
    {certificate : Certificate} {left right conclusion vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    (vertexNotConclusion : vertex ≠ conclusion) :
    (certificate.peelTerminalPar left right conclusion).axiomCount
        (compactVertex conclusion vertex) =
      certificate.axiomCount vertex := by
  unfold axiomCount
  change ((certificate.links.filterMap
      (Link.deleteVertex? conclusion)).filter
        (·.containsAxiomEndpoint (compactVertex conclusion vertex))).length =
    (certificate.links.filter (·.containsAxiomEndpoint vertex)).length
  apply length_filter_filterMap_eq
  intro link membership
  cases deleted : link.deleteVertex? conclusion with
  | none =>
      have same := (TerminalPar.deletion_none_iff_eq structural terminal
        membership).mp deleted
      subst link
      rfl
  | some compacted =>
      exact Link.containsAxiomEndpoint_deleteVertex?_eq_some
        vertexNotConclusion deleted

theorem peelTerminalPar_producerCount_compact
    {certificate : Certificate} {left right conclusion vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    (vertexNotConclusion : vertex ≠ conclusion) :
    (certificate.peelTerminalPar left right conclusion).producerCount
        (compactVertex conclusion vertex) =
      certificate.producerCount vertex := by
  unfold producerCount
  change ((certificate.links.filterMap
      (Link.deleteVertex? conclusion)).filter
        (·.produces (compactVertex conclusion vertex))).length =
    (certificate.links.filter (·.produces vertex)).length
  apply length_filter_filterMap_eq
  intro link membership
  cases deleted : link.deleteVertex? conclusion with
  | none =>
      have same := (TerminalPar.deletion_none_iff_eq structural terminal
        membership).mp deleted
      subst link
      simp [Link.produces, Ne.symm vertexNotConclusion]
  | some compacted =>
      exact Link.produces_deleteVertex?_eq_some vertexNotConclusion deleted

theorem peelTerminalPar_parentUseCount_compact
    {certificate : Certificate} {left right conclusion vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    (vertexNotConclusion : vertex ≠ conclusion)
    (vertexNotLeft : vertex ≠ left) (vertexNotRight : vertex ≠ right) :
    (certificate.peelTerminalPar left right conclusion).parentUseCount
        (compactVertex conclusion vertex) =
      certificate.parentUseCount vertex := by
  unfold parentUseCount
  change ((certificate.links.filterMap
      (Link.deleteVertex? conclusion)).filter
        (·.usesAsPremise (compactVertex conclusion vertex))).length =
    (certificate.links.filter (·.usesAsPremise vertex)).length
  apply length_filter_filterMap_eq
  intro link membership
  cases deleted : link.deleteVertex? conclusion with
  | none =>
      have same := (TerminalPar.deletion_none_iff_eq structural terminal
        membership).mp deleted
      subst link
      simp [Link.usesAsPremise, Link.premises, vertexNotLeft,
        vertexNotRight]
  | some compacted =>
      exact Link.usesAsPremise_deleteVertex?_eq_some
        vertexNotConclusion deleted

theorem peelTerminalPar_parentUseCount_premise_zero
    {certificate : Certificate} {left right conclusion premise : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    (isPremise : premise = left ∨ premise = right) :
    (certificate.peelTerminalPar left right conclusion).parentUseCount
        (compactVertex conclusion premise) = 0 := by
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  rcases terminalWellFormed with
    ⟨_, leftNotConclusion, rightNotConclusion, leftInBounds,
      rightInBounds, _, _⟩
  have premiseNotConclusion : premise ≠ conclusion := by
    rcases isPremise with rfl | rfl
    · exact leftNotConclusion
    · exact rightNotConclusion
  have premiseInBounds : premise < certificate.formulas.size := by
    rcases isPremise with rfl | rfl
    · exact leftInBounds
    · exact rightInBounds
  have premiseNotBoundary : premise ∉ certificate.conclusions := by
    have boundaries := TerminalPar.premises_not_conclusions structural terminal
    rcases isPremise with rfl | rfl
    · exact boundaries.1
    · exact boundaries.2
  have originalNode := structural.2.2.2.2.2 premise premiseInBounds
  have originalCount : certificate.parentUseCount premise = 1 := by
    simpa [Certificate.NodeWellFormed, premiseNotBoundary] using originalNode.2
  have terminalUses :
      (Link.par left right conclusion).usesAsPremise premise = true := by
    rcases isPremise with rfl | rfl <;>
      simp [Link.usesAsPremise, Link.premises]
  unfold parentUseCount
  change ((certificate.links.filterMap
      (Link.deleteVertex? conclusion)).filter
        (·.usesAsPremise (compactVertex conclusion premise))).length = 0
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro compacted compactedMembership
  cases compactedUses :
      compacted.usesAsPremise (compactVertex conclusion premise) with
  | false => simp
  | true =>
      simp only [List.mem_filterMap] at compactedMembership
      rcases compactedMembership with
        ⟨original, originalMembership, deleted⟩
      have originalUses := Link.usesAsPremise_deleteVertex?_eq_some
        premiseNotConclusion deleted
      rw [compactedUses] at originalUses
      have originalUsesTrue : original.usesAsPremise premise = true := by
        simpa using originalUses.symm
      have unique := eq_of_mem_filter_length_one
        (show (certificate.links.filter
          (·.usesAsPremise premise)).length = 1 from originalCount)
        originalMembership originalUsesTrue terminal.1 terminalUses
      subst original
      simp [Link.deleteVertex?, Certificate.deleteVertex?] at deleted

theorem peelTerminalPar_compact_mem_conclusions_iff
    {certificate : Certificate} {left right conclusion vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    (vertexNotConclusion : vertex ≠ conclusion) :
    compactVertex conclusion vertex ∈
        (certificate.peelTerminalPar left right conclusion).conclusions ↔
      vertex ∈ certificate.conclusions ∨ vertex = left ∨ vertex = right := by
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  have leftNotConclusion := terminalWellFormed.2.1
  have rightNotConclusion := terminalWellFormed.2.2.1
  change compactVertex conclusion vertex ∈
      (certificate.conclusions.filter (· != conclusion)).map
          (compactVertex conclusion) ++
        [compactVertex conclusion left,
          compactVertex conclusion right] ↔ _
  constructor
  · intro membership
    rw [List.mem_append] at membership
    rcases membership with contextMembership | premiseMembership
    · rcases List.mem_map.mp contextMembership with
        ⟨original, originalMembership, same⟩
      have filtered := List.mem_filter.mp originalMembership
      have originalNotConclusion : original ≠ conclusion := by
        simpa using filtered.2
      have originalSame := compactVertex_injective_of_ne
        originalNotConclusion vertexNotConclusion same
      subst original
      exact Or.inl filtered.1
    · simp at premiseMembership
      rcases premiseMembership with same | same
      · exact Or.inr (Or.inl (compactVertex_injective_of_ne
          vertexNotConclusion leftNotConclusion same))
      · exact Or.inr (Or.inr (compactVertex_injective_of_ne
          vertexNotConclusion rightNotConclusion same))
  · intro membership
    rw [List.mem_append]
    rcases membership with oldBoundary | same
    · left
      apply List.mem_map.mpr
      exact ⟨vertex, List.mem_filter.mpr
        ⟨oldBoundary, by simpa using vertexNotConclusion⟩, rfl⟩
    · rcases same with rfl | rfl
      · right
        simp
      · right
        simp

theorem peelTerminalPar_nodeWellFormed_compact
    {certificate : Certificate} {left right conclusion vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    (vertexInBounds : vertex < certificate.formulas.size)
    (vertexNotConclusion : vertex ≠ conclusion) :
    (certificate.peelTerminalPar left right conclusion).NodeWellFormed
      (compactVertex conclusion vertex) := by
  have originalNode := structural.2.2.2.2.2 vertex vertexInBounds
  unfold NodeWellFormed at originalNode ⊢
  rw [peelTerminalPar_formula?_compact structural terminal
    vertexNotConclusion]
  constructor
  · cases formula : certificate.formula? vertex with
    | none => simp [formula] at originalNode
    | some value =>
        cases value with
        | atom name positive =>
            simp only [formula] at originalNode ⊢
            rw [peelTerminalPar_axiomCount_compact structural terminal
              vertexNotConclusion]
            exact originalNode.1
        | tensor first second =>
            simp only [formula] at originalNode ⊢
            rw [peelTerminalPar_producerCount_compact structural terminal
              vertexNotConclusion]
            exact originalNode.1
        | par first second =>
            simp only [formula] at originalNode ⊢
            rw [peelTerminalPar_producerCount_compact structural terminal
              vertexNotConclusion]
            exact originalNode.1
  · by_cases isLeft : vertex = left
    · subst vertex
      have newBoundary : compactVertex conclusion left ∈
          (certificate.peelTerminalPar left right conclusion).conclusions :=
        (peelTerminalPar_compact_mem_conclusions_iff structural terminal
          (structural.2.2.2.2.1 _ terminal.1).2.1).mpr
          (Or.inr (Or.inl rfl))
      rw [if_pos newBoundary]
      exact peelTerminalPar_parentUseCount_premise_zero structural terminal
        (Or.inl rfl)
    · by_cases isRight : vertex = right
      · subst vertex
        have newBoundary : compactVertex conclusion right ∈
            (certificate.peelTerminalPar left right conclusion).conclusions :=
          (peelTerminalPar_compact_mem_conclusions_iff structural terminal
            (structural.2.2.2.2.1 _ terminal.1).2.2.1).mpr
            (Or.inr (Or.inr rfl))
        rw [if_pos newBoundary]
        exact peelTerminalPar_parentUseCount_premise_zero structural terminal
          (Or.inr rfl)
      · have boundaryIff : compactVertex conclusion vertex ∈
            (certificate.peelTerminalPar left right conclusion).conclusions ↔
            vertex ∈ certificate.conclusions := by
          rw [peelTerminalPar_compact_mem_conclusions_iff structural terminal
            vertexNotConclusion]
          simp [isLeft, isRight]
        by_cases oldBoundary : vertex ∈ certificate.conclusions
        · have newBoundary := boundaryIff.mpr oldBoundary
          rw [if_pos newBoundary,
            peelTerminalPar_parentUseCount_compact structural terminal
              vertexNotConclusion isLeft isRight]
          simpa [oldBoundary] using originalNode.2
        · have newBoundary : compactVertex conclusion vertex ∉
              (certificate.peelTerminalPar left right conclusion).conclusions :=
            fun membership => oldBoundary (boundaryIff.mp membership)
          rw [if_neg newBoundary,
            peelTerminalPar_parentUseCount_compact structural terminal
              vertexNotConclusion isLeft isRight]
          simpa [oldBoundary] using originalNode.2

theorem peelTerminalPar_nodes_wellFormed
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    ∀ vertex,
      vertex <
        (certificate.peelTerminalPar left right conclusion).formulas.size →
      (certificate.peelTerminalPar left right conclusion).NodeWellFormed
        vertex := by
  intro vertex vertexInBounds
  have conclusionInBounds := structural.2.2.1 conclusion terminal.2
  have formulaSize :
      (certificate.peelTerminalPar left right conclusion).formulas.size =
        certificate.formulas.size - 1 := by
    simp [peelTerminalPar, Array.eraseIdxIfInBounds, conclusionInBounds]
  have compactedInBounds : vertex < certificate.formulas.size - 1 := by
    simpa [formulaSize] using vertexInBounds
  let original := expandVertex conclusion vertex
  have originalInBounds : original < certificate.formulas.size :=
    expandVertex_lt conclusionInBounds compactedInBounds
  have originalNotConclusion : original ≠ conclusion :=
    expandVertex_ne conclusion vertex
  have node := peelTerminalPar_nodeWellFormed_compact structural terminal
    originalInBounds originalNotConclusion
  simpa [original, compactVertex_expandVertex] using node

/-- Removing a terminal par link and exposing its two premises preserves the
complete Boolean-free structural specification. -/
theorem peelTerminalPar_structurallyWellFormed
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    (certificate.peelTerminalPar left right conclusion).StructurallyWellFormed := by
  rcases peelTerminalPar_structural_prefix structural terminal with
    ⟨formulasPositive, conclusionsPositive, conclusionsInBounds,
      conclusionsUnique, linksWellFormed⟩
  exact ⟨formulasPositive, conclusionsPositive, conclusionsInBounds,
    conclusionsUnique, linksWellFormed,
    peelTerminalPar_nodes_wellFormed structural terminal⟩

theorem peelTerminalPar_wellFormed
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    (certificate.peelTerminalPar left right conclusion).wellFormed = true :=
  (Certificate.wellFormed_iff_structurallyWellFormed
    (certificate.peelTerminalPar left right conclusion)).mpr
    (peelTerminalPar_structurallyWellFormed structural terminal)

theorem peelTerminalPar_parChoices
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    (certificate.peelTerminalPar left right conclusion).parChoices =
      certificate.parChoices.filterMap
        (ParChoice.deleteVertex? conclusion) := by
  let emitChoice : Link → Option (Edge × Edge) := fun
    | .par first second result =>
        some ({ first := first, second := result },
          { first := second, second := result })
    | _ => none
  change
    ((certificate.links.filterMap (Link.deleteVertex? conclusion)).filterMap
      emitChoice) =
    (certificate.links.filterMap emitChoice).filterMap
      (ParChoice.deleteVertex? conclusion)
  suffices general : ∀ links : List Link,
      (∀ link ∈ links, link ∈ certificate.links) →
      ((links.filterMap (Link.deleteVertex? conclusion)).filterMap
        emitChoice) =
      (links.filterMap emitChoice).filterMap
        (ParChoice.deleteVertex? conclusion) by
    exact general certificate.links (by simp)
  intro links subset
  induction links with
  | nil => rfl
  | cons head tail ih =>
      have headMembership : head ∈ certificate.links :=
        subset head (by simp)
      have tailSubset : ∀ link ∈ tail, link ∈ certificate.links := by
        intro link membership
        exact subset link (by simp [membership])
      have tailEquality := ih tailSubset
      cases deleted : head.deleteVertex? conclusion with
      | none =>
          have same := (TerminalPar.deletion_none_iff_eq structural terminal
            headMembership).mp deleted
          subst head
          simpa [emitChoice, deleted, Link.deleteVertex?,
            ParChoice.deleteVertex?, Edge.deleteVertex?,
            Certificate.deleteVertex?] using tailEquality
      | some compacted =>
          rcases (Link.deleteVertex?_eq_some_iff head compacted conclusion).mp
            deleted with ⟨avoids, rfl⟩
          cases head with
          | «axiom» first second =>
              simpa [emitChoice, deleted, Link.compactVertices] using tailEquality
          | tensor first second result =>
              simpa [emitChoice, deleted, Link.compactVertices] using tailEquality
          | par first second result =>
              simp [Link.vertices] at avoids
              have firstNotConclusion : first ≠ conclusion := Ne.symm avoids.1
              have secondNotConclusion : second ≠ conclusion :=
                Ne.symm avoids.2.1
              have resultNotConclusion : result ≠ conclusion :=
                Ne.symm avoids.2.2
              simpa [emitChoice, deleted, Link.compactVertices,
                ParChoice.deleteVertex?, Edge.deleteVertex?,
                Certificate.deleteVertex?, firstNotConclusion,
                secondNotConclusion, resultNotConclusion] using tailEquality

theorem peelTerminalPar_fixedEdges
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    (certificate.peelTerminalPar left right conclusion).fixedEdges =
      certificate.fixedEdges.filterMap (Edge.deleteVertex? conclusion) := by
  let emitFixed : Link → List Edge := fun
    | .axiom first second => [{ first, second }]
    | .tensor first second result =>
        [{ first := first, second := result },
         { first := second, second := result }]
    | .par _ _ _ => []
  change
    (certificate.links.filterMap
      (Link.deleteVertex? conclusion)).flatMap emitFixed =
    (certificate.links.flatMap emitFixed).filterMap
      (Edge.deleteVertex? conclusion)
  suffices general : ∀ links : List Link,
      (∀ link ∈ links, link ∈ certificate.links) →
      (links.filterMap (Link.deleteVertex? conclusion)).flatMap emitFixed =
      (links.flatMap emitFixed).filterMap (Edge.deleteVertex? conclusion) by
    exact general certificate.links (by simp)
  intro links subset
  induction links with
  | nil => rfl
  | cons head tail ih =>
      have headMembership : head ∈ certificate.links :=
        subset head (by simp)
      have tailSubset : ∀ link ∈ tail, link ∈ certificate.links := by
        intro link membership
        exact subset link (by simp [membership])
      have tailEquality := ih tailSubset
      cases deleted : head.deleteVertex? conclusion with
      | none =>
          have same := (TerminalPar.deletion_none_iff_eq structural terminal
            headMembership).mp deleted
          subst head
          simpa [emitFixed, deleted, Link.deleteVertex?,
            Certificate.deleteVertex?] using tailEquality
      | some compacted =>
          rcases (Link.deleteVertex?_eq_some_iff head compacted conclusion).mp
            deleted with ⟨avoids, rfl⟩
          cases head with
          | «axiom» first second =>
              simp [Link.vertices] at avoids
              have firstNotConclusion : first ≠ conclusion := Ne.symm avoids.1
              have secondNotConclusion : second ≠ conclusion :=
                Ne.symm avoids.2
              simpa [emitFixed, deleted, Link.compactVertices,
                Edge.deleteVertex?, Certificate.deleteVertex?,
                firstNotConclusion, secondNotConclusion] using tailEquality
          | tensor first second result =>
              simp [Link.vertices] at avoids
              have firstNotConclusion : first ≠ conclusion := Ne.symm avoids.1
              have secondNotConclusion : second ≠ conclusion :=
                Ne.symm avoids.2.1
              have resultNotConclusion : result ≠ conclusion :=
                Ne.symm avoids.2.2
              simpa [emitFixed, deleted, Link.compactVertices,
                Edge.deleteVertex?, Certificate.deleteVertex?,
                firstNotConclusion, secondNotConclusion,
                resultNotConclusion] using tailEquality
          | par first second result =>
              simpa [emitFixed, deleted, Link.compactVertices]
                using tailEquality

/-- Checker-gated terminal-par premise. Even before the general preservation
theorem is complete, callers cannot accidentally treat a malformed candidate
as a proof net. -/
def peelTerminalParChecked? (certificate : Certificate)
    (left right conclusion : Vertex) :
    Option CutFreeDerivation.CheckedCertificate := do
  let premise ← certificate.peelTerminalParCandidate? left right conclusion
  if accepted : premise.check = true then
    some ⟨premise, accepted⟩
  else
    none

/-- Two checker-accepted premises produced by a terminal splitting tensor
candidate. -/
structure CheckedTensorPremises where
  leftPremise : CutFreeDerivation.CheckedCertificate
  rightPremise : CutFreeDerivation.CheckedCertificate

/-- Executable candidate for the inverse tensor rule. Reachability is computed
in the full occurrence graph after deleting the terminal tensor conclusion.
The candidate is returned only when the two vertex sets cover every remaining
link without crossings. Mathematical completeness of this criterion is a
separate splitting theorem. -/
def splitTerminalTensorCandidate? (certificate : Certificate)
    (left right conclusion : Vertex) : Option (Certificate × Certificate) := do
  let terminalLink := Link.tensor left right conclusion
  if !certificate.links.contains terminalLink then none
  if !certificate.conclusions.contains conclusion then none
  let graph := certificate.fullGraphWithoutVertex conclusion
  let leftReachable := graph.closureN certificate.formulas.size [left]
  if leftReachable.contains right then none
  let remainingVertices := List.range certificate.formulas.size
  let leftVertices := remainingVertices.filter fun vertex =>
    vertex != conclusion && leftReachable.contains vertex
  let rightVertices := remainingVertices.filter fun vertex =>
    vertex != conclusion && !leftReachable.contains vertex
  let remainingLinks := certificate.links.erase terminalLink
  let partitioned := remainingLinks.all fun link =>
    link.vertices.all leftVertices.contains ||
      link.vertices.all rightVertices.contains
  if !partitioned then none
  let otherConclusions := certificate.conclusions.erase conclusion
  let leftBoundary :=
    otherConclusions.filter leftVertices.contains ++ [left]
  let rightBoundary :=
    otherConclusions.filter rightVertices.contains ++ [right]
  let leftCertificate ← certificate.restrictTo? leftVertices leftBoundary
  let rightCertificate ← certificate.restrictTo? rightVertices rightBoundary
  pure (leftCertificate, rightCertificate)

/-- Checker-gated tensor split. No recursive caller can consume a proposed
component unless both independent proof-net checks succeed. -/
def splitTerminalTensorChecked? (certificate : Certificate)
    (left right conclusion : Vertex) : Option CheckedTensorPremises := do
  let (leftCertificate, rightCertificate) ←
    certificate.splitTerminalTensorCandidate? left right conclusion
  if leftAccepted : leftCertificate.check = true then
    if rightAccepted : rightCertificate.check = true then
      some {
        leftPremise := ⟨leftCertificate, leftAccepted⟩
        rightPremise := ⟨rightCertificate, rightAccepted⟩ }
    else
      none
  else
    none

/-- Exact proof interface for a terminal-par inverse. It isolates the
certificate bookkeeping obligation from the already-proved graph theorem:
every premise switching must be an edge-order permutation of an original
switching with the terminal par conclusion deleted as a leaf. -/
structure TerminalParReduction (input premise : Certificate)
    (conclusion : Vertex) : Prop where
  premiseStructural : premise.StructurallyWellFormed
  switchingDeletion : ∀ premiseGraph,
    premise.SwitchingGraph premiseGraph →
      ∃ inputGraph,
        input.SwitchingGraph inputGraph ∧
        inputGraph.Leaf conclusion ∧
        premiseGraph.vertexCount =
          (inputGraph.deleteVertex conclusion).vertexCount ∧
        premiseGraph.edges.Perm
          (inputGraph.deleteVertex conclusion).edges

/-- The concrete terminal-par peel satisfies the exact graph-deletion
interface required by sequentialization. -/
theorem peelTerminalPar_reduction
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    TerminalParReduction certificate
      (certificate.peelTerminalPar left right conclusion) conclusion := by
  refine {
    premiseStructural :=
      peelTerminalPar_structurallyWellFormed structural terminal
    switchingDeletion := ?_ }
  intro premiseGraph premiseSwitching
  rcases premiseSwitching with ⟨selected, selection, rfl⟩
  have transformedSelection : ChoiceSelection
      (certificate.parChoices.filterMap
        (ParChoice.deleteVertex? conclusion)) selected := by
    rw [← peelTerminalPar_parChoices structural terminal]
    exact selection
  rcases transformedSelection.liftDelete (by
      intro choice membership
      exact TerminalPar.parChoice_deletion_agreement structural terminal
        membership) with
    ⟨lifted, liftedSelection, selectedEquation⟩
  let inputGraph := certificate.graphForSelection lifted
  refine ⟨inputGraph, ⟨lifted, liftedSelection, rfl⟩,
    TerminalPar.graphForSelection_leaf structural terminal liftedSelection,
    ?_, ?_⟩
  · change
      (certificate.peelTerminalPar left right conclusion).formulas.size =
        certificate.formulas.size - 1
    have conclusionInBounds := structural.2.2.1 conclusion terminal.2
    simp [peelTerminalPar, Array.eraseIdxIfInBounds, conclusionInBounds]
  · change
      ((certificate.peelTerminalPar left right conclusion).fixedEdges ++
        selected).Perm
      ((certificate.fixedEdges ++ lifted).filterMap
        (Edge.deleteVertex? conclusion))
    rw [peelTerminalPar_fixedEdges structural terminal, selectedEquation,
      List.filterMap_append]

namespace TerminalParReduction

theorem declarativelyCorrect {input premise : Certificate}
    {conclusion : Vertex}
    (reduction : TerminalParReduction input premise conclusion)
    (correct : input.DeclarativelyCorrect) :
    premise.DeclarativelyCorrect := by
  refine ⟨reduction.premiseStructural, ?_⟩
  intro premiseGraph premiseSwitching
  rcases reduction.switchingDeletion premiseGraph premiseSwitching with
    ⟨inputGraph, inputSwitching, leaf, vertexCount, edgePermutation⟩
  have inputTree := correct.2 inputGraph inputSwitching
  have deletedTree := inputTree.deleteLeaf leaf
  exact deletedTree.permuteEdges vertexCount.symm edgePermutation.symm

theorem check_of_check {input premise : Certificate} {conclusion : Vertex}
    (reduction : TerminalParReduction input premise conclusion)
    (accepted : input.check = true) :
    premise.check = true := by
  apply premise.check_iff_declarativelyCorrect.mpr
  exact reduction.declarativelyCorrect
    (input.check_iff_declarativelyCorrect.mp accepted)

end TerminalParReduction

theorem peelTerminalPar_check_of_check
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    (accepted : certificate.check = true) :
    (certificate.peelTerminalPar left right conclusion).check = true :=
  (peelTerminalPar_reduction structural terminal).check_of_check accepted

theorem mem_terminalPars_iff (certificate : Certificate)
    (left right conclusion : Vertex) :
    (left, right, conclusion) ∈ certificate.terminalPars ↔
      certificate.TerminalPar left right conclusion := by
  constructor
  · intro membership
    simp only [terminalPars, List.mem_filterMap] at membership
    rcases membership with ⟨link, linkMembership, emitted⟩
    cases link with
    | «axiom» first second => simp at emitted
    | tensor first second result => simp at emitted
    | par first second result =>
        by_cases boundary : result ∈ certificate.conclusions
        · simp [boundary] at emitted
          rcases emitted with ⟨rfl, rfl, rfl⟩
          exact ⟨linkMembership, boundary⟩
        · simp [boundary] at emitted
  · rintro ⟨linkMembership, boundary⟩
    simp only [terminalPars, List.mem_filterMap]
    exact ⟨.par left right conclusion, linkMembership, by simp [boundary]⟩

theorem mem_terminalTensors_iff (certificate : Certificate)
    (left right conclusion : Vertex) :
    (left, right, conclusion) ∈ certificate.terminalTensors ↔
      certificate.TerminalTensor left right conclusion := by
  constructor
  · intro membership
    simp only [terminalTensors, List.mem_filterMap] at membership
    rcases membership with ⟨link, linkMembership, emitted⟩
    cases link with
    | «axiom» first second => simp at emitted
    | par first second result => simp at emitted
    | tensor first second result =>
        by_cases boundary : result ∈ certificate.conclusions
        · simp [boundary] at emitted
          rcases emitted with ⟨rfl, rfl, rfl⟩
          exact ⟨linkMembership, boundary⟩
        · simp [boundary] at emitted
  · rintro ⟨linkMembership, boundary⟩
    simp only [terminalTensors, List.mem_filterMap]
    exact ⟨.tensor left right conclusion, linkMembership, by simp [boundary]⟩

end Certificate

end ProofNetIR
