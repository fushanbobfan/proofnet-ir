import Lean.Elab.Tactic.Omega
import ProofNetIR.Certificate

namespace ProofNetIR

structure Edge where
  first : Vertex
  second : Vertex
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure Graph where
  vertexCount : Nat
  edges : List Edge
  deriving Repr, DecidableEq, BEq

namespace Graph

/-- A finite list containing a value with property `P` has a decomposition at
the first such value. -/
theorem exists_first_decomposition {α : Type} (values : List α)
    (P : α → Prop) (existsValue : ∃ value ∈ values, P value) :
    ∃ before value after,
      values = before ++ value :: after ∧
      P value ∧
      ∀ earlier ∈ before, ¬P earlier := by
  classical
  induction values with
  | nil => simp at existsValue
  | cons head tail ih =>
      by_cases headProperty : P head
      · exact ⟨[], head, tail, by simp, headProperty, by simp⟩
      · have tailExists : ∃ value ∈ tail, P value := by
          rcases existsValue with ⟨value, membership, property⟩
          rw [List.mem_cons] at membership
          rcases membership with same | inTail
          · subst value
            exact False.elim (headProperty property)
          · exact ⟨value, inTail, property⟩
        rcases ih tailExists with
          ⟨before, value, after, equation, property, first⟩
        refine ⟨head :: before, value, after, ?_, property, ?_⟩
        · simp [equation]
        · intro earlier membership
          rw [List.mem_cons] at membership
          rcases membership with same | inBefore
          · subst earlier
            exact headProperty
          · exact first earlier inBefore

/-- Reversal preserves duplicate-freedom for arbitrary finite lists. -/
theorem nodup_reverse_of_nodup {α : Type} (values : List α)
    (nodup : values.Nodup) : values.reverse.Nodup := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      rw [List.reverse_cons, List.nodup_append]
      refine ⟨ih (List.nodup_cons.mp nodup).2, by simp, ?_⟩
      intro first firstMembership second secondMembership same
      simp at secondMembership
      subst second
      subst first
      exact (List.nodup_cons.mp nodup).1
        (by simpa using firstMembership)

theorem mem_of_mem_dropLast {α : Type} {value : α} {values : List α}
    (membership : value ∈ values.dropLast) : value ∈ values := by
  have nonempty : values ≠ [] := by
    intro empty
    simp [empty] at membership
  rw [← List.dropLast_concat_getLast nonempty]
  exact List.mem_append.mpr (.inl membership)

theorem eq_of_map_eq_of_mem_of_nodup {α β : Type}
    {values : List α} {function : α → β} {first second : α}
    (nodup : (values.map function).Nodup)
    (firstMembership : first ∈ values)
    (secondMembership : second ∈ values)
    (same : function first = function second) : first = second := by
  induction values with
  | nil => simp at firstMembership
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at nodup
      simp only [List.mem_cons] at firstMembership secondMembership
      rcases firstMembership with rfl | firstTail <;>
        rcases secondMembership with rfl | secondTail
      · rfl
      · exact False.elim (nodup.1
          (List.mem_map.mpr ⟨second, secondTail, same.symm⟩))
      · exact False.elim (nodup.1
          (List.mem_map.mpr ⟨first, firstTail, same⟩))
      · exact ih nodup.2 firstTail secondTail

/-- Number of retained Boolean mask entries strictly before an original edge
index. This is the compacted index of a kept edge. -/
def retainedIndex (mask : List Bool) (index : Nat) : Nat :=
  (mask.take index).count true

/-- Retain stored edge occurrences according to a parallel Boolean mask. -/
def retainEdgesByMask : List Edge → List Bool → List Edge
  | edge :: edges, keep :: mask =>
      if keep then edge :: retainEdgesByMask edges mask
      else retainEdgesByMask edges mask
  | _, _ => []

/-- The occurrence-preserving masked subgraph. -/
def retainEdges (graph : Graph) (mask : List Bool) : Graph where
  vertexCount := graph.vertexCount
  edges := retainEdgesByMask graph.edges mask

theorem retainEdgesByMask_lookup_kept {edges : List Edge} {mask : List Bool}
    {index : Nat} {edge : Edge}
    (aligned : edges.length = mask.length)
    (edgeLookup : edges[index]? = some edge)
    (kept : mask[index]? = some true) :
    (retainEdgesByMask edges mask)[retainedIndex mask index]? = some edge := by
  induction index generalizing edges mask with
  | zero =>
      cases edges <;> cases mask <;>
        simp_all [retainEdgesByMask, retainedIndex]
  | succ index ih =>
      cases edges with
      | nil => simp at edgeLookup
      | cons head tail =>
          cases mask with
          | nil => simp at aligned
          | cons keep rest =>
              cases keep <;>
                simp_all [retainEdgesByMask, retainedIndex]

theorem retainedIndex_lt_of_lt_of_kept {mask : List Bool} {first second : Nat}
    (less : first < second) (firstKept : mask[first]? = some true) :
    retainedIndex mask first < retainedIndex mask second := by
  induction mask generalizing first second with
  | nil => simp at firstKept
  | cons keep tail ih =>
      cases first with
      | zero =>
          cases second with
          | zero => omega
          | succ second =>
              cases keep <;>
                simp_all [retainedIndex]
      | succ first =>
          cases second with
          | zero => omega
          | succ second =>
              have smaller := ih (Nat.lt_of_succ_lt_succ less) firstKept
              cases keep <;>
                simp_all [retainedIndex]

theorem retainedIndex_injective_of_kept {mask : List Bool}
    {first second : Nat}
    (firstKept : mask[first]? = some true)
    (secondKept : mask[second]? = some true)
    (same : retainedIndex mask first = retainedIndex mask second) :
    first = second := by
  rcases Nat.lt_trichotomy first second with less | equal | greater
  · have strict := retainedIndex_lt_of_lt_of_kept less firstKept
    omega
  · exact equal
  · have strict := retainedIndex_lt_of_lt_of_kept greater secondKept
    omega

/-- Undirected adjacency induced by one stored edge. -/
def Adjacent (graph : Graph) (left right : Vertex) : Prop :=
  ∃ edge ∈ graph.edges,
    (edge.first = left ∧ edge.second = right) ∨
    (edge.first = right ∧ edge.second = left)

/-- One oriented occurrence of a stored multigraph edge. The list index keeps
parallel equal-valued edges distinct, which vertex-only `Walk` deliberately
does not do. -/
structure DirectedEdge (graph : Graph) where
  index : Nat
  edge : Edge
  lookup : graph.edges[index]? = some edge
  forward : Bool

namespace DirectedEdge

def source {graph : Graph} (directed : graph.DirectedEdge) : Vertex :=
  if directed.forward then directed.edge.first else directed.edge.second

def target {graph : Graph} (directed : graph.DirectedEdge) : Vertex :=
  if directed.forward then directed.edge.second else directed.edge.first

def reverse {graph : Graph} (directed : graph.DirectedEdge) :
    graph.DirectedEdge where
  index := directed.index
  edge := directed.edge
  lookup := directed.lookup
  forward := !directed.forward

@[simp] theorem reverse_source {graph : Graph}
    (directed : graph.DirectedEdge) :
    directed.reverse.source = directed.target := by
  rcases directed with ⟨index, edge, lookup, forward⟩
  cases forward <;> rfl

@[simp] theorem reverse_target {graph : Graph}
    (directed : graph.DirectedEdge) :
    directed.reverse.target = directed.source := by
  rcases directed with ⟨index, edge, lookup, forward⟩
  cases forward <;> rfl

@[simp] theorem reverse_index {graph : Graph}
    (directed : graph.DirectedEdge) : directed.reverse.index = directed.index :=
  rfl

@[simp] theorem reverse_reverse {graph : Graph}
    (directed : graph.DirectedEdge) : directed.reverse.reverse = directed := by
  rcases directed with ⟨index, edge, lookup, forward⟩
  cases forward <;> rfl

/-- An exact stored occurrence has exactly two orientations. Thus equal
occurrence indices determine either the same directed edge or its reverse. -/
theorem eq_or_eq_reverse_of_index_eq {graph : Graph}
    (first second : graph.DirectedEdge)
    (sameIndex : first.index = second.index) :
    first = second ∨ first = second.reverse := by
  have sameEdge : first.edge = second.edge := by
    have lookupEquation : some first.edge = some second.edge := by
      rw [← first.lookup, ← second.lookup, sameIndex]
    exact Option.some.inj lookupEquation
  rcases first with ⟨firstIndex, firstEdge, firstLookup, firstForward⟩
  rcases second with ⟨secondIndex, secondEdge, secondLookup, secondForward⟩
  simp only at sameIndex sameEdge
  subst secondIndex
  subst secondEdge
  cases firstForward <;> cases secondForward <;>
    simp [reverse]

/-- An occurrence index together with its orientation determines the complete
directed-edge value; the stored edge and lookup proof are forced by the graph
list. -/
theorem eq_of_index_eq_of_forward_eq {graph : Graph}
    (first second : graph.DirectedEdge)
    (sameIndex : first.index = second.index)
    (sameForward : first.forward = second.forward) : first = second := by
  rcases first with ⟨firstIndex, firstEdge, firstLookup, firstForward⟩
  rcases second with ⟨secondIndex, secondEdge, secondLookup, secondForward⟩
  simp only at sameIndex sameForward
  subst secondIndex
  subst secondForward
  have sameEdge : firstEdge = secondEdge := by
    apply Option.some.inj
    exact firstLookup.symm.trans secondLookup
  subst secondEdge
  rfl

theorem edge_mem {graph : Graph} (directed : graph.DirectedEdge) :
    directed.edge ∈ graph.edges := by
  rcases List.getElem?_eq_some_iff.mp directed.lookup with
    ⟨inBounds, equation⟩
  rw [← equation]
  exact List.getElem_mem inBounds

theorem adjacent {graph : Graph} (directed : graph.DirectedEdge) :
    graph.Adjacent directed.source directed.target := by
  rcases directed with ⟨index, edge, lookup, forward⟩
  have membership : edge ∈ graph.edges := by
    rcases List.getElem?_eq_some_iff.mp lookup with ⟨inBounds, equation⟩
    rw [← equation]
    exact List.getElem_mem inBounds
  refine ⟨edge, membership, ?_⟩
  cases forward <;> simp [source, target]

def retain {graph : Graph} {mask : List Bool}
    (directed : graph.DirectedEdge)
    (aligned : graph.edges.length = mask.length)
    (kept : mask[directed.index]? = some true) :
    (graph.retainEdges mask).DirectedEdge where
  index := retainedIndex mask directed.index
  edge := directed.edge
  lookup := retainEdgesByMask_lookup_kept aligned directed.lookup kept
  forward := directed.forward

@[simp] theorem retain_source {graph : Graph} {mask : List Bool}
    (directed : graph.DirectedEdge)
    (aligned : graph.edges.length = mask.length)
    (kept : mask[directed.index]? = some true) :
    (directed.retain aligned kept).source = directed.source := rfl

@[simp] theorem retain_target {graph : Graph} {mask : List Bool}
    (directed : graph.DirectedEdge)
    (aligned : graph.edges.length = mask.length)
    (kept : mask[directed.index]? = some true) :
    (directed.retain aligned kept).target = directed.target := rfl

end DirectedEdge

/-- Enumerate both orientations of every stored edge occurrence. The exact
list index and lookup proof remain attached, so parallel equal-valued edges are
distinct entries. -/
def directedEdges (graph : Graph) : List graph.DirectedEdge :=
  (List.range graph.edges.length).flatMap fun index =>
    match lookup : graph.edges[index]? with
    | none => []
    | some edge =>
        [{ index, edge, lookup, forward := false },
         { index, edge, lookup, forward := true }]

theorem DirectedEdge.mem_directedEdges {graph : Graph}
    (directed : graph.DirectedEdge) : directed ∈ graph.directedEdges := by
  rcases directed with ⟨index, edge, lookup, forward⟩
  simp only [directedEdges, List.mem_flatMap]
  refine ⟨index, List.mem_range.mpr
    (List.getElem?_eq_some_iff.mp lookup).1, ?_⟩
  split
  · rename_i absent
    have impossible : (none : Option Edge) = some edge :=
      absent.symm.trans lookup
    contradiction
  · rename_i matched present
    have sameEdge : matched = edge :=
      Option.some.inj (present.symm.trans lookup)
    subst matched
    cases forward <;> simp

/-- Edge-identity-aware oriented walks for colored-path and multigraph-cycle
arguments. `Walk` remains the checker-facing endpoint relation; this layer is
strictly richer and records the exact stored edge occurrence at every step. -/
inductive EdgeWalk (graph : Graph) :
    Vertex → List graph.DirectedEdge → Vertex → Prop where
  | refl (vertex : Vertex) : EdgeWalk graph vertex [] vertex
  | step {start middle finish : Vertex}
      {traversed : List graph.DirectedEdge}
      (prior : EdgeWalk graph start traversed middle)
      (directed : graph.DirectedEdge)
      (starts : directed.source = middle)
      (finishes : directed.target = finish) :
      EdgeWalk graph start (traversed ++ [directed]) finish

/-- Cons-oriented view of an edge-aware traversal. It is equivalent to
`EdgeWalk` but exposes consecutive source/target equations directly. -/
inductive EdgeChain (graph : Graph) :
    Vertex → List graph.DirectedEdge → Vertex → Prop where
  | nil (vertex : Vertex) : EdgeChain graph vertex [] vertex
  | cons {start finish : Vertex} {rest : List graph.DirectedEdge}
      (directed : graph.DirectedEdge)
      (starts : directed.source = start)
      (tail : EdgeChain graph directed.target rest finish) :
      EdgeChain graph start (directed :: rest) finish

namespace EdgeChain

theorem appendLast {graph : Graph} {start middle finish : Vertex}
    {traversed : List graph.DirectedEdge}
    (chain : graph.EdgeChain start traversed middle)
    (directed : graph.DirectedEdge)
    (starts : directed.source = middle)
    (finishes : directed.target = finish) :
    graph.EdgeChain start (traversed ++ [directed]) finish := by
  induction chain with
  | nil =>
      apply EdgeChain.cons directed starts
      rw [finishes]
      exact .nil _
  | @cons chainStart chainFinish rest first firstStarts tail ih =>
      exact EdgeChain.cons first firstStarts
        (ih starts)

end EdgeChain

/-- Independent path semantics for the graph checker. -/
inductive Walk (graph : Graph) : Vertex → Vertex → Prop where
  | refl (vertex : Vertex) : Walk graph vertex vertex
  | step {start middle finish : Vertex} :
      Walk graph start middle →
      graph.Adjacent middle finish →
      Walk graph start finish

namespace EdgeWalk

/-- Vertices reached while following an edge-aware traversal, including its
initial vertex. -/
def visitedVertices {graph : Graph} (start : Vertex)
    (traversed : List graph.DirectedEdge) : List Vertex :=
  start :: traversed.map DirectedEdge.target

theorem finish_mem_visitedVertices {graph : Graph} {start finish : Vertex}
    {traversed : List graph.DirectedEdge}
    (walk : graph.EdgeWalk start traversed finish) :
    finish ∈ visitedVertices start traversed := by
  induction walk with
  | refl => simp [visitedVertices]
  | @step start finish traversed prior directed starts finishes ih =>
      simp [visitedVertices, List.map_append, finishes]

theorem mem_visitedVertices_append {graph : Graph} {start vertex : Vertex}
    {traversed suffix : List graph.DirectedEdge}
    (membership : vertex ∈ visitedVertices start traversed) :
    vertex ∈ visitedVertices start (traversed ++ suffix) := by
  simp only [visitedVertices, List.mem_cons] at membership ⊢
  rcases membership with rfl | tailMembership
  · exact .inl rfl
  · exact .inr (by
      rw [List.map_append]
      exact List.mem_append.mpr (.inl tailMembership))

theorem endpoints_mem_visitedVertices {graph : Graph}
    {start finish : Vertex} {traversed : List graph.DirectedEdge}
    (walk : graph.EdgeWalk start traversed finish)
    {directed : graph.DirectedEdge} (membership : directed ∈ traversed) :
    directed.source ∈ visitedVertices start traversed ∧
      directed.target ∈ visitedVertices start traversed := by
  induction walk generalizing directed with
  | refl => simp at membership
  | @step start finish priorSteps prior directedStep starts finishes ih =>
      simp only [List.mem_append, List.mem_singleton] at membership
      rcases membership with earlier | rfl
      · rcases ih earlier with ⟨sourceMembership, targetMembership⟩
        exact ⟨mem_visitedVertices_append sourceMembership,
          mem_visitedVertices_append targetMembership⟩
      · constructor
        · rw [starts]
          exact mem_visitedVertices_append prior.finish_mem_visitedVertices
        · simp [visitedVertices, List.map_append]

theorem getLast_target {graph : Graph} {start finish : Vertex}
    {traversed : List graph.DirectedEdge}
    (walk : graph.EdgeWalk start traversed finish)
    (nonempty : traversed ≠ []) :
    (traversed.getLast nonempty).target = finish := by
  cases walk with
  | refl => exact False.elim (nonempty rfl)
  | @step start finish priorSteps prior directed starts finishes =>
      simpa using finishes

theorem toChain {graph : Graph} {start finish : Vertex}
    {traversed : List graph.DirectedEdge}
    (walk : graph.EdgeWalk start traversed finish) :
    graph.EdgeChain start traversed finish := by
  induction walk with
  | refl => exact .nil _
  | @step start finish priorSteps prior directed starts finishes ih =>
      exact ih.appendLast directed starts finishes

/-- Transport an edge-aware walk through an occurrence mask that keeps every
traversed edge. The returned traversal records the exact compacted indices and
preserves its target-vertex sequence. -/
theorem retainEdges {graph : Graph} {mask : List Bool}
    {start finish : Vertex} {traversed : List graph.DirectedEdge}
    (walk : graph.EdgeWalk start traversed finish)
    (aligned : graph.edges.length = mask.length)
    (allKept : ∀ directed ∈ traversed,
      mask[directed.index]? = some true) :
    ∃ retainedTraversal : List (graph.retainEdges mask).DirectedEdge,
      (graph.retainEdges mask).EdgeWalk start retainedTraversal finish ∧
      retainedTraversal.map DirectedEdge.index =
        traversed.map (fun directed => retainedIndex mask directed.index) ∧
      retainedTraversal.map DirectedEdge.target =
        traversed.map DirectedEdge.target := by
  induction walk with
  | refl => exact ⟨[], .refl _, rfl, rfl⟩
  | @step start finish priorSteps prior directed starts finishes ih =>
      have priorKept : ∀ earlier ∈ priorSteps,
          mask[earlier.index]? = some true := by
        intro earlier earlierMembership
        exact allKept earlier (by simp [earlierMembership])
      rcases ih priorKept with
        ⟨retainedPrior, retainedWalk, indexEquation, targetEquation⟩
      have directedKept : mask[directed.index]? = some true :=
        allKept directed (by simp)
      let retainedDirected := directed.retain aligned directedKept
      refine ⟨retainedPrior ++ [retainedDirected], ?_, ?_, ?_⟩
      · exact EdgeWalk.step retainedWalk retainedDirected
          (by simpa [retainedDirected] using starts)
          (by simpa [retainedDirected] using finishes)
      · simp [List.map_append, indexEquation, retainedDirected,
          DirectedEdge.retain]
      · simp [List.map_append, targetEquation, retainedDirected]

def reverseTraversal {graph : Graph}
    (traversed : List graph.DirectedEdge) : List graph.DirectedEdge :=
  traversed.reverse.map DirectedEdge.reverse

theorem head_reverseTraversal {graph : Graph}
    (traversed : List graph.DirectedEdge) (nonempty : traversed ≠ []) :
    (reverseTraversal traversed).head
        (by simpa [reverseTraversal] using nonempty) =
      (traversed.getLast nonempty).reverse := by
  unfold reverseTraversal
  rw [List.head_map, List.head_reverse]

theorem getLast_reverseTraversal {graph : Graph}
    (traversed : List graph.DirectedEdge) (nonempty : traversed ≠ []) :
    (reverseTraversal traversed).getLast
        (by simpa [reverseTraversal] using nonempty) =
      (traversed.head nonempty).reverse := by
  unfold reverseTraversal
  rw [List.getLast_map, List.getLast_reverse]

theorem trans {graph : Graph} {start middle finish : Vertex}
    {firstSteps secondSteps : List graph.DirectedEdge}
    (first : graph.EdgeWalk start firstSteps middle)
    (second : graph.EdgeWalk middle secondSteps finish) :
    graph.EdgeWalk start (firstSteps ++ secondSteps) finish := by
  induction second with
  | refl => simpa using first
  | @step secondStart secondFinish traversed prior directed starts finishes ih =>
      simpa [List.append_assoc] using
        (EdgeWalk.step ih directed starts finishes)

theorem toWalk {graph : Graph} {start finish : Vertex}
    {traversed : List graph.DirectedEdge}
    (walk : graph.EdgeWalk start traversed finish) :
    graph.Walk start finish := by
  induction walk with
  | refl => exact .refl _
  | @step start finish traversed prior directed starts finishes ih =>
      exact .step ih (by simpa [starts, finishes] using directed.adjacent)

theorem reverse {graph : Graph} {start finish : Vertex}
    {traversed : List graph.DirectedEdge}
    (walk : graph.EdgeWalk start traversed finish) :
    graph.EdgeWalk finish (reverseTraversal traversed) start := by
  induction walk with
  | refl => exact .refl _
  | @step stepStart stepFinish priorSteps prior directed starts finishes ih =>
      have first : graph.EdgeWalk stepFinish [directed.reverse]
          stepStart := by
        apply EdgeWalk.step (.refl stepFinish) directed.reverse
        · rw [DirectedEdge.reverse_source, finishes]
        · rw [DirectedEdge.reverse_target, starts]
      have combined := first.trans ih
      simpa [reverseTraversal] using combined

/-- Reversing a valid traversal reverses its visited-vertex list exactly. -/
theorem visitedVertices_reverse {graph : Graph} {start finish : Vertex}
    {traversed : List graph.DirectedEdge}
    (walk : graph.EdgeWalk start traversed finish) :
    visitedVertices finish (reverseTraversal traversed) =
      (visitedVertices start traversed).reverse := by
  induction walk with
  | refl => simp [visitedVertices, reverseTraversal]
  | @step stepStart stepFinish priorSteps prior directed starts finishes ih =>
      have reversedEquation :
          reverseTraversal (priorSteps ++ [directed]) =
            directed.reverse :: reverseTraversal priorSteps := by
        simp [reverseTraversal]
      rw [reversedEquation]
      simp only [visitedVertices, List.map_cons,
        DirectedEdge.reverse_target]
      rw [starts]
      change stepFinish :: visitedVertices stepStart
          (reverseTraversal priorSteps) = _
      rw [ih]
      simp [visitedVertices, List.map_append, finishes]

end EdgeWalk

namespace EdgeChain

theorem sources_eq_start_targets_dropLast {graph : Graph}
    {start finish : Vertex} {traversed : List graph.DirectedEdge}
    (chain : graph.EdgeChain start traversed finish)
    (nonempty : traversed ≠ []) :
    traversed.map Graph.DirectedEdge.source =
      start :: (traversed.map Graph.DirectedEdge.target).dropLast := by
  induction chain with
  | nil => exact False.elim (nonempty rfl)
  | @cons start finish rest directed starts tail ih =>
      cases rest with
      | nil => simp [starts]
      | cons next remaining =>
          have tailNonempty : next :: remaining ≠ [] := by simp
          rw [List.map_cons, starts, ih tailNonempty]
          simp

theorem split_append {graph : Graph} {start finish : Vertex}
    {leftSteps rightSteps : List graph.DirectedEdge}
    (chain : graph.EdgeChain start (leftSteps ++ rightSteps) finish) :
    ∃ middle,
      graph.EdgeChain start leftSteps middle ∧
        graph.EdgeChain middle rightSteps finish := by
  induction leftSteps generalizing start with
  | nil => exact ⟨start, .nil _, by simpa using chain⟩
  | cons first rest ih =>
      cases chain with
      | cons directed starts tail =>
          rcases ih tail with ⟨middle, prefixChain, suffixChain⟩
          exact ⟨middle, .cons first starts prefixChain, suffixChain⟩

theorem eq_of_nil {graph : Graph} {start finish : Vertex}
    (chain : graph.EdgeChain start [] finish) : start = finish := by
  cases chain
  rfl

/-- A directed traversal list and its start vertex determine its endpoint. -/
theorem finish_unique {graph : Graph} {start firstFinish secondFinish : Vertex}
    {traversed : List graph.DirectedEdge}
    (first : graph.EdgeChain start traversed firstFinish)
    (second : graph.EdgeChain start traversed secondFinish) :
    firstFinish = secondFinish := by
  induction first generalizing secondFinish with
  | nil =>
      cases second
      rfl
  | @cons chainStart chainFinish rest directed starts tail ih =>
      cases second with
      | cons _ secondStarts secondTail =>
          exact ih secondTail

theorem head_source {graph : Graph} {start finish : Vertex}
    {first : graph.DirectedEdge} {rest : List graph.DirectedEdge}
    (chain : graph.EdgeChain start (first :: rest) finish) :
    first.source = start := by
  cases chain
  assumption

theorem toWalk {graph : Graph} {start finish : Vertex}
    {traversed : List graph.DirectedEdge}
    (chain : graph.EdgeChain start traversed finish) :
    graph.EdgeWalk start traversed finish := by
  induction chain with
  | nil => exact .refl _
  | @cons start finish rest directed starts tail ih =>
      have first : graph.EdgeWalk start [directed] directed.target := by
        exact EdgeWalk.step (.refl start) directed starts rfl
      exact first.trans ih

/-- A walk whose visited vertices are duplicate-free cannot reuse an exact
stored edge occurrence in either orientation. -/
theorem edgeIndicesNodup_of_visitedVertices_nodup {graph : Graph}
    {start finish : Vertex} {traversed : List graph.DirectedEdge}
    (chain : graph.EdgeChain start traversed finish)
    (verticesNodup :
      (EdgeWalk.visitedVertices start traversed).Nodup) :
    (traversed.map DirectedEdge.index).Nodup := by
  induction chain with
  | nil => simp
  | @cons chainStart chainFinish rest first starts tail ih =>
      simp only [EdgeWalk.visitedVertices, List.map_cons] at verticesNodup ⊢
      have tailVerticesNodup :
          (first.target :: rest.map DirectedEdge.target).Nodup :=
        (List.nodup_cons.mp verticesNodup).2
      rw [List.nodup_cons]
      constructor
      · intro indexMembership
        rcases List.mem_map.mp indexMembership with
          ⟨later, laterMembership, sameIndex⟩
        have laterTargetMembership : later.target ∈
            rest.map DirectedEdge.target :=
          List.mem_map.mpr ⟨later, laterMembership, rfl⟩
        rcases DirectedEdge.eq_or_eq_reverse_of_index_eq first later
            sameIndex.symm with same | reversed
        · have targetRepeat : first.target ∈
              rest.map DirectedEdge.target := by
            simpa [same] using laterTargetMembership
          exact (List.nodup_cons.mp tailVerticesNodup).1 targetRepeat
        · have startInTail : chainStart ∈
              first.target :: rest.map DirectedEdge.target := by
            right
            have : later.target = chainStart := by
              calc
                later.target = later.reverse.source :=
                  (DirectedEdge.reverse_source later).symm
                _ = first.source :=
                  (congrArg DirectedEdge.source reversed).symm
                _ = chainStart := starts
            rw [this] at laterTargetMembership
            exact laterTargetMembership
          exact (List.nodup_cons.mp verticesNodup).1 startInTail
      · exact ih tailVerticesNodup

end EdgeChain

/-- An edge-identity-aware path with no repeated visited vertex. Unlike
`EdgeSimpleCycle`, its endpoints need not coincide; the empty reflexive path is
also admitted so endpoint openness can be stated by clients when needed. -/
structure EdgeSimplePath (graph : Graph) where
  start : Vertex
  finish : Vertex
  traversed : List graph.DirectedEdge
  walk : graph.EdgeWalk start traversed finish
  verticesNodup :
    (EdgeWalk.visitedVertices start traversed).Nodup

namespace EdgeSimplePath

def vertices {graph : Graph} (path : graph.EdgeSimplePath) : List Vertex :=
  EdgeWalk.visitedVertices path.start path.traversed

@[simp] theorem vertices_nodup {graph : Graph}
    (path : graph.EdgeSimplePath) : path.vertices.Nodup :=
  path.verticesNodup

theorem start_not_mem_vertices_tail {graph : Graph}
    (path : graph.EdgeSimplePath) : path.start ∉ path.vertices.tail := by
  have nodup := path.verticesNodup
  simpa [vertices, EdgeWalk.visitedVertices] using
    (List.nodup_cons.mp nodup).1

@[simp] theorem edgeIndicesNodup {graph : Graph}
    (path : graph.EdgeSimplePath) :
    (path.traversed.map DirectedEdge.index).Nodup :=
  path.walk.toChain.edgeIndicesNodup_of_visitedVertices_nodup
    path.verticesNodup

/-- Reverse a simple open path, preserving its exact edge occurrences and
reversing its visited-vertex list. -/
def reverse {graph : Graph} (path : graph.EdgeSimplePath) :
    graph.EdgeSimplePath where
  start := path.finish
  finish := path.start
  traversed := EdgeWalk.reverseTraversal path.traversed
  walk := path.walk.reverse
  verticesNodup := by
    rw [path.walk.visitedVertices_reverse]
    exact nodup_reverse_of_nodup _ path.verticesNodup

@[simp] theorem reverse_vertices {graph : Graph}
    (path : graph.EdgeSimplePath) :
    path.reverse.vertices = path.vertices.reverse := by
  exact path.walk.visitedVertices_reverse

@[simp] theorem reverse_reverse {graph : Graph}
    (path : graph.EdgeSimplePath) : path.reverse.reverse = path := by
  cases path
  simp [reverse, EdgeWalk.reverseTraversal, List.map_map, Function.comp_def]

theorem start_ne_finish_of_nonempty {graph : Graph}
    (path : graph.EdgeSimplePath) (nonempty : path.traversed ≠ []) :
    path.start ≠ path.finish := by
  intro same
  have lastMembership : path.traversed.getLast nonempty ∈ path.traversed :=
    List.getLast_mem nonempty
  have finishInTail : path.finish ∈
      path.traversed.map DirectedEdge.target := by
    apply List.mem_map.mpr
    refine ⟨path.traversed.getLast nonempty, lastMembership, ?_⟩
    exact path.walk.getLast_target nonempty
  have startFresh : path.start ∉ path.traversed.map DirectedEdge.target := by
    have nodup :
        (path.start :: path.traversed.map DirectedEdge.target).Nodup := by
      simpa [EdgeWalk.visitedVertices] using path.verticesNodup
    exact (List.nodup_cons.mp nodup).1
  exact startFresh (same ▸ finishInTail)

/-- Both endpoints of every exact occurrence traversed by a simple path occur
in its visited-vertex list. -/
theorem directed_endpoints_mem_vertices {graph : Graph}
    (path : graph.EdgeSimplePath) {directed : graph.DirectedEdge}
    (membership : directed ∈ path.traversed) :
    directed.source ∈ path.vertices ∧ directed.target ∈ path.vertices := by
  exact path.walk.endpoints_mem_visitedVertices membership

/-- For a nonempty simple path, its visited vertices are exactly the source of
each traversal edge followed by the final endpoint. -/
theorem vertices_eq_sources_append_finish {graph : Graph}
    (path : graph.EdgeSimplePath) (nonempty : path.traversed ≠ []) :
    path.vertices =
      path.traversed.map DirectedEdge.source ++ [path.finish] := by
  have sources := path.walk.toChain.sources_eq_start_targets_dropLast
    nonempty
  have targetDecomposition := congrArg (List.map DirectedEdge.target)
    (List.dropLast_concat_getLast nonempty)
  simp only [List.map_append, List.map_singleton, List.map_dropLast]
    at targetDecomposition
  rw [path.walk.getLast_target nonempty] at targetDecomposition
  rw [vertices, EdgeWalk.visitedVertices, ← targetDecomposition]
  change (path.start ::
    (path.traversed.map DirectedEdge.target).dropLast) ++ [path.finish] = _
  rw [← sources]

theorem targets_nodup {graph : Graph} (path : graph.EdgeSimplePath) :
    (path.traversed.map DirectedEdge.target).Nodup := by
  have tailNodup := path.verticesNodup.tail
  change (path.traversed.map DirectedEdge.target).Nodup at tailNodup
  exact tailNodup

theorem sources_nodup {graph : Graph} (path : graph.EdgeSimplePath) :
    (path.traversed.map DirectedEdge.source).Nodup := by
  by_cases nonempty : path.traversed ≠ []
  · have nodup := path.verticesNodup
    change path.vertices.Nodup at nodup
    rw [path.vertices_eq_sources_append_finish nonempty,
      List.nodup_append] at nodup
    exact nodup.1
  · simp at nonempty
    simp [nonempty]

theorem finish_not_mem_vertices_dropLast {graph : Graph}
    (path : graph.EdgeSimplePath) (nonempty : path.traversed ≠ []) :
    path.finish ∉ path.vertices.dropLast := by
  have nodup := path.verticesNodup
  change path.vertices.Nodup at nodup
  rw [path.vertices_eq_sources_append_finish nonempty,
    List.nodup_append] at nodup
  have finishNotInSources : path.finish ∉
      path.traversed.map DirectedEdge.source := by
    intro membership
    exact nodup.2.2 path.finish membership path.finish (by simp) rfl
  rw [path.vertices_eq_sources_append_finish nonempty]
  simpa using finishNotInSources

/-- No traversed occurrence can leave the final vertex of a nonempty simple
path. -/
theorem directed_source_ne_finish {graph : Graph}
    (path : graph.EdgeSimplePath) (nonempty : path.traversed ≠ [])
    {directed : graph.DirectedEdge} (membership : directed ∈ path.traversed) :
    directed.source ≠ path.finish := by
  have nodup := path.verticesNodup
  change path.vertices.Nodup at nodup
  rw [path.vertices_eq_sources_append_finish nonempty,
    List.nodup_append] at nodup
  intro same
  exact nodup.2.2 path.finish
    (by
      rw [← same]
      exact List.mem_map.mpr ⟨directed, membership, rfl⟩)
    path.finish (by simp) rfl

/-- The head occurrence of a nonempty simple path leaves its stated start. -/
theorem head_source {graph : Graph} (path : graph.EdgeSimplePath)
    (nonempty : path.traversed ≠ []) :
    (path.traversed.head nonempty).source = path.start := by
  rcases List.exists_cons_of_ne_nil nonempty with
    ⟨first, rest, traversalEquation⟩
  have headOption : path.traversed.head? = some first := by
    simp [traversalEquation]
  have headEquation : path.traversed.head nonempty = first :=
    List.head_of_head?_eq_some headOption
  have chain := path.walk.toChain
  rw [traversalEquation] at chain
  rw [headEquation]
  exact chain.head_source

theorem finish_not_mem_vertices_tail_dropLast {graph : Graph}
    (path : graph.EdgeSimplePath) (nonempty : path.traversed ≠ []) :
    path.finish ∉ path.vertices.tail.dropLast := by
  have targetDecomposition := congrArg (List.map DirectedEdge.target)
    (List.dropLast_concat_getLast nonempty)
  simp only [List.map_append, List.map_singleton, List.map_dropLast]
    at targetDecomposition
  rw [path.walk.getLast_target nonempty] at targetDecomposition
  have targetNodup := path.targets_nodup
  rw [← targetDecomposition, List.nodup_append] at targetNodup
  intro membership
  apply targetNodup.2.2 path.finish membership path.finish (by simp)
  rfl

theorem eq_of_source_eq {graph : Graph} (path : graph.EdgeSimplePath)
    {first second : graph.DirectedEdge}
    (firstMembership : first ∈ path.traversed)
    (secondMembership : second ∈ path.traversed)
    (sameSource : first.source = second.source) : first = second := by
  apply eq_of_map_eq_of_mem_of_nodup path.sources_nodup
    firstMembership secondMembership sameSource

theorem eq_of_target_eq {graph : Graph} (path : graph.EdgeSimplePath)
    {first second : graph.DirectedEdge}
    (firstMembership : first ∈ path.traversed)
    (secondMembership : second ∈ path.traversed)
    (sameTarget : first.target = second.target) : first = second := by
  apply eq_of_map_eq_of_mem_of_nodup path.targets_nodup
    firstMembership secondMembership sameTarget

/-- Every visited vertex other than the finish is the source of an exact edge
occurrence, yielding a traversal decomposition at that outgoing edge. -/
theorem outgoingAtVertex {graph : Graph} (path : graph.EdgeSimplePath)
    {vertex : Vertex} (membership : vertex ∈ path.vertices)
    (notFinish : vertex ≠ path.finish) :
    ∃ before next after,
      path.traversed = before ++ next :: after ∧ next.source = vertex := by
  have nonempty : path.traversed ≠ [] := by
    intro empty
    have chain := path.walk.toChain
    rw [empty] at chain
    have startFinish := chain.eq_of_nil
    have atStart : vertex = path.start := by
      simpa [vertices, EdgeWalk.visitedVertices, empty] using membership
    exact notFinish (atStart.trans startFinish)
  rw [path.vertices_eq_sources_append_finish nonempty,
    List.mem_append] at membership
  rcases membership with inSources | atFinish
  · rcases List.mem_map.mp inSources with
      ⟨next, nextMembership, nextSource⟩
    rcases List.mem_iff_append.mp nextMembership with
      ⟨before, after, traversalEquation⟩
    exact ⟨before, next, after, traversalEquation, nextSource⟩
  · simp at atFinish
    exact False.elim (notFinish atFinish)

/-- Concatenate two simple edge paths when, after deleting the shared start of
the second path, their visited vertex lists are disjoint. -/
def append {graph : Graph} (first second : graph.EdgeSimplePath)
    (meeting : first.finish = second.start)
    (disjoint : ∀ vertex, vertex ∈ first.vertices →
      vertex ∈ second.vertices.tail → False) :
    graph.EdgeSimplePath := by
  have secondWalk : graph.EdgeWalk first.finish second.traversed
      second.finish := by
    rw [meeting]
    exact second.walk
  refine
    { start := first.start
      finish := second.finish
      traversed := first.traversed ++ second.traversed
      walk := first.walk.trans secondWalk
      verticesNodup := ?_ }
  have verticesEquation :
      EdgeWalk.visitedVertices first.start
          (first.traversed ++ second.traversed) =
        first.vertices ++ second.vertices.tail := by
    simp [vertices, EdgeWalk.visitedVertices, List.map_append]
  rw [verticesEquation, List.nodup_append]
  refine ⟨first.verticesNodup, second.verticesNodup.tail, ?_⟩
  intro firstVertex firstMembership secondVertex secondMembership same
  subst secondVertex
  exact disjoint firstVertex firstMembership secondMembership

@[simp] theorem append_start {graph : Graph}
    (first second : graph.EdgeSimplePath)
    (meeting : first.finish = second.start)
    (disjoint : ∀ vertex, vertex ∈ first.vertices →
      vertex ∈ second.vertices.tail → False) :
    (first.append second meeting disjoint).start = first.start := rfl

@[simp] theorem append_finish {graph : Graph}
    (first second : graph.EdgeSimplePath)
    (meeting : first.finish = second.start)
    (disjoint : ∀ vertex, vertex ∈ first.vertices →
      vertex ∈ second.vertices.tail → False) :
    (first.append second meeting disjoint).finish = second.finish := rfl

@[simp] theorem append_traversed {graph : Graph}
    (first second : graph.EdgeSimplePath)
    (meeting : first.finish = second.start)
    (disjoint : ∀ vertex, vertex ∈ first.vertices →
      vertex ∈ second.vertices.tail → False) :
    (first.append second meeting disjoint).traversed =
      first.traversed ++ second.traversed := rfl

@[simp] theorem append_vertices {graph : Graph}
    (first second : graph.EdgeSimplePath)
    (meeting : first.finish = second.start)
    (disjoint : ∀ vertex, vertex ∈ first.vertices →
      vertex ∈ second.vertices.tail → False) :
    (first.append second meeting disjoint).vertices =
      first.vertices ++ second.vertices.tail := by
  simp [append, vertices, EdgeWalk.visitedVertices, List.map_append]

/-- A traversal prefix ending at a selected exact edge occurrence remains a
simple path. -/
theorem prefixPath {graph : Graph} (path : graph.EdgeSimplePath)
    {before after : List graph.DirectedEdge} {last : graph.DirectedEdge}
    (traversalEquation : path.traversed = before ++ last :: after) :
    ∃ initialPath : graph.EdgeSimplePath,
      initialPath.start = path.start ∧
      initialPath.finish = last.target ∧
      initialPath.traversed = before ++ [last] := by
  let prefixSteps := before ++ [last]
  have fullChain := path.walk.toChain
  rw [traversalEquation] at fullChain
  have decomposedChain : graph.EdgeChain path.start
      (prefixSteps ++ after) path.finish := by
    simpa [prefixSteps, List.append_assoc] using fullChain
  rcases decomposedChain.split_append with
    ⟨middle, prefixChain, _⟩
  have prefixWalk := prefixChain.toWalk
  have prefixNonempty : prefixSteps ≠ [] := by simp [prefixSteps]
  have finishEquation : middle = last.target := by
    have lastTarget := prefixWalk.getLast_target prefixNonempty
    simpa [prefixSteps] using lastTarget.symm
  rw [finishEquation] at prefixWalk
  refine ⟨
    { start := path.start
      finish := last.target
      traversed := prefixSteps
      walk := prefixWalk
      verticesNodup := ?_ }, rfl, rfl, by rfl⟩
  have fullNodup := path.verticesNodup
  rw [traversalEquation] at fullNodup
  have decomposedNodup :
      ((path.start :: prefixSteps.map DirectedEdge.target) ++
        after.map DirectedEdge.target).Nodup := by
    simpa [EdgeWalk.visitedVertices, prefixSteps, List.append_assoc] using
      fullNodup
  exact (List.nodup_append.mp decomposedNodup).1

/-- A traversal suffix beginning at a selected exact edge occurrence remains
a simple path from that edge's source to the original finish. -/
theorem suffixPath {graph : Graph} (path : graph.EdgeSimplePath)
    {before after : List graph.DirectedEdge} {first : graph.DirectedEdge}
    (traversalEquation : path.traversed = before ++ first :: after) :
    ∃ suffix : graph.EdgeSimplePath,
      suffix.start = first.source ∧
      suffix.finish = path.finish ∧
      suffix.traversed = first :: after ∧
      ∀ vertex, vertex ∈ suffix.vertices → vertex ∈ path.vertices := by
  have fullChain := path.walk.toChain
  rw [traversalEquation] at fullChain
  rcases fullChain.split_append with
    ⟨middle, prefixChain, suffixChain⟩
  have suffixStart : middle = first.source :=
    suffixChain.head_source.symm
  have suffixWalk := suffixChain.toWalk
  rw [suffixStart] at suffixWalk
  refine ⟨
    { start := first.source
      finish := path.finish
      traversed := first :: after
      walk := suffixWalk
      verticesNodup := ?_ }, rfl, rfl, rfl, ?_⟩
  have fullNodup := path.verticesNodup
  rw [traversalEquation] at fullNodup
  have decomposedNodup :
      ((path.start :: before.map DirectedEdge.target) ++
        (first :: after).map DirectedEdge.target).Nodup := by
    simpa [EdgeWalk.visitedVertices, List.map_append] using fullNodup
  have parts := List.nodup_append.mp decomposedNodup
  change (first.source ::
    (first :: after).map DirectedEdge.target).Nodup
  rw [List.nodup_cons]
  constructor
  · intro firstTargetMembership
    have middleMembership : middle ∈
        EdgeWalk.visitedVertices path.start before :=
      prefixChain.toWalk.finish_mem_visitedVertices
    have firstSourceMembership : first.source ∈
        path.start :: before.map DirectedEdge.target := by
      simpa [EdgeWalk.visitedVertices, suffixStart] using middleMembership
    exact parts.2.2 first.source firstSourceMembership first.source
      firstTargetMembership rfl
  · exact parts.2.1
  intro vertex membership
  simp only [vertices, EdgeWalk.visitedVertices, List.mem_cons,
    List.mem_map] at membership ⊢
  rcases membership with atSource | atTarget
  · have firstMembership : first ∈ path.traversed := by
      rw [traversalEquation]
      simp
    have sourceMembership :=
      (path.walk.endpoints_mem_visitedVertices firstMembership).1
    rw [atSource]
    simpa [EdgeWalk.visitedVertices] using sourceMembership
  · rcases atTarget with ⟨directed, directedMembership, targetEquation⟩
    have fullMembership : directed ∈ path.traversed := by
      rw [traversalEquation]
      simp only [List.mem_append, List.mem_cons]
      exact .inr directedMembership
    have targetMembership :=
      (path.walk.endpoints_mem_visitedVertices fullMembership).2
    rw [targetEquation] at targetMembership
    simpa [EdgeWalk.visitedVertices] using targetMembership

/-- Every edge occurrence traversed by a simple path has distinct endpoints. -/
theorem directed_source_ne_target {graph : Graph}
    (path : graph.EdgeSimplePath) {directed : graph.DirectedEdge}
    (membership : directed ∈ path.traversed) :
    directed.source ≠ directed.target := by
  rcases List.mem_iff_append.mp membership with
    ⟨before, after, traversalEquation⟩
  rcases path.suffixPath traversalEquation with
    ⟨suffix, _suffixStarts, _suffixFinishes, suffixSteps, _subset⟩
  have nodup := suffix.verticesNodup
  rw [suffixSteps] at nodup
  rw [_suffixStarts] at nodup
  change (directed.source :: directed.target ::
    after.map DirectedEdge.target).Nodup at nodup
  exact fun same => (List.nodup_cons.mp nodup).1 (by simp [same])

/-- Every visited vertex after the start is the endpoint of a simple traversal
prefix, with an exact list decomposition at its last edge. -/
theorem prefixToTailVertex {graph : Graph} (path : graph.EdgeSimplePath)
    {vertex : Vertex} (membership : vertex ∈ path.vertices.tail) :
    ∃ (initialPath : graph.EdgeSimplePath)
      (before after : List graph.DirectedEdge) (last : graph.DirectedEdge),
      path.traversed = before ++ last :: after ∧
      initialPath.start = path.start ∧
      initialPath.finish = vertex ∧
      initialPath.traversed = before ++ [last] ∧
      last.target = vertex := by
  have targetMembership :
      vertex ∈ path.traversed.map DirectedEdge.target := by
    simpa [vertices, EdgeWalk.visitedVertices] using membership
  rcases List.mem_map.mp targetMembership with
    ⟨last, lastMembership, lastTarget⟩
  rcases List.mem_iff_append.mp lastMembership with
    ⟨before, after, traversalEquation⟩
  rcases path.prefixPath traversalEquation with
    ⟨initialPath, prefixStarts, prefixFinishes, prefixSteps⟩
  refine ⟨initialPath, before, after, last, traversalEquation, prefixStarts,
    ?_, prefixSteps, lastTarget⟩
  exact prefixFinishes.trans lastTarget

end EdgeSimplePath

/-- A nonempty closed edge-aware walk with no repeated vertex except its
identified start/end. The exact edge indices allow two parallel stored edges
to form a genuine length-two multigraph cycle. -/
structure EdgeSimpleCycle (graph : Graph) where
  start : Vertex
  traversed : List graph.DirectedEdge
  nonempty : traversed ≠ []
  walk : graph.EdgeWalk start traversed start
  edgeIndicesNodup : (traversed.map DirectedEdge.index).Nodup
  interiorNodup :
    (start :: traversed.dropLast.map DirectedEdge.target).Nodup

namespace EdgeSimpleCycle

/-- Close two oppositely directed simple paths into an exact simple cycle.
The second path's final return to the first start is omitted from the interior
vertex comparison, while edge-occurrence disjointness remains explicit. -/
def ofTwoPaths {graph : Graph}
    (first second : graph.EdgeSimplePath)
    (firstNonempty : first.traversed ≠ [])
    (secondNonempty : second.traversed ≠ [])
    (meeting : first.finish = second.start)
    (closing : second.finish = first.start)
    (vertexDisjoint : ∀ vertex, vertex ∈ first.vertices →
      vertex ∈ second.vertices.tail.dropLast → False)
    (edgeDisjoint : ∀ index,
      index ∈ first.traversed.map DirectedEdge.index →
      index ∈ second.traversed.map DirectedEdge.index → False) :
    graph.EdgeSimpleCycle := by
  have secondWalk : graph.EdgeWalk first.finish second.traversed
      first.start := by
    rw [meeting]
    simpa only [closing] using second.walk
  refine
    { start := first.start
      traversed := first.traversed ++ second.traversed
      nonempty := by simp [firstNonempty]
      walk := first.walk.trans secondWalk
      edgeIndicesNodup := ?_
      interiorNodup := ?_ }
  · rw [List.map_append, List.nodup_append]
    exact ⟨first.edgeIndicesNodup, second.edgeIndicesNodup,
      fun firstIndex firstMembership secondIndex secondMembership same =>
        edgeDisjoint firstIndex firstMembership (same ▸ secondMembership)⟩
  · change (first.start ::
      (first.traversed ++ second.traversed).dropLast.map
        DirectedEdge.target).Nodup
    rw [List.dropLast_append_of_ne_nil secondNonempty, List.map_append]
    change (first.vertices ++
      second.traversed.dropLast.map DirectedEdge.target).Nodup
    rw [List.nodup_append]
    refine ⟨first.verticesNodup, ?_, ?_⟩
    · have secondTargetsNodup :
          (second.traversed.map DirectedEdge.target).Nodup := by
        have tailNodup := second.verticesNodup.tail
        change (second.traversed.map DirectedEdge.target).Nodup at tailNodup
        exact tailNodup
      have targetsNonempty :
          second.traversed.map DirectedEdge.target ≠ [] := by
        simp [secondNonempty]
      have targetDecomposition :=
        List.dropLast_concat_getLast targetsNonempty
      rw [← targetDecomposition] at secondTargetsNodup
      rw [List.map_dropLast]
      exact (List.nodup_append.mp secondTargetsNodup).1
    · intro firstVertex firstMembership secondVertex secondMembership same
      subst secondVertex
      apply vertexDisjoint firstVertex firstMembership
      simpa [EdgeSimplePath.vertices, EdgeWalk.visitedVertices,
        List.map_dropLast] using secondMembership

@[simp] theorem ofTwoPaths_traversed {graph : Graph}
    (first second : graph.EdgeSimplePath)
    (firstNonempty : first.traversed ≠ [])
    (secondNonempty : second.traversed ≠ [])
    (meeting : first.finish = second.start)
    (closing : second.finish = first.start)
    (vertexDisjoint : ∀ vertex, vertex ∈ first.vertices →
      vertex ∈ second.vertices.tail.dropLast → False)
    (edgeDisjoint : ∀ index,
      index ∈ first.traversed.map DirectedEdge.index →
      index ∈ second.traversed.map DirectedEdge.index → False) :
    (ofTwoPaths first second firstNonempty secondNonempty meeting closing
      vertexDisjoint edgeDisjoint).traversed =
      first.traversed ++ second.traversed := rfl

def vertices {graph : Graph} (cycle : graph.EdgeSimpleCycle) : List Vertex :=
  cycle.start :: cycle.traversed.dropLast.map DirectedEdge.target

@[simp] theorem vertices_nodup {graph : Graph}
    (cycle : graph.EdgeSimpleCycle) : cycle.vertices.Nodup :=
  cycle.interiorNodup

theorem targets_eq {graph : Graph} (cycle : graph.EdgeSimpleCycle) :
    cycle.traversed.map DirectedEdge.target =
      cycle.traversed.dropLast.map DirectedEdge.target ++ [cycle.start] := by
  have decomposition := congrArg (List.map DirectedEdge.target)
    (List.dropLast_concat_getLast cycle.nonempty)
  simp only [List.map_append, List.map_singleton] at decomposition
  rw [cycle.walk.getLast_target cycle.nonempty] at decomposition
  exact decomposition.symm

@[simp] theorem vertices_length {graph : Graph}
    (cycle : graph.EdgeSimpleCycle) :
    cycle.vertices.length = cycle.traversed.length := by
  have positive : 0 < cycle.traversed.length :=
    List.length_pos_iff.mpr cycle.nonempty
  simp [vertices, List.length_dropLast]
  omega

theorem directed_endpoints_mem_vertices {graph : Graph}
    (cycle : graph.EdgeSimpleCycle) {directed : graph.DirectedEdge}
    (membership : directed ∈ cycle.traversed) :
    directed.source ∈ cycle.vertices ∧ directed.target ∈ cycle.vertices := by
  have endpoints := cycle.walk.endpoints_mem_visitedVertices membership
  constructor
  · have sourceMembership := endpoints.1
    simp only [EdgeWalk.visitedVertices] at sourceMembership
    rw [targets_eq cycle] at sourceMembership
    simp only [vertices, List.mem_cons, List.mem_append] at sourceMembership ⊢
    rcases sourceMembership with atStart | inInterior | atEnd
    · exact .inl atStart
    · exact .inr inInterior
    · rcases atEnd with atEnd | impossible
      · exact .inl atEnd
      · simp at impossible
  · have targetMembership := endpoints.2
    simp only [EdgeWalk.visitedVertices] at targetMembership
    rw [targets_eq cycle] at targetMembership
    simp only [vertices, List.mem_cons, List.mem_append] at targetMembership ⊢
    rcases targetMembership with atStart | inInterior | atEnd
    · exact .inl atStart
    · exact .inr inInterior
    · rcases atEnd with atEnd | impossible
      · exact .inl atEnd
      · simp at impossible

theorem edge_endpoints_mem_vertices {graph : Graph}
    (cycle : graph.EdgeSimpleCycle) {directed : graph.DirectedEdge}
    (membership : directed ∈ cycle.traversed) :
    directed.edge.first ∈ cycle.vertices ∧
      directed.edge.second ∈ cycle.vertices := by
  have endpoints := cycle.directed_endpoints_mem_vertices membership
  cases direction : directed.forward with
  | false =>
      exact ⟨by
        simpa [DirectedEdge.source, DirectedEdge.target, direction] using
          endpoints.2, by
        simpa [DirectedEdge.source, DirectedEdge.target, direction] using
          endpoints.1⟩
  | true =>
      simpa [DirectedEdge.source, DirectedEdge.target, direction] using endpoints

/-- A path whose start and every exact directed occurrence lie in a simple
cycle visits only vertices of that cycle. -/
theorem path_vertices_subset {graph : Graph}
    (cycle : graph.EdgeSimpleCycle) (path : graph.EdgeSimplePath)
    (startInCycle : path.start ∈ cycle.vertices)
    (edgeSubset : ∀ directed, directed ∈ path.traversed →
      directed ∈ cycle.traversed) :
    ∀ vertex, vertex ∈ path.vertices → vertex ∈ cycle.vertices := by
  intro vertex membership
  simp only [EdgeSimplePath.vertices, EdgeWalk.visitedVertices,
    List.mem_cons] at membership
  rcases membership with atStart | inTargets
  · simpa [atStart] using startInCycle
  · rcases List.mem_map.mp inTargets with
      ⟨directed, directedMembership, targetEquation⟩
    rw [← targetEquation]
    exact (cycle.directed_endpoints_mem_vertices
      (edgeSubset directed directedMembership)).2

theorem sources_eq_vertices {graph : Graph}
    (cycle : graph.EdgeSimpleCycle) :
    cycle.traversed.map Graph.DirectedEdge.source = cycle.vertices := by
  have sources := cycle.walk.toChain.sources_eq_start_targets_dropLast
    cycle.nonempty
  simpa [vertices, List.map_dropLast] using sources

theorem sources_nodup {graph : Graph} (cycle : graph.EdgeSimpleCycle) :
    (cycle.traversed.map Graph.DirectedEdge.source).Nodup := by
  rw [cycle.sources_eq_vertices]
  exact cycle.vertices_nodup

theorem targets_nodup {graph : Graph} (cycle : graph.EdgeSimpleCycle) :
    (cycle.traversed.map Graph.DirectedEdge.target).Nodup := by
  rw [cycle.targets_eq]
  have permutation :
      (cycle.traversed.dropLast.map Graph.DirectedEdge.target ++ [cycle.start]).Perm
        cycle.vertices := by
    simp [vertices]
  exact permutation.nodup_iff.mpr cycle.vertices_nodup

/-- Rotate a simple cycle to begin at an exact traversal occurrence. -/
theorem rotateAt_exists {graph : Graph} (cycle : graph.EdgeSimpleCycle)
    {before after : List graph.DirectedEdge} {first : graph.DirectedEdge}
    (traversalEquation : cycle.traversed = before ++ first :: after) :
    ∃ rotated : graph.EdgeSimpleCycle,
      rotated.start = first.source ∧
      rotated.traversed = (first :: after) ++ before := by
  have fullChain := cycle.walk.toChain
  rw [traversalEquation] at fullChain
  rcases fullChain.split_append with
    ⟨middle, prefixChain, suffixChain⟩
  have middleEquation : middle = first.source :=
    suffixChain.head_source.symm
  have suffixWalk := suffixChain.toWalk
  rw [middleEquation] at suffixWalk
  have prefixWalk := prefixChain.toWalk
  rw [middleEquation] at prefixWalk
  have rotatedWalk : graph.EdgeWalk first.source
      ((first :: after) ++ before) first.source :=
    suffixWalk.trans prefixWalk
  have originalIndexNodup := cycle.edgeIndicesNodup
  rw [traversalEquation, List.map_append, List.nodup_append]
    at originalIndexNodup
  have rotatedIndexNodup :
      (((first :: after) ++ before).map DirectedEdge.index).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨originalIndexNodup.2.1, originalIndexNodup.1, ?_⟩
    intro afterIndex afterMembership beforeIndex beforeMembership same
    exact originalIndexNodup.2.2 beforeIndex beforeMembership afterIndex
      afterMembership same.symm
  have originalSourceNodup := cycle.sources_nodup
  rw [traversalEquation, List.map_append, List.nodup_append]
    at originalSourceNodup
  have rotatedSourceNodup :
      (((first :: after) ++ before).map DirectedEdge.source).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨originalSourceNodup.2.1, originalSourceNodup.1, ?_⟩
    intro afterSource afterMembership beforeSource beforeMembership same
    exact originalSourceNodup.2.2 beforeSource beforeMembership afterSource
      afterMembership same.symm
  refine ⟨
    { start := first.source
      traversed := (first :: after) ++ before
      nonempty := by simp
      walk := rotatedWalk
      edgeIndicesNodup := rotatedIndexNodup
      interiorNodup := ?_ }, rfl, rfl⟩
  have sourceEquation :=
    rotatedWalk.toChain.sources_eq_start_targets_dropLast (by simp)
  rw [List.map_dropLast]
  rw [← sourceEquation]
  exact rotatedSourceNodup

theorem eq_of_source_eq {graph : Graph} (cycle : graph.EdgeSimpleCycle)
    {first second : graph.DirectedEdge}
    (firstMembership : first ∈ cycle.traversed)
    (secondMembership : second ∈ cycle.traversed)
    (same : first.source = second.source) : first = second :=
  eq_of_map_eq_of_mem_of_nodup cycle.sources_nodup firstMembership
    secondMembership same

theorem eq_of_target_eq {graph : Graph} (cycle : graph.EdgeSimpleCycle)
    {first second : graph.DirectedEdge}
    (firstMembership : first ∈ cycle.traversed)
    (secondMembership : second ∈ cycle.traversed)
    (same : first.target = second.target) : first = second :=
  eq_of_map_eq_of_mem_of_nodup cycle.targets_nodup firstMembership
    secondMembership same

/-- Consecutive traversal edges, including the wrap-around transition from the
last edge back to the first edge. -/
def CyclicSuccessor {graph : Graph} (cycle : graph.EdgeSimpleCycle)
    (incoming outgoing : graph.DirectedEdge) : Prop :=
  (∃ before after,
    cycle.traversed = before ++ incoming :: outgoing :: after) ∨
  (∃ middle,
    cycle.traversed = (outgoing :: middle) ++ [incoming])

theorem successor_of_target_eq_source {graph : Graph}
    (cycle : graph.EdgeSimpleCycle) {incoming outgoing : graph.DirectedEdge}
    (incomingMembership : incoming ∈ cycle.traversed)
    (outgoingMembership : outgoing ∈ cycle.traversed)
    (different : incoming ≠ outgoing)
    (meeting : incoming.target = outgoing.source) :
    cycle.CyclicSuccessor incoming outgoing := by
  rcases List.mem_iff_append.mp incomingMembership with
    ⟨before, after, traversalEquation⟩
  have chain := cycle.walk.toChain
  rw [traversalEquation] at chain
  rcases chain.split_append with
    ⟨middle, beforeChain, incomingChain⟩
  cases incomingChain with
  | cons directed starts tailChain =>
      cases after with
      | nil =>
          cases before with
          | nil =>
              have onlyIncoming : outgoing = incoming := by
                simpa [traversalEquation] using outgoingMembership
              exact False.elim (different onlyIncoming.symm)
          | cons first rest =>
              have firstMembership : first ∈ cycle.traversed := by
                rw [traversalEquation]
                simp
              have incomingTargetStart : incoming.target = cycle.start := by
                exact EdgeChain.eq_of_nil tailChain
              have firstSourceStart : first.source = cycle.start := by
                have fullChain := cycle.walk.toChain
                rw [traversalEquation] at fullChain
                exact EdgeChain.head_source fullChain
              have firstIsOutgoing := cycle.eq_of_source_eq firstMembership
                outgoingMembership (by
                  rw [firstSourceStart, ← incomingTargetStart, meeting])
              subst first
              exact .inr ⟨rest, by simpa using traversalEquation⟩
      | cons next rest =>
          have nextMembership : next ∈ cycle.traversed := by
            rw [traversalEquation]
            simp
          have nextStarts : next.source = incoming.target := by
            cases tailChain
            assumption
          have nextIsOutgoing := cycle.eq_of_source_eq nextMembership
            outgoingMembership (nextStarts.trans meeting)
          subst next
          exact .inl ⟨before, rest, traversalEquation⟩

/-- Reverse the orientation and order of a simple cycle while keeping the same
base vertex. Exact edge indices remain duplicate-free, and the interior vertex
list is reversed. -/
def reverse {graph : Graph} (cycle : graph.EdgeSimpleCycle) :
    graph.EdgeSimpleCycle := by
  have reversedNonempty :
      EdgeWalk.reverseTraversal cycle.traversed ≠ [] := by
    simp [EdgeWalk.reverseTraversal, cycle.nonempty]
  refine
    { start := cycle.start
      traversed := EdgeWalk.reverseTraversal cycle.traversed
      nonempty := reversedNonempty
      walk := cycle.walk.reverse
      edgeIndicesNodup := ?_
      interiorNodup := ?_ }
  · have reversedIndices :=
      nodup_reverse_of_nodup _ cycle.edgeIndicesNodup
    simpa [EdgeWalk.reverseTraversal, List.map_map, Function.comp_def] using
      reversedIndices
  · have reversedTargets :
        (EdgeWalk.reverseTraversal cycle.traversed).map
            Graph.DirectedEdge.target =
          (cycle.traversed.map Graph.DirectedEdge.source).reverse := by
      simp [EdgeWalk.reverseTraversal, List.map_map, Function.comp_def]
    change (cycle.start ::
      (EdgeWalk.reverseTraversal cycle.traversed).dropLast.map
        Graph.DirectedEdge.target).Nodup
    rw [List.map_dropLast, reversedTargets, cycle.sources_eq_vertices]
    simp only [vertices, List.reverse_cons, List.dropLast_concat]
    have originalNodup := cycle.interiorNodup
    rw [List.nodup_cons] at originalNodup ⊢
    have interiorReverseNodup :
        (cycle.traversed.dropLast.map
          Graph.DirectedEdge.target).reverse.Nodup :=
      nodup_reverse_of_nodup _ originalNodup.2
    exact ⟨by simpa using originalNodup.1, interiorReverseNodup⟩

theorem mem_targets_iff_mem_vertices {graph : Graph}
    (cycle : graph.EdgeSimpleCycle) (vertex : Vertex) :
    vertex ∈ cycle.traversed.map DirectedEdge.target ↔
      vertex ∈ cycle.vertices := by
  rw [cycle.targets_eq]
  simp [vertices, or_comm]

/-- Reversing a simple cycle changes orientations and order, but not its
underlying finite set of visited vertices. -/
theorem mem_reverse_vertices_iff {graph : Graph}
    (cycle : graph.EdgeSimpleCycle) (vertex : Vertex) :
    vertex ∈ cycle.reverse.vertices ↔ vertex ∈ cycle.vertices := by
  constructor
  · intro membership
    rw [← cycle.reverse.sources_eq_vertices] at membership
    rcases List.mem_map.mp membership with
      ⟨reversedEdge, reversedMembership, sourceEquation⟩
    simp only [reverse, EdgeWalk.reverseTraversal, List.mem_map,
      List.mem_reverse] at reversedMembership
    rcases reversedMembership with
      ⟨originalEdge, originalMembership, reversedEquation⟩
    have targetInCycle :=
      (cycle.directed_endpoints_mem_vertices originalMembership).2
    rw [← sourceEquation, ← reversedEquation,
      DirectedEdge.reverse_source]
    exact targetInCycle
  · intro membership
    have targetMembership : vertex ∈
        cycle.traversed.map DirectedEdge.target :=
      (cycle.mem_targets_iff_mem_vertices vertex).2 membership
    rcases List.mem_map.mp targetMembership with
      ⟨originalEdge, originalMembership, targetEquation⟩
    rw [← cycle.reverse.sources_eq_vertices]
    apply List.mem_map.mpr
    refine ⟨originalEdge.reverse, ?_, ?_⟩
    · change originalEdge.reverse ∈
          cycle.traversed.reverse.map DirectedEdge.reverse
      apply List.mem_map.mpr
      exact ⟨originalEdge, by simpa using originalMembership, rfl⟩
    · rw [DirectedEdge.reverse_source]
      exact targetEquation

/-- The prefix ending at an internal incoming edge of a simple cycle is a
simple open path from the cycle base to that edge's target. The nonempty
remaining suffix ensures the repeated closing base is not included. -/
theorem prefixPath {graph : Graph} (cycle : graph.EdgeSimpleCycle)
    {before after : List graph.DirectedEdge}
    {incoming outgoing : graph.DirectedEdge}
    (traversalEquation :
      cycle.traversed = before ++ incoming :: outgoing :: after) :
    ∃ path : graph.EdgeSimplePath,
      path.start = cycle.start ∧
      path.finish = incoming.target ∧
      path.traversed = before ++ [incoming] := by
  let prefixSteps := before ++ [incoming]
  have fullChain := cycle.walk.toChain
  rw [traversalEquation] at fullChain
  have decomposedChain : graph.EdgeChain cycle.start
      (prefixSteps ++ outgoing :: after) cycle.start := by
    simpa [prefixSteps, List.append_assoc] using fullChain
  rcases decomposedChain.split_append with
    ⟨middle, prefixChain, _⟩
  have prefixWalk := prefixChain.toWalk
  have prefixNonempty : prefixSteps ≠ [] := by
    simp [prefixSteps]
  have finishEquation : middle = incoming.target := by
    have lastTarget := prefixWalk.getLast_target prefixNonempty
    simpa [prefixSteps] using lastTarget.symm
  rw [finishEquation] at prefixWalk
  refine ⟨
    { start := cycle.start
      finish := incoming.target
      traversed := prefixSteps
      walk := prefixWalk
      verticesNodup := ?_ }, rfl, rfl, by rfl⟩
  have interiorNodup := cycle.interiorNodup
  rw [traversalEquation] at interiorNodup
  have decomposedInteriorNodup : (cycle.start ::
      (prefixSteps ++ outgoing :: after).dropLast.map
        Graph.DirectedEdge.target).Nodup := by
    simpa [prefixSteps, List.append_assoc] using interiorNodup
  rw [List.dropLast_append_of_ne_nil (by simp : outgoing :: after ≠ [])]
    at decomposedInteriorNodup
  rw [List.map_append] at decomposedInteriorNodup
  change ((cycle.start ::
      prefixSteps.map Graph.DirectedEdge.target) ++
        (outgoing :: after).dropLast.map
          Graph.DirectedEdge.target).Nodup at decomposedInteriorNodup
  exact (List.nodup_append.mp decomposedInteriorNodup).1

/-- A prefix immediately before a selected outgoing occurrence is a
simple path ending at that occurrence's source. -/
theorem prefixBefore {graph : Graph} (cycle : graph.EdgeSimpleCycle)
    {initialSteps after : List graph.DirectedEdge}
    {outgoing : graph.DirectedEdge}
    (traversalEquation :
      cycle.traversed = initialSteps ++ outgoing :: after) :
    ∃ path : graph.EdgeSimplePath,
      path.start = cycle.start ∧
      path.finish = outgoing.source ∧
      path.traversed = initialSteps ∧
      ∀ vertex, vertex ∈ path.vertices → vertex ∈ cycle.vertices := by
  have fullChain := cycle.walk.toChain
  rw [traversalEquation] at fullChain
  rcases fullChain.split_append with
    ⟨middle, prefixChain, suffixChain⟩
  have finishEquation : middle = outgoing.source :=
    suffixChain.head_source.symm
  have prefixWalk := prefixChain.toWalk
  rw [finishEquation] at prefixWalk
  have interiorNodup := cycle.interiorNodup
  rw [traversalEquation,
    List.dropLast_append_of_ne_nil (by simp : outgoing :: after ≠ []),
    List.map_append] at interiorNodup
  have decomposedNodup :
      ((cycle.start :: initialSteps.map DirectedEdge.target) ++
        (outgoing :: after).dropLast.map DirectedEdge.target).Nodup := by
    simpa using interiorNodup
  let path : graph.EdgeSimplePath :=
    { start := cycle.start
      finish := outgoing.source
      traversed := initialSteps
      walk := prefixWalk
      verticesNodup := (List.nodup_append.mp decomposedNodup).1 }
  refine ⟨path, rfl, rfl, rfl, ?_⟩
  intro vertex membership
  have prefixMembership : vertex ∈
      cycle.start :: initialSteps.map DirectedEdge.target := by
    simpa [path, EdgeSimplePath.vertices, EdgeWalk.visitedVertices] using
      membership
  change vertex ∈
    cycle.start :: cycle.traversed.dropLast.map DirectedEdge.target
  rw [traversalEquation,
    List.dropLast_append_of_ne_nil (by simp : outgoing :: after ≠ []),
    List.map_append]
  change vertex ∈
    (cycle.start :: initialSteps.map DirectedEdge.target) ++
      (outgoing :: after).dropLast.map DirectedEdge.target
  exact List.mem_append.mpr (.inl prefixMembership)

/-- Given two consecutive cusp edges later in a cycle, extract the complementary
simple path that starts with the outgoing cusp edge, wraps through the cycle
base, and stops just before a selected earlier outgoing edge. -/
theorem complementPath {graph : Graph} (cycle : graph.EdgeSimpleCycle)
    {before between after : List graph.DirectedEdge}
    {outgoingAtVertex cuspIncoming cuspOutgoing : graph.DirectedEdge}
    (traversalEquation : cycle.traversed =
      before ++ outgoingAtVertex :: between ++
        cuspIncoming :: cuspOutgoing :: after) :
    ∃ path : graph.EdgeSimplePath,
      path.start = cuspOutgoing.source ∧
      path.finish = outgoingAtVertex.source ∧
      path.traversed = (cuspOutgoing :: after) ++ before ∧
      cycle.start ∈ path.vertices.tail ∧
      (∀ vertex, vertex ∈ path.vertices → vertex ∈ cycle.vertices) ∧
      ∀ index, index ∈ path.traversed.map DirectedEdge.index →
        index ∈ cycle.traversed.map DirectedEdge.index := by
  let beforeRotation :=
    before ++ outgoingAtVertex :: between ++ [cuspIncoming]
  have rotationEquation : cycle.traversed =
      beforeRotation ++ cuspOutgoing :: after := by
    simpa [beforeRotation, List.append_assoc] using traversalEquation
  rcases cycle.rotateAt_exists rotationEquation with
    ⟨rotated, rotatedStart, rotatedSteps⟩
  have rotatedDecomposition : rotated.traversed =
      ((cuspOutgoing :: after) ++ before) ++
        outgoingAtVertex :: (between ++ [cuspIncoming]) := by
    rw [rotatedSteps]
    simp [beforeRotation, List.append_assoc]
  rcases rotated.prefixBefore rotatedDecomposition with
    ⟨path, pathStarts, pathFinishes, pathSteps, pathSubset⟩
  have traversalPermutation : rotated.traversed.Perm cycle.traversed := by
    rw [rotatedSteps, traversalEquation]
    simpa [beforeRotation, List.append_assoc] using
      ((List.perm_append_comm :
        (beforeRotation ++ (cuspOutgoing :: after)).Perm
          ((cuspOutgoing :: after) ++ beforeRotation)).symm)
  have suffixNonempty : cuspOutgoing :: after ≠ [] := by simp
  have groupedTraversal : cycle.traversed =
      (before ++ outgoingAtVertex :: between ++ [cuspIncoming]) ++
        (cuspOutgoing :: after) := by
    simpa [List.append_assoc] using traversalEquation
  let oldLast := (cuspOutgoing :: after).getLast suffixNonempty
  have oldLastTarget : oldLast.target = cycle.start := by
    have cycleLastTarget := cycle.walk.getLast_target cycle.nonempty
    have cycleLastOption : cycle.traversed.getLast? = some oldLast := by
      rw [groupedTraversal, List.getLast?_append,
        List.getLast?_eq_some_getLast suffixNonempty]
      simp [oldLast]
    have cycleLastEquation :
        cycle.traversed.getLast cycle.nonempty = oldLast :=
      List.getLast_of_getLast?_eq_some cycleLastOption
    rw [cycleLastEquation] at cycleLastTarget
    exact cycleLastTarget
  have oldLastInPath : oldLast ∈ path.traversed := by
    rw [pathSteps]
    exact List.mem_append.mpr
      (.inl (List.getLast_mem suffixNonempty))
  have baseInPathTail : cycle.start ∈ path.vertices.tail := by
    change cycle.start ∈ path.traversed.map DirectedEdge.target
    rw [← oldLastTarget]
    exact List.mem_map.mpr ⟨oldLast, oldLastInPath, rfl⟩
  refine ⟨path, pathStarts.trans rotatedStart,
    pathFinishes, pathSteps, baseInPathTail, ?_, ?_⟩
  intro vertex membership
  have inRotated := pathSubset vertex membership
  rw [← rotated.sources_eq_vertices] at inRotated
  rcases List.mem_map.mp inRotated with
    ⟨directed, directedMembership, sourceEquation⟩
  have originalMembership : directed ∈ cycle.traversed :=
    traversalPermutation.mem_iff.mp directedMembership
  rw [← sourceEquation]
  exact (cycle.directed_endpoints_mem_vertices originalMembership).1
  intro index indexMembership
  rcases List.mem_map.mp indexMembership with
    ⟨directed, directedMembership, indexEquation⟩
  have inRotated : directed ∈ rotated.traversed := by
    rw [rotatedSteps]
    rw [pathSteps] at directedMembership
    rcases List.mem_append.mp directedMembership with inWrap | inBefore
    · exact List.mem_append.mpr (.inl inWrap)
    · exact List.mem_append.mpr (.inr (by
        simp [beforeRotation, inBefore]))
  have inOriginal : directed ∈ cycle.traversed :=
    traversalPermutation.mem_iff.mp inRotated
  exact List.mem_map.mpr ⟨directed, inOriginal, indexEquation⟩

/-- Extract the contiguous old-cycle arc from a selected outgoing occurrence
through a later incoming occurrence, stopping immediately before its successor.
The exact edge indices and all visited vertices remain contained in the cycle.
-/
theorem middlePath {graph : Graph} (cycle : graph.EdgeSimpleCycle)
    {before between after : List graph.DirectedEdge}
    {outgoing incoming successor : graph.DirectedEdge}
    (traversalEquation : cycle.traversed =
      before ++ outgoing :: between ++ incoming :: successor :: after) :
    ∃ path : graph.EdgeSimplePath,
      path.start = outgoing.source ∧
      path.finish = incoming.target ∧
      path.traversed = (outgoing :: between) ++ [incoming] ∧
      (∀ vertex, vertex ∈ path.vertices → vertex ∈ cycle.vertices) ∧
      ∀ index, index ∈ path.traversed.map DirectedEdge.index →
        index ∈ cycle.traversed.map DirectedEdge.index := by
  have rotationEquation : cycle.traversed = before ++
      outgoing :: (between ++ incoming :: successor :: after) := by
    simpa [List.append_assoc] using traversalEquation
  rcases cycle.rotateAt_exists rotationEquation with
    ⟨rotated, rotatedStarts, rotatedSteps⟩
  have rotatedDecomposition : rotated.traversed =
      (outgoing :: between) ++ incoming :: successor :: (after ++ before) := by
    rw [rotatedSteps]
    simp [List.append_assoc]
  rcases rotated.prefixPath rotatedDecomposition with
    ⟨path, pathStarts, pathFinishes, pathSteps⟩
  have traversalPermutation : rotated.traversed.Perm cycle.traversed := by
    rw [rotatedSteps, traversalEquation]
    simpa [List.append_assoc] using
      ((List.perm_append_comm :
        (before ++ (outgoing ::
          (between ++ incoming :: successor :: after))).Perm
        ((outgoing :: (between ++ incoming :: successor :: after)) ++
          before)).symm)
  refine ⟨path, pathStarts.trans rotatedStarts, pathFinishes, pathSteps,
    ?_, ?_⟩
  · intro vertex membership
    have inRotated : vertex ∈ rotated.vertices := by
      rw [path.vertices_eq_sources_append_finish (by simp [pathSteps])]
        at membership
      rcases List.mem_append.mp membership with inSources | atFinish
      · rcases List.mem_map.mp inSources with
          ⟨directed, directedMembership, sourceEquation⟩
        have directedInRotated : directed ∈ rotated.traversed := by
          rw [rotatedDecomposition]
          simp [pathSteps] at directedMembership ⊢
          rcases directedMembership with rfl | inBetween | rfl
          · simp
          · simp [inBetween]
          · simp
        rw [← sourceEquation]
        exact (rotated.directed_endpoints_mem_vertices
          directedInRotated).1
      · simp at atFinish
        subst vertex
        rw [pathFinishes]
        exact (rotated.directed_endpoints_mem_vertices
          (directed := incoming) (by
          rw [rotatedDecomposition]
          simp)).2
    rw [← rotated.sources_eq_vertices] at inRotated
    rcases List.mem_map.mp inRotated with
      ⟨directed, directedMembership, sourceEquation⟩
    have inOriginal := traversalPermutation.mem_iff.mp directedMembership
    rw [← sourceEquation]
    exact (cycle.directed_endpoints_mem_vertices inOriginal).1
  · intro index membership
    rcases List.mem_map.mp membership with
      ⟨directed, directedMembership, indexEquation⟩
    have inRotated : directed ∈ rotated.traversed := by
      rw [rotatedDecomposition]
      rw [pathSteps] at directedMembership
      simp at directedMembership ⊢
      rcases directedMembership with rfl | inBetween | rfl
      · simp
      · simp [inBetween]
      · simp
    have inOriginal := traversalPermutation.mem_iff.mp inRotated
    exact List.mem_map.mpr ⟨directed, inOriginal, indexEquation⟩

/-- For a selected cusp followed later by a hit vertex, extract the
wrap-around return path from that hit through the old base and prefix back to
the cusp. -/
theorem wrapPathAfterCusp {graph : Graph} (cycle : graph.EdgeSimpleCycle)
    {initial between suffix : List graph.DirectedEdge}
    {incoming partner outgoingAtHit : graph.DirectedEdge}
    (traversalEquation : cycle.traversed =
      initial ++ incoming :: partner :: between ++ outgoingAtHit :: suffix) :
    ∃ path : graph.EdgeSimplePath,
      path.start = outgoingAtHit.source ∧
      path.finish = incoming.target ∧
      path.traversed =
        ((outgoingAtHit :: suffix) ++ initial) ++ [incoming] ∧
      (∀ vertex, vertex ∈ path.vertices → vertex ∈ cycle.vertices) ∧
      ∀ index, index ∈ path.traversed.map DirectedEdge.index →
        index ∈ cycle.traversed.map DirectedEdge.index := by
  let beforeRotation := initial ++ incoming :: partner :: between
  have rotationEquation : cycle.traversed =
      beforeRotation ++ outgoingAtHit :: suffix := by
    simpa [beforeRotation, List.append_assoc] using traversalEquation
  rcases cycle.rotateAt_exists rotationEquation with
    ⟨rotated, rotatedStarts, rotatedSteps⟩
  have rotatedDecomposition : rotated.traversed =
      (((outgoingAtHit :: suffix) ++ initial) ++
        incoming :: partner :: between) := by
    rw [rotatedSteps]
    simp [beforeRotation, List.append_assoc]
  rcases rotated.prefixPath rotatedDecomposition with
    ⟨path, pathStarts, pathFinishes, pathSteps⟩
  have traversalPermutation : rotated.traversed.Perm cycle.traversed := by
    rw [rotatedSteps, traversalEquation]
    simpa [beforeRotation, List.append_assoc] using
      ((List.perm_append_comm :
        (beforeRotation ++ (outgoingAtHit :: suffix)).Perm
          ((outgoingAtHit :: suffix) ++ beforeRotation)).symm)
  have pathEdgeSubset : ∀ directed, directed ∈ path.traversed →
      directed ∈ cycle.traversed := by
    intro directed membership
    have inRotated : directed ∈ rotated.traversed := by
      rw [rotatedDecomposition]
      rw [pathSteps] at membership
      rcases List.mem_append.mp membership with inInitial | atIncoming
      · exact List.mem_append.mpr (.inl inInitial)
      · simp at atIncoming
        subst directed
        simp
    exact traversalPermutation.mem_iff.mp inRotated
  have outgoingMembership : outgoingAtHit ∈ cycle.traversed := by
    rw [traversalEquation]
    simp
  have startInCycle : outgoingAtHit.source ∈ cycle.vertices :=
    (cycle.directed_endpoints_mem_vertices outgoingMembership).1
  refine ⟨path, pathStarts.trans rotatedStarts, pathFinishes, pathSteps,
    cycle.path_vertices_subset path (by
      rw [pathStarts, rotatedStarts]
      exact startInCycle) pathEdgeSubset, ?_⟩
  intro index membership
  rcases List.mem_map.mp membership with
    ⟨directed, directedMembership, indexEquation⟩
  exact List.mem_map.mpr
    ⟨directed, pathEdgeSubset directed directedMembership, indexEquation⟩

/-- Extract the old post-cusp arc from the outgoing cusp edge up to, but not
including, the outgoing occurrence at the first hit. -/
theorem segmentBeforeAfterCuspHit {graph : Graph}
    (cycle : graph.EdgeSimpleCycle)
    {initial between suffix : List graph.DirectedEdge}
    {incoming partner outgoingAtHit : graph.DirectedEdge}
    (traversalEquation : cycle.traversed =
      initial ++ incoming :: partner :: between ++ outgoingAtHit :: suffix) :
    ∃ path : graph.EdgeSimplePath,
      path.start = partner.source ∧
      path.finish = outgoingAtHit.source ∧
      path.traversed = partner :: between ∧
      (∀ vertex, vertex ∈ path.vertices → vertex ∈ cycle.vertices) ∧
      ∀ index, index ∈ path.traversed.map DirectedEdge.index →
        index ∈ cycle.traversed.map DirectedEdge.index := by
  let beforeRotation := initial ++ [incoming]
  have rotationEquation : cycle.traversed =
      beforeRotation ++ partner :: (between ++ outgoingAtHit :: suffix) := by
    simpa [beforeRotation, List.append_assoc] using traversalEquation
  rcases cycle.rotateAt_exists rotationEquation with
    ⟨rotated, rotatedStarts, rotatedSteps⟩
  have rotatedDecomposition : rotated.traversed =
      (partner :: between) ++ outgoingAtHit ::
        (suffix ++ beforeRotation) := by
    rw [rotatedSteps]
    simp [beforeRotation, List.append_assoc]
  rcases rotated.prefixBefore rotatedDecomposition with
    ⟨path, pathStarts, pathFinishes, pathSteps, _pathSubsetRotated⟩
  have traversalPermutation : rotated.traversed.Perm cycle.traversed := by
    rw [rotatedSteps, traversalEquation]
    simpa [beforeRotation, List.append_assoc] using
      ((List.perm_append_comm :
        (beforeRotation ++ (partner ::
          (between ++ outgoingAtHit :: suffix))).Perm
        ((partner :: (between ++ outgoingAtHit :: suffix)) ++
          beforeRotation)).symm)
  have pathEdgeSubset : ∀ directed, directed ∈ path.traversed →
      directed ∈ cycle.traversed := by
    intro directed membership
    have inRotated : directed ∈ rotated.traversed := by
      rw [rotatedDecomposition]
      rw [pathSteps] at membership
      exact List.mem_append.mpr (.inl membership)
    exact traversalPermutation.mem_iff.mp inRotated
  have partnerMembership : partner ∈ cycle.traversed := by
    rw [traversalEquation]
    simp
  have startInCycle : partner.source ∈ cycle.vertices :=
    (cycle.directed_endpoints_mem_vertices partnerMembership).1
  refine ⟨path, pathStarts.trans rotatedStarts, pathFinishes, pathSteps,
    cycle.path_vertices_subset path (by
      rw [pathStarts, rotatedStarts]
      exact startInCycle) pathEdgeSubset, ?_⟩
  intro index membership
  rcases List.mem_map.mp membership with
    ⟨directed, directedMembership, indexEquation⟩
  exact List.mem_map.mpr
    ⟨directed, pathEdgeSubset directed directedMembership, indexEquation⟩

end EdgeSimpleCycle

/-- An independent graph walk carrying its exact number of edge steps. The
index makes finite-depth completeness statements possible without eliminating
the proof-irrelevant `Walk` proposition into data. -/
inductive WalkN (graph : Graph) (start : Vertex) : Nat → Vertex → Prop where
  | refl : WalkN graph start 0 start
  | step {steps : Nat} {middle finish : Vertex} :
      WalkN graph start steps middle →
      graph.Adjacent middle finish →
      WalkN graph start (steps + 1) finish

namespace WalkN

theorem toWalk {graph : Graph} {start finish : Vertex} {steps : Nat} :
    graph.WalkN start steps finish → graph.Walk start finish := by
  intro walk
  induction walk with
  | refl => exact .refl start
  | step prior adjacency ih => exact .step ih adjacency

end WalkN

/-- A walk together with the duplicate-free list of vertices it visits. This
is the finite combinatorial object used to bound arbitrary inductive walks. -/
inductive SimpleWalk (graph : Graph) (start : Vertex) :
    Nat → List Vertex → Vertex → Prop where
  | refl : SimpleWalk graph start 0 [start] start
  | step {steps : Nat} {visited : List Vertex} {middle finish : Vertex} :
      SimpleWalk graph start steps visited middle →
      graph.Adjacent middle finish →
      finish ∉ visited →
      SimpleWalk graph start (steps + 1) (visited ++ [finish]) finish

namespace SimpleWalk

theorem toWalkN {graph : Graph} {start finish : Vertex} {steps : Nat}
    {visited : List Vertex} :
    graph.SimpleWalk start steps visited finish →
      graph.WalkN start steps finish := by
  intro walk
  induction walk with
  | refl => exact .refl
  | step prior adjacency fresh ih => exact .step ih adjacency

theorem nodup {graph : Graph} {start finish : Vertex} {steps : Nat}
    {visited : List Vertex} :
    graph.SimpleWalk start steps visited finish → visited.Nodup := by
  intro walk
  induction walk with
  | refl => simp
  | step prior adjacency fresh ih =>
      rw [List.nodup_append]
      refine ⟨ih, by simp, ?_⟩
      intro vertex membership singleton singletonMembership
      simp at singletonMembership
      subst singleton
      intro same
      subst vertex
      exact fresh membership

theorem length_eq {graph : Graph} {start finish : Vertex} {steps : Nat}
    {visited : List Vertex}
    (walk : graph.SimpleWalk start steps visited finish) :
    visited.length = steps + 1 := by
  induction walk with
  | refl => simp
  | step prior adjacency fresh ih => simp [ih, Nat.add_assoc]

theorem restrict {graph : Graph} {start finish vertex : Vertex} {steps : Nat}
    {visited : List Vertex}
    (walk : graph.SimpleWalk start steps visited finish)
    (membership : vertex ∈ visited) :
    ∃ restrictedSteps restricted,
      graph.SimpleWalk start restrictedSteps restricted vertex := by
  induction walk with
  | refl =>
      simp at membership
      subst vertex
      exact ⟨0, [start], .refl⟩
  | @step priorSteps priorVisited middle current prior adjacency fresh ih =>
      simp at membership
      rcases membership with membership | same
      · exact ih membership
      · subst vertex
        exact ⟨priorSteps + 1, priorVisited ++ [current],
          .step prior adjacency fresh⟩

/-- Lift a duplicate-free vertex walk through an edge-inclusion map to an
exact occurrence-aware simple path in the ambient multigraph.  The visited
vertex list is preserved literally. -/
theorem liftToEdgeSimplePath {subgraph graph : Graph}
    {start finish : Vertex} {steps : Nat} {visited : List Vertex}
    (simple : subgraph.SimpleWalk start steps visited finish)
    (edgeSubset : ∀ edge ∈ subgraph.edges, edge ∈ graph.edges) :
    ∃ path : graph.EdgeSimplePath,
      path.start = start ∧ path.finish = finish ∧
        path.vertices = visited := by
  induction simple with
  | refl =>
      let path : graph.EdgeSimplePath :=
        { start := start
          finish := start
          traversed := []
          walk := .refl start
          verticesNodup := by simp [EdgeWalk.visitedVertices] }
      exact ⟨path, rfl, rfl, by simp [path, EdgeSimplePath.vertices,
        EdgeWalk.visitedVertices]⟩
  | @step priorSteps priorVisited middle current prior adjacency fresh ih =>
      rcases ih with ⟨priorPath, priorStarts, priorFinishes,
        priorVertices⟩
      rcases adjacency with ⟨edge, edgeMembership, direction⟩
      have ambientMembership := edgeSubset edge edgeMembership
      rcases List.getElem?_of_mem ambientMembership with
        ⟨index, edgeLookup⟩
      rcases direction with forward | backward
      · let directed : graph.DirectedEdge :=
          { index := index
            edge := edge
            lookup := edgeLookup
            forward := true }
        have starts : directed.source = priorPath.finish := by
          rw [priorFinishes]
          simpa [directed, DirectedEdge.source] using forward.1
        have finishes : directed.target = current := by
          simpa [directed, DirectedEdge.target] using forward.2
        have extendedVertices : EdgeWalk.visitedVertices priorPath.start
            (priorPath.traversed ++ [directed]) =
              priorPath.vertices ++ [current] := by
          simp [EdgeSimplePath.vertices, EdgeWalk.visitedVertices,
            List.map_append, finishes]
        let path : graph.EdgeSimplePath :=
          { start := priorPath.start
            finish := current
            traversed := priorPath.traversed ++ [directed]
            walk := EdgeWalk.step priorPath.walk directed starts finishes
            verticesNodup := by
              rw [extendedVertices]
              rw [List.nodup_append]
              refine ⟨priorPath.verticesNodup, by simp, ?_⟩
              intro vertex membership singleton singletonMembership
              simp at singletonMembership
              subst singleton
              intro same
              subst vertex
              apply fresh
              rw [← priorVertices]
              exact membership }
        refine ⟨path, priorStarts, rfl, ?_⟩
        change EdgeWalk.visitedVertices priorPath.start
          (priorPath.traversed ++ [directed]) = priorVisited ++ [current]
        rw [extendedVertices, priorVertices]
      · let directed : graph.DirectedEdge :=
          { index := index
            edge := edge
            lookup := edgeLookup
            forward := false }
        have starts : directed.source = priorPath.finish := by
          rw [priorFinishes]
          simpa [directed, DirectedEdge.source] using backward.2
        have finishes : directed.target = current := by
          simpa [directed, DirectedEdge.target] using backward.1
        have extendedVertices : EdgeWalk.visitedVertices priorPath.start
            (priorPath.traversed ++ [directed]) =
              priorPath.vertices ++ [current] := by
          simp [EdgeSimplePath.vertices, EdgeWalk.visitedVertices,
            List.map_append, finishes]
        let path : graph.EdgeSimplePath :=
          { start := priorPath.start
            finish := current
            traversed := priorPath.traversed ++ [directed]
            walk := EdgeWalk.step priorPath.walk directed starts finishes
            verticesNodup := by
              rw [extendedVertices]
              rw [List.nodup_append]
              refine ⟨priorPath.verticesNodup, by simp, ?_⟩
              intro vertex membership singleton singletonMembership
              simp at singletonMembership
              subst singleton
              intro same
              subst vertex
              apply fresh
              rw [← priorVertices]
              exact membership }
        refine ⟨path, priorStarts, rfl, ?_⟩
        change EdgeWalk.visitedVertices priorPath.start
          (priorPath.traversed ++ [directed]) = priorVisited ++ [current]
        rw [extendedVertices, priorVertices]

end SimpleWalk

namespace Walk

/-- Every finite walk can have its loops erased. The result preserves the
endpoints while visiting no vertex twice. -/
theorem toSimple {graph : Graph} {start finish : Vertex}
    (walk : graph.Walk start finish) :
    ∃ steps visited, graph.SimpleWalk start steps visited finish := by
  induction walk with
  | refl => exact ⟨0, [start], .refl⟩
  | @step middle finish prior adjacency ih =>
      rcases ih with ⟨steps, visited, simple⟩
      by_cases repeated : finish ∈ visited
      · exact simple.restrict repeated
      · exact ⟨steps + 1, visited ++ [finish],
          .step simple adjacency repeated⟩

end Walk

private theorem length_le_of_nodup_subset [BEq alpha] [LawfulBEq alpha]
    {values ambient : List alpha} (nodup : values.Nodup)
    (subset : ∀ value ∈ values, value ∈ ambient) :
    values.length ≤ ambient.length := by
  induction values generalizing ambient with
  | nil => simp
  | cons head tail ih =>
      have headMembership : head ∈ ambient := subset head (by simp)
      have tailSubset : ∀ value ∈ tail, value ∈ ambient.erase head := by
        intro value membership
        have valueMembership : value ∈ ambient :=
          subset value (by simp [membership])
        have different : value ≠ head := by
          intro same
          subst value
          exact (List.nodup_cons.mp nodup).1 membership
        exact (List.mem_erase_of_ne different).2 valueMembership
      have tailBound := ih (List.nodup_cons.mp nodup).2 tailSubset
      rw [List.length_erase_of_mem headMembership] at tailBound
      have positive : 0 < ambient.length :=
        List.length_pos_of_mem headMembership
      simp only [List.length_cons]
      omega

theorem EdgeSimpleCycle.length_le_edges {graph : Graph}
    (cycle : graph.EdgeSimpleCycle) :
    cycle.traversed.length ≤ graph.edges.length := by
  have indexSubset : ∀ index ∈ cycle.traversed.map DirectedEdge.index,
      index ∈ List.range graph.edges.length := by
    intro index membership
    rcases List.mem_map.mp membership with ⟨directed, directedMembership, rfl⟩
    exact List.mem_range.mpr
      (List.getElem?_eq_some_iff.mp directed.lookup).1
  have bound := length_le_of_nodup_subset cycle.edgeIndicesNodup indexSubset
  simpa using bound

/-- Existence of a graph walk with no more than `fuel` edge steps. -/
def WalkWithin (graph : Graph) (start : Vertex) (fuel : Nat)
    (finish : Vertex) : Prop :=
  ∃ steps, steps ≤ fuel ∧ graph.WalkN start steps finish

def neighbors (graph : Graph) (vertex : Vertex) : List Vertex :=
  graph.edges.flatMap fun edge =>
    if edge.first == vertex then [edge.second]
    else if edge.second == vertex then [edge.first]
    else []

theorem neighbor_adjacent (graph : Graph) {left right : Vertex}
    (membership : right ∈ graph.neighbors left) :
    graph.Adjacent left right := by
  simp only [neighbors, List.mem_flatMap] at membership
  obtain ⟨edge, edgeMembership, endpointMembership⟩ := membership
  by_cases firstMatches : edge.first = left
  · simp [firstMatches] at endpointMembership
    exact ⟨edge, edgeMembership, .inl ⟨firstMatches, endpointMembership.symm⟩⟩
  · by_cases secondMatches : edge.second = left
    · simp [firstMatches, secondMatches] at endpointMembership
      exact ⟨edge, edgeMembership,
        .inr ⟨endpointMembership.symm, secondMatches⟩⟩
    · simp [firstMatches, secondMatches] at endpointMembership

theorem adjacent_neighbor (graph : Graph) {left right : Vertex}
    (adjacency : graph.Adjacent left right) :
    right ∈ graph.neighbors left := by
  rcases adjacency with ⟨edge, edgeMembership, direction⟩
  simp only [neighbors, List.mem_flatMap]
  refine ⟨edge, edgeMembership, ?_⟩
  rcases direction with forward | backward
  · rcases forward with ⟨firstMatches, secondMatches⟩
    simp [firstMatches, secondMatches]
  · rcases backward with ⟨firstMatches, secondMatches⟩
    by_cases same : right = left <;>
      simp [firstMatches, secondMatches, same]

theorem neighbor_iff_adjacent (graph : Graph) {left right : Vertex} :
    right ∈ graph.neighbors left ↔ graph.Adjacent left right :=
  ⟨graph.neighbor_adjacent, graph.adjacent_neighbor⟩

def closure (graph : Graph) (seen : List Vertex) : List Vertex :=
  (seen ++ seen.flatMap graph.neighbors)
    |>.filter (· < graph.vertexCount)
    |>.eraseDups

theorem closure_preserves_walks (graph : Graph) (start : Vertex)
    (seen : List Vertex)
    (walks : ∀ vertex ∈ seen, graph.Walk start vertex) :
    ∀ vertex ∈ graph.closure seen, graph.Walk start vertex := by
  intro vertex membership
  simp [closure, List.mem_flatMap] at membership
  rcases membership with ⟨alreadySeen, _⟩ | ⟨reachedByEdge, _⟩
  · exact walks vertex alreadySeen
  · obtain ⟨middle, middleSeen, neighborMembership⟩ := reachedByEdge
    exact .step (walks middle middleSeen)
      (graph.neighbor_adjacent neighborMembership)

theorem closure_preserves_walkWithin (graph : Graph) (start : Vertex)
    (fuel : Nat)
    (seen : List Vertex)
    (walks : ∀ vertex ∈ seen, graph.WalkWithin start fuel vertex) :
    ∀ vertex ∈ graph.closure seen,
      graph.WalkWithin start (fuel + 1) vertex := by
  intro vertex membership
  simp [closure, List.mem_flatMap] at membership
  rcases membership with ⟨alreadySeen, _⟩ | ⟨reachedByEdge, _⟩
  · rcases walks vertex alreadySeen with ⟨steps, stepBound, walk⟩
    exact ⟨steps, Nat.le_trans stepBound (Nat.le_add_right fuel 1), walk⟩
  · obtain ⟨middle, middleSeen, neighborMembership⟩ := reachedByEdge
    rcases walks middle middleSeen with ⟨steps, stepBound, walk⟩
    exact ⟨steps + 1, Nat.add_le_add_right stepBound 1,
      .step walk (graph.neighbor_adjacent neighborMembership)⟩

def closureN (graph : Graph) : Nat → List Vertex → List Vertex
  | 0, seen => seen
  | fuel + 1, seen => graph.closureN fuel (graph.closure seen)

theorem closureN_succ (graph : Graph) (fuel : Nat) (seen : List Vertex) :
    graph.closureN (fuel + 1) seen =
      graph.closure (graph.closureN fuel seen) := by
  induction fuel generalizing seen with
  | zero => rfl
  | succ remaining ih =>
      exact ih (graph.closure seen)

theorem neighbor_mem_closure (graph : Graph) {middle finish : Vertex}
    (middleSeen : middle ∈ seen)
    (adjacency : graph.Adjacent middle finish)
    (finishInBounds : finish < graph.vertexCount) :
    finish ∈ graph.closure seen := by
  simp only [closure, List.mem_eraseDups, List.mem_filter,
    List.mem_append, List.mem_flatMap]
  refine ⟨?_, by simpa using finishInBounds⟩
  exact .inr ⟨middle, middleSeen, graph.adjacent_neighbor adjacency⟩

theorem mem_closure_of_mem (graph : Graph) {seen : List Vertex}
    {vertex : Vertex} (membership : vertex ∈ seen)
    (inBounds : vertex < graph.vertexCount) :
    vertex ∈ graph.closure seen := by
  simp only [closure, List.mem_eraseDups, List.mem_filter,
    List.mem_append, List.mem_flatMap]
  exact ⟨.inl membership, by simpa using inBounds⟩

theorem mem_closureN_mono (graph : Graph) {small large : Nat}
    {seen : List Vertex} {vertex : Vertex} (fuelOrder : small ≤ large)
    (inBounds : vertex < graph.vertexCount)
    (membership : vertex ∈ graph.closureN small seen) :
    vertex ∈ graph.closureN large seen := by
  rcases Nat.exists_eq_add_of_le fuelOrder with ⟨extra, rfl⟩
  clear fuelOrder
  induction extra with
  | zero => simpa
  | succ remaining ih =>
      rw [Nat.add_succ, graph.closureN_succ]
      exact graph.mem_closure_of_mem ih inBounds

theorem closureN_preserves_walks (graph : Graph) (start : Vertex)
    (fuel : Nat) (seen : List Vertex)
    (walks : ∀ vertex ∈ seen, graph.Walk start vertex) :
    ∀ vertex ∈ graph.closureN fuel seen, graph.Walk start vertex := by
  induction fuel generalizing seen with
  | zero => exact walks
  | succ remaining ih =>
      exact ih (graph.closure seen)
        (graph.closure_preserves_walks start seen walks)

theorem closureN_preserves_walkWithin (graph : Graph) (start : Vertex)
    (base fuel : Nat)
    (seen : List Vertex)
    (walks : ∀ vertex ∈ seen, graph.WalkWithin start base vertex) :
    ∀ vertex ∈ graph.closureN fuel seen,
      graph.WalkWithin start (base + fuel) vertex := by
  induction fuel generalizing seen base with
  | zero => simpa [closureN] using walks
  | succ remaining ih =>
      have afterOne :=
        graph.closure_preserves_walkWithin start base seen walks
      have afterRest := ih (base + 1) (graph.closure seen) afterOne
      simpa [closureN, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        afterRest

theorem closureN_walkWithin (graph : Graph) (start : Vertex) (fuel : Nat) :
    ∀ vertex ∈ graph.closureN fuel [start],
      graph.WalkWithin start fuel vertex := by
  have initial : ∀ vertex ∈ [start], graph.WalkWithin start 0 vertex := by
    intro vertex membership
    simp at membership
    subst vertex
    exact ⟨0, Nat.le_refl 0, .refl⟩
  simpa using graph.closureN_preserves_walkWithin start 0 fuel [start] initial

/-- Vertices reachable from vertex zero after enough finite closure rounds. -/
def reachable (graph : Graph) : List Vertex :=
  if graph.vertexCount == 0 then [] else graph.closureN graph.vertexCount [0]

theorem reachable_sound (graph : Graph) {vertex : Vertex}
    (membership : vertex ∈ graph.reachable) : graph.Walk 0 vertex := by
  simp only [reachable] at membership
  split at membership
  next isEmpty => simp at membership
  next isNonempty =>
    exact graph.closureN_preserves_walks 0 graph.vertexCount [0]
      (by
        intro current currentMembership
        simp at currentMembership
        subst current
        exact .refl 0)
      vertex membership

theorem reachable_walkWithin (graph : Graph) (positive : 0 < graph.vertexCount)
    {vertex : Vertex} (membership : vertex ∈ graph.reachable) :
    graph.WalkWithin 0 graph.vertexCount vertex := by
  simp only [reachable] at membership
  split at membership
  next isEmpty =>
    have : graph.vertexCount = 0 := by simpa using isEmpty
    simp [this] at positive
  next isNonempty =>
    exact graph.closureN_walkWithin 0 graph.vertexCount vertex membership

def boundedEdges (graph : Graph) : Bool :=
  graph.edges.all fun edge =>
    edge.first < graph.vertexCount && edge.second < graph.vertexCount &&
      edge.first != edge.second

def connected (graph : Graph) : Bool :=
  graph.vertexCount > 0 &&
    (List.range graph.vertexCount).all graph.reachable.contains

/-- Executable tree test for a finite undirected multigraph. -/
def isTree (graph : Graph) : Bool :=
  graph.boundedEdges && graph.connected &&
    graph.edges.length + 1 == graph.vertexCount

/-- Every stored edge names two distinct vertices of the finite graph. -/
def Bounded (graph : Graph) : Prop :=
  ∀ edge ∈ graph.edges,
    edge.first < graph.vertexCount ∧
    edge.second < graph.vertexCount ∧
    edge.first ≠ edge.second

theorem adjacent_right_in_bounds (graph : Graph) (bounded : graph.Bounded)
    {left right : Vertex} (adjacency : graph.Adjacent left right) :
    right < graph.vertexCount := by
  rcases adjacency with ⟨edge, edgeMembership, direction⟩
  have edgeBounds := bounded edge edgeMembership
  rcases direction with forward | backward
  · exact forward.2 ▸ edgeBounds.2.1
  · exact backward.1 ▸ edgeBounds.1

theorem SimpleWalk.vertices_in_bounds {graph : Graph}
    {start finish : Vertex} {steps : Nat} {visited : List Vertex}
    (walk : graph.SimpleWalk start steps visited finish)
    (bounded : graph.Bounded) (startInBounds : start < graph.vertexCount) :
    ∀ vertex ∈ visited, vertex < graph.vertexCount := by
  induction walk with
  | refl => simpa using startInBounds
  | step prior adjacency fresh ih =>
      intro vertex membership
      simp at membership
      rcases membership with membership | same
      · exact ih vertex membership
      · subst vertex
        exact graph.adjacent_right_in_bounds bounded adjacency

/-- A duplicate-free walk in a bounded `vertexCount`-vertex graph uses at
most `vertexCount` edge steps. -/
theorem SimpleWalk.toWalkWithin {graph : Graph}
    {start finish : Vertex} {steps : Nat} {visited : List Vertex}
    (walk : graph.SimpleWalk start steps visited finish)
    (bounded : graph.Bounded) (startInBounds : start < graph.vertexCount) :
    graph.WalkWithin start graph.vertexCount finish := by
  have allInBounds := walk.vertices_in_bounds bounded startInBounds
  have subsetRange : ∀ vertex ∈ visited,
      vertex ∈ List.range graph.vertexCount := by
    intro vertex membership
    simpa using allInBounds vertex membership
  have vertexBound : visited.length ≤ (List.range graph.vertexCount).length :=
    length_le_of_nodup_subset walk.nodup subsetRange
  have stepBound : steps ≤ graph.vertexCount := by
    rw [List.length_range] at vertexBound
    have exactLength := walk.length_eq
    omega
  exact ⟨steps, stepBound, walk.toWalkN⟩

theorem walkN_mem_closureN (graph : Graph) (bounded : graph.Bounded)
    {start finish : Vertex} {steps : Nat}
    (walk : graph.WalkN start steps finish) :
    finish ∈ graph.closureN steps [start] := by
  induction walk with
  | refl => simp [closureN]
  | step prior adjacency ih =>
      rw [graph.closureN_succ]
      exact graph.neighbor_mem_closure ih adjacency
        (graph.adjacent_right_in_bounds bounded adjacency)

theorem mem_closureN_iff_walkWithin (graph : Graph) (bounded : graph.Bounded)
    (start finish : Vertex) (fuel : Nat)
    (finishInBounds : finish < graph.vertexCount) :
    finish ∈ graph.closureN fuel [start] ↔
      graph.WalkWithin start fuel finish := by
  constructor
  · exact graph.closureN_walkWithin start fuel finish
  · intro walkWithin
    rcases walkWithin with ⟨steps, stepBound, walk⟩
    exact graph.mem_closureN_mono stepBound finishInBounds
      (graph.walkN_mem_closureN bounded walk)

/-- Every bounded inductive walk is discovered after some finite number of
closure rounds. The remaining semantic-completeness obligation is a uniform
`vertexCount` bound on the required rounds. -/
theorem walk_mem_some_closureN (graph : Graph) (bounded : graph.Bounded)
    {start finish : Vertex} (walk : graph.Walk start finish) :
    ∃ fuel, finish ∈ graph.closureN fuel [start] := by
  induction walk with
  | refl => exact ⟨0, by simp [closureN]⟩
  | step prior adjacency ih =>
      rcases ih with ⟨fuel, membership⟩
      refine ⟨fuel + 1, ?_⟩
      rw [graph.closureN_succ]
      exact graph.neighbor_mem_closure membership adjacency
        (graph.adjacent_right_in_bounds bounded adjacency)

/-- Every in-bounds vertex occurs in the finite closure from vertex zero. -/
def ReachablyConnected (graph : Graph) : Prop :=
  0 < graph.vertexCount ∧
    ∀ vertex, vertex < graph.vertexCount → vertex ∈ graph.reachable

/-- Connectedness stated independently using graph walks. -/
def Connected (graph : Graph) : Prop :=
  0 < graph.vertexCount ∧
    ∀ vertex, vertex < graph.vertexCount → graph.Walk 0 vertex

/-- Connectedness with an explicit finite path budget. This is independent of
the closure implementation while still matching its `vertexCount` fuel. -/
def FuelConnected (graph : Graph) : Prop :=
  0 < graph.vertexCount ∧
    ∀ vertex, vertex < graph.vertexCount →
      graph.WalkWithin 0 graph.vertexCount vertex

/-- Loop erasure supplies the uniform finite path budget needed by the
executable reachability closure. -/
theorem Connected.toFuelConnected {graph : Graph}
    (connected : graph.Connected) (bounded : graph.Bounded) :
    graph.FuelConnected :=
  ⟨connected.1, by
    intro vertex inBounds
    rcases (connected.2 vertex inBounds).toSimple with
      ⟨steps, visited, simple⟩
    exact simple.toWalkWithin bounded connected.1⟩

/-- The exact finite-closure contract decided by `isTree`. -/
def ComputationalTree (graph : Graph) : Prop :=
  graph.Bounded ∧ graph.ReachablyConnected ∧
    graph.edges.length + 1 = graph.vertexCount

/-- Declarative tree property used by the semantic checker soundness theorem. -/
def IsTree (graph : Graph) : Prop :=
  graph.Bounded ∧ graph.Connected ∧
    graph.edges.length + 1 = graph.vertexCount

/-- Occurrence-aware acyclicity for finite undirected multigraphs. Parallel
stored edges remain distinct, so two parallel occurrences can form a
length-two `EdgeSimpleCycle`. -/
def Acyclic (graph : Graph) : Prop :=
  ∀ _cycle : graph.EdgeSimpleCycle, False

/-- The public acyclicity predicate is exactly the nonexistence of an
occurrence-aware simple cycle. -/
theorem acyclic_iff_not_nonempty_edgeSimpleCycle (graph : Graph) :
    graph.Acyclic ↔ ¬Nonempty graph.EdgeSimpleCycle := by
  constructor
  · intro acyclic cycle
    rcases cycle with ⟨cycle⟩
    exact acyclic cycle
  · intro noCycle cycle
    exact noCycle ⟨cycle⟩

/-- Independent fuel-indexed tree semantics with an executable completeness
theorem. -/
def FuelTree (graph : Graph) : Prop :=
  graph.Bounded ∧ graph.FuelConnected ∧
    graph.edges.length + 1 = graph.vertexCount

theorem boundedEdges_iff (graph : Graph) :
    graph.boundedEdges = true ↔ graph.Bounded := by
  simp [boundedEdges, Bounded, and_assoc]

theorem connected_iff (graph : Graph) :
    graph.connected = true ↔ graph.ReachablyConnected := by
  simp [connected, ReachablyConnected]

theorem connected_iff_fuelConnected (graph : Graph) (bounded : graph.Bounded) :
    graph.connected = true ↔ graph.FuelConnected := by
  constructor
  · intro accepted
    have reachableContract := (graph.connected_iff).mp accepted
    exact ⟨reachableContract.1, by
      intro vertex inBounds
      exact graph.reachable_walkWithin reachableContract.1
        (reachableContract.2 vertex inBounds)⟩
  · intro semantic
    apply graph.connected_iff.mpr
    exact ⟨semantic.1, by
      intro vertex inBounds
      rcases semantic.2 vertex inBounds with
        ⟨steps, stepBound, walk⟩
      have atExactDepth := graph.walkN_mem_closureN bounded walk
      have atVertexDepth := graph.mem_closureN_mono stepBound inBounds atExactDepth
      simpa [reachable, Nat.ne_of_gt semantic.1] using atVertexDepth⟩

/-- Executable connectedness is sound and complete for the standard
unbounded inductive-walk semantics on bounded finite graphs. -/
theorem connected_iff_connected (graph : Graph) (bounded : graph.Bounded) :
    graph.connected = true ↔ graph.Connected := by
  constructor
  · intro accepted
    have reachableContract := graph.connected_iff.mp accepted
    exact ⟨reachableContract.1, by
      intro vertex inBounds
      exact graph.reachable_sound (reachableContract.2 vertex inBounds)⟩
  · intro connected
    exact (graph.connected_iff_fuelConnected bounded).mpr
      (connected.toFuelConnected bounded)

theorem connected_sound (graph : Graph) (accepted : graph.connected = true) :
    graph.Connected := by
  have reachableContract := (graph.connected_iff).mp accepted
  exact ⟨reachableContract.1, by
    intro vertex inBounds
    exact graph.reachable_sound (reachableContract.2 vertex inBounds)⟩

theorem FuelConnected.toConnected {graph : Graph}
    (fuelConnected : graph.FuelConnected) : graph.Connected :=
  ⟨fuelConnected.1, by
    intro vertex inBounds
    rcases fuelConnected.2 vertex inBounds with ⟨steps, _, walk⟩
    exact walk.toWalk⟩

theorem FuelTree.toIsTree {graph : Graph} (fuelTree : graph.FuelTree) :
    graph.IsTree :=
  ⟨fuelTree.1, fuelTree.2.1.toConnected, fuelTree.2.2⟩

theorem isTree_iff_computational (graph : Graph) :
    graph.isTree = true ↔ graph.ComputationalTree := by
  simp [isTree, ComputationalTree, boundedEdges_iff, connected_iff, and_assoc]

theorem isTree_iff_fuelTree (graph : Graph) :
    graph.isTree = true ↔ graph.FuelTree := by
  constructor
  · intro accepted
    have computational := graph.isTree_iff_computational.mp accepted
    have connectedAccepted := graph.connected_iff.mpr computational.2.1
    exact ⟨computational.1,
      (graph.connected_iff_fuelConnected computational.1).mp connectedAccepted,
      computational.2.2⟩
  · intro semantic
    have connectedAccepted :=
      (graph.connected_iff_fuelConnected semantic.1).mpr semantic.2.1
    apply graph.isTree_iff_computational.mpr
    exact ⟨semantic.1, graph.connected_iff.mp connectedAccepted, semantic.2.2⟩

/-- The finite executable tree checker decides the public declarative tree
property, not only an auxiliary fuel-indexed approximation. -/
theorem isTree_iff_isTree (graph : Graph) :
    graph.isTree = true ↔ graph.IsTree := by
  constructor
  · intro accepted
    exact (graph.isTree_iff_fuelTree.mp accepted).toIsTree
  · intro tree
    exact graph.isTree_iff_fuelTree.mpr
      ⟨tree.1, tree.2.1.toFuelConnected tree.1, tree.2.2⟩

theorem isTree_sound (graph : Graph) (accepted : graph.isTree = true) :
    graph.IsTree := by
  have computational := (graph.isTree_iff_computational).mp accepted
  exact ⟨computational.1,
    ⟨computational.2.1.1, by
      intro vertex inBounds
      exact graph.reachable_sound (computational.2.1.2 vertex inBounds)⟩,
    computational.2.2⟩

end Graph
end ProofNetIR
