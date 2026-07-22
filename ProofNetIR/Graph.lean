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

theorem head_source {graph : Graph} {start finish : Vertex}
    {first : graph.DirectedEdge} {rest : List graph.DirectedEdge}
    (chain : graph.EdgeChain start (first :: rest) finish) :
    first.source = start := by
  cases chain
  assumption

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

private theorem eq_of_map_eq_of_mem_of_nodup {α β : Type}
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
