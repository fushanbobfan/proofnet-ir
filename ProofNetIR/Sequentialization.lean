import Lean.Elab.Tactic.Omega
import ProofNetIR.DerivationTree
import ProofNetIR.NetEquivalence

namespace ProofNetIR

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

end Edge

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

theorem Walk.expandDelete {graph : Graph} {removed start finish : Vertex}
    (walk : (graph.deleteVertex removed).Walk start finish) :
    graph.Walk (Certificate.expandVertex removed start)
      (Certificate.expandVertex removed finish) := by
  induction walk with
  | refl => exact .refl _
  | step prior adjacency ih =>
      exact .step ih
        ((graph.adjacent_deleteVertex_iff removed _ _).mp adjacency)

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
  let context ← (certificate.conclusions.erase conclusion).mapM
    (deleteVertex? conclusion)
  pure {
    formulas := certificate.formulas.eraseIdxIfInBounds conclusion
    links := certificate.links.filterMap (Link.deleteVertex? conclusion)
    conclusions := context ++ [left', right'] }

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
