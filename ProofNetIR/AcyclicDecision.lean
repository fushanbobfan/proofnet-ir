import ProofNetIR.Sequentialization

namespace ProofNetIR

private def sequencesOfLength (values : List α) : Nat → List (List α)
  | 0 => [[]]
  | length + 1 =>
      values.flatMap fun value =>
        (sequencesOfLength values length).map (value :: ·)

private theorem mem_sequencesOfLength_length {values : List α}
    {length : Nat} {candidate : List α}
    (membership : candidate ∈ sequencesOfLength values length) :
    candidate.length = length := by
  induction length generalizing candidate with
  | zero =>
      simpa [sequencesOfLength] using congrArg List.length
        (show candidate = [] by simpa [sequencesOfLength] using membership)
  | succ length ih =>
      simp only [sequencesOfLength, List.mem_flatMap] at membership
      rcases membership with ⟨head, headMembership, mappedMembership⟩
      rcases List.mem_map.mp mappedMembership with
        ⟨tail, tailMembership, candidateEquation⟩
      subst candidate
      simp [ih tailMembership]

private theorem mem_sequencesOfLength_elements {values : List α}
    {length : Nat} {candidate : List α}
    (membership : candidate ∈ sequencesOfLength values length) :
    ∀ value ∈ candidate, value ∈ values := by
  induction length generalizing candidate with
  | zero =>
      have empty : candidate = [] := by
        simpa [sequencesOfLength] using membership
      subst candidate
      simp
  | succ length ih =>
      simp only [sequencesOfLength, List.mem_flatMap] at membership
      rcases membership with ⟨head, headMembership, mappedMembership⟩
      rcases List.mem_map.mp mappedMembership with
        ⟨tail, tailMembership, candidateEquation⟩
      subst candidate
      intro value valueMembership
      simp only [List.mem_cons] at valueMembership
      rcases valueMembership with rfl | inTail
      · exact headMembership
      · exact ih tailMembership value inTail

private theorem mem_sequencesOfLength_of_length_of_elements
    {values candidate : List α} {length : Nat}
    (candidateLength : candidate.length = length)
    (elements : ∀ value ∈ candidate, value ∈ values) :
    candidate ∈ sequencesOfLength values length := by
  induction length generalizing candidate with
  | zero =>
      have empty : candidate = [] := List.eq_nil_of_length_eq_zero
        candidateLength
      subst candidate
      simp [sequencesOfLength]
  | succ length ih =>
      cases candidate with
      | nil => simp at candidateLength
      | cons head tail =>
          have tailLength : tail.length = length := by
            simpa using Nat.succ.inj candidateLength
          have headMembership : head ∈ values :=
            elements head (by simp)
          have tailElements : ∀ value ∈ tail, value ∈ values := by
            intro value membership
            exact elements value (by simp [membership])
          simp only [sequencesOfLength, List.mem_flatMap]
          exact ⟨head, headMembership,
            List.mem_map.mpr ⟨tail,
              ih tailLength tailElements, rfl⟩⟩

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

namespace Graph

/-- Executable validation of one proposed exact cycle traversal. A candidate
must be nonempty, close endpoint-to-source in order, use no stored edge index
twice, and visit no source vertex twice. -/
def isEdgeSimpleCycleTraversal {graph : Graph} :
    List graph.DirectedEdge → Bool
  | [] => false
  | first :: rest =>
      ((first :: rest).map DirectedEdge.target ==
        rest.map DirectedEdge.source ++ [first.source]) &&
      (((first :: rest).map DirectedEdge.index).eraseDups.length ==
        (first :: rest).length) &&
      (((first :: rest).map DirectedEdge.source).eraseDups.length ==
        (first :: rest).length)

private theorem edgeChain_of_targets_eq_sources_append
    {graph : Graph} {first : graph.DirectedEdge}
    {rest : List graph.DirectedEdge} {finish : Vertex}
    (equation :
      (first :: rest).map DirectedEdge.target =
        rest.map DirectedEdge.source ++ [finish]) :
    graph.EdgeChain first.source (first :: rest) finish := by
  induction rest generalizing first with
  | nil =>
      have closes : first.target = finish := by
        simpa using equation
      exact .cons first rfl (by
        rw [closes]
        exact .nil finish)
  | cons second remaining ih =>
      have parts :
          first.target = second.source ∧
          (second :: remaining).map DirectedEdge.target =
            remaining.map DirectedEdge.source ++ [finish] := by
        simpa using equation
      exact .cons first rfl (by
        rw [parts.1]
        exact ih parts.2)

/-- Every traversal accepted by the executable validator reconstructs an exact
occurrence-aware simple cycle with the same directed-edge sequence. -/
theorem isEdgeSimpleCycleTraversal_sound {graph : Graph}
    {traversed : List graph.DirectedEdge}
    (accepted : graph.isEdgeSimpleCycleTraversal traversed = true) :
    ∃ cycle : graph.EdgeSimpleCycle,
      cycle.traversed = traversed := by
  cases traversed with
  | nil => simp [isEdgeSimpleCycleTraversal] at accepted
  | cons first rest =>
      have acceptedParts :
          ((first :: rest).map DirectedEdge.target =
              rest.map DirectedEdge.source ++ [first.source] ∧
            ((first :: rest).map DirectedEdge.index).eraseDups.length =
              (first :: rest).length) ∧
          ((first :: rest).map DirectedEdge.source).eraseDups.length =
            (first :: rest).length := by
        simpa only [isEdgeSimpleCycleTraversal, Bool.and_eq_true,
          beq_iff_eq] using accepted
      rcases acceptedParts with
        ⟨⟨closed, indexLength⟩, sourceLength⟩
      have indexNodup :
          ((first :: rest).map DirectedEdge.index).Nodup :=
        nodup_of_eraseDups_length_eq (by simpa using indexLength)
      have sourceNodup :
          ((first :: rest).map DirectedEdge.source).Nodup :=
        nodup_of_eraseDups_length_eq (by simpa using sourceLength)
      have chain :
          graph.EdgeChain first.source (first :: rest) first.source :=
        edgeChain_of_targets_eq_sources_append closed
      let cycle : graph.EdgeSimpleCycle :=
        { start := first.source
          traversed := first :: rest
          nonempty := by simp
          walk := chain.toWalk
          edgeIndicesNodup := indexNodup
          interiorNodup := by
            have sources := chain.sources_eq_start_targets_dropLast
              (by simp)
            rw [sources] at sourceNodup
            simpa [List.map_dropLast] using sourceNodup }
      exact ⟨cycle, rfl⟩

/-- Every exact occurrence-aware simple cycle is accepted when its stored
directed-edge traversal is presented to the executable validator. -/
theorem isEdgeSimpleCycleTraversal_complete {graph : Graph}
    (cycle : graph.EdgeSimpleCycle) :
    graph.isEdgeSimpleCycleTraversal cycle.traversed = true := by
  cases traversalEquation : cycle.traversed with
  | nil => exact False.elim (cycle.nonempty traversalEquation)
  | cons first rest =>
      have chain := cycle.walk.toChain
      rw [traversalEquation] at chain
      have sources := chain.sources_eq_start_targets_dropLast (by simp)
      simp only [List.map_cons, List.cons.injEq] at sources
      have targets := cycle.targets_eq
      rw [traversalEquation] at targets
      have closed :
          (first :: rest).map DirectedEdge.target =
            rest.map DirectedEdge.source ++ [first.source] := by
        calc
          (first :: rest).map DirectedEdge.target =
              ((first :: rest).map DirectedEdge.target).dropLast ++
                [cycle.start] := by
            simpa [List.map_dropLast] using targets
          _ = rest.map DirectedEdge.source ++ [first.source] := by
            simp only [List.map_cons]
            rw [← sources.2, ← sources.1]
      have indexLength :
          (((first :: rest).map DirectedEdge.index).eraseDups.length =
            (first :: rest).length) := by
        have indexNodup := cycle.edgeIndicesNodup
        rw [traversalEquation] at indexNodup
        simpa using congrArg List.length
          (eraseDups_eq_self_of_nodup indexNodup)
      have sourceLength :
          (((first :: rest).map DirectedEdge.source).eraseDups.length =
            (first :: rest).length) := by
        have sourceNodup := cycle.sources_nodup
        rw [traversalEquation] at sourceNodup
        simpa using congrArg List.length
          (eraseDups_eq_self_of_nodup sourceNodup)
      simp only [isEdgeSimpleCycleTraversal]
      rw [show
        ((first :: rest).map DirectedEdge.target ==
          rest.map DirectedEdge.source ++ [first.source]) = true
        from beq_iff_eq.mpr closed]
      rw [show
        (((first :: rest).map DirectedEdge.index).eraseDups.length ==
          (first :: rest).length) = true
        from beq_iff_eq.mpr indexLength]
      rw [show
        (((first :: rest).map DirectedEdge.source).eraseDups.length ==
          (first :: rest).length) = true
        from beq_iff_eq.mpr sourceLength]
      rfl

/-- All exact directed-edge lists of lengths one through the number of stored
edge occurrences. This is a finite reference oracle, not a scalable cycle
enumerator. -/
def edgeSimpleCycleTraversalCandidates (graph : Graph) :
    List (List graph.DirectedEdge) :=
  (List.range graph.edges.length).flatMap fun offset =>
    sequencesOfLength graph.directedEdges (offset + 1)

/-- Every exact simple-cycle traversal occurs in the finite exhaustive
candidate family. -/
theorem EdgeSimpleCycle.traversed_mem_candidates {graph : Graph}
    (cycle : graph.EdgeSimpleCycle) :
    cycle.traversed ∈ graph.edgeSimpleCycleTraversalCandidates := by
  have positive : 0 < cycle.traversed.length :=
    List.length_pos_iff.mpr cycle.nonempty
  have bounded := cycle.length_le_edges
  have offsetBound : cycle.traversed.length - 1 < graph.edges.length := by
    omega
  simp only [edgeSimpleCycleTraversalCandidates, List.mem_flatMap]
  refine ⟨cycle.traversed.length - 1,
    List.mem_range.mpr offsetBound, ?_⟩
  apply mem_sequencesOfLength_of_length_of_elements
  · exact (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt positive))).symm
  · intro directed membership
    exact directed.mem_directedEdges

/-- Exhaustive occurrence-aware cycle detection. Its candidate family is
finite and complete, but exponential; it is intended as a certified
specification oracle for the later optimized forest checker. -/
def hasEdgeSimpleCycle (graph : Graph) : Bool :=
  graph.edgeSimpleCycleTraversalCandidates.any
    graph.isEdgeSimpleCycleTraversal

/-- Exhaustive cycle search returns true exactly when an
occurrence-aware simple cycle exists. -/
theorem hasEdgeSimpleCycle_eq_true_iff (graph : Graph) :
    graph.hasEdgeSimpleCycle = true ↔
      Nonempty graph.EdgeSimpleCycle := by
  constructor
  · intro accepted
    rcases List.any_eq_true.mp accepted with
      ⟨traversed, candidateMembership, traversalAccepted⟩
    rcases isEdgeSimpleCycleTraversal_sound traversalAccepted with
      ⟨cycle, cycleTraversal⟩
    exact ⟨cycle⟩
  · rintro ⟨cycle⟩
    apply List.any_eq_true.mpr
    exact ⟨cycle.traversed, cycle.traversed_mem_candidates,
      isEdgeSimpleCycleTraversal_complete cycle⟩

/-- Certified exhaustive decision procedure for occurrence-aware acyclicity.
This reference implementation deliberately favors a direct completeness proof
over scalability. -/
def isAcyclic (graph : Graph) : Bool :=
  !graph.hasEdgeSimpleCycle

/-- The exhaustive Boolean acyclicity oracle exactly decides the public
occurrence-aware `Acyclic` proposition. -/
theorem isAcyclic_eq_true_iff (graph : Graph) :
    graph.isAcyclic = true ↔ graph.Acyclic := by
  constructor
  · intro accepted cycle
    have noCycle : graph.hasEdgeSimpleCycle = false := by
      simpa [isAcyclic] using accepted
    have hasCycle : graph.hasEdgeSimpleCycle = true :=
      graph.hasEdgeSimpleCycle_eq_true_iff.mpr ⟨cycle⟩
    rw [hasCycle] at noCycle
    contradiction
  · intro acyclic
    have noCycle : graph.hasEdgeSimpleCycle ≠ true := by
      intro hasCycle
      rcases graph.hasEdgeSimpleCycle_eq_true_iff.mp hasCycle with
        ⟨cycle⟩
      exact acyclic cycle
    have absent : graph.hasEdgeSimpleCycle = false :=
      Bool.eq_false_iff.mpr noCycle
    simp [isAcyclic, absent]

/-- Reference tree decision through the independently specified acyclicity
oracle. It is deliberately not the production path: `isAcyclic` is
exponential. -/
def isTreeViaAcyclic (graph : Graph) : Bool :=
  graph.boundedEdges && graph.connected && graph.isAcyclic

/-- The reference acyclicity-based tree decision exactly decides the public
finite-multigraph tree semantics. -/
theorem isTreeViaAcyclic_eq_true_iff (graph : Graph) :
    graph.isTreeViaAcyclic = true ↔ graph.IsTree := by
  constructor
  · intro accepted
    have acceptedParts :
        (graph.boundedEdges = true ∧ graph.connected = true) ∧
          graph.isAcyclic = true := by
      simpa only [isTreeViaAcyclic, Bool.and_eq_true] using accepted
    rcases acceptedParts with
      ⟨⟨boundedAccepted, connectedAccepted⟩, acyclicAccepted⟩
    have bounded : graph.Bounded :=
      graph.boundedEdges_iff.mp boundedAccepted
    have connected : graph.Connected :=
      (graph.connected_iff_connected bounded).mp connectedAccepted
    have acyclic : graph.Acyclic :=
      graph.isAcyclic_eq_true_iff.mp acyclicAccepted
    exact graph.isTree_iff_bounded_connected_acyclic.mpr
      ⟨bounded, connected, acyclic⟩
  · intro tree
    have semantic :=
      graph.isTree_iff_bounded_connected_acyclic.mp tree
    have boundedAccepted : graph.boundedEdges = true :=
      graph.boundedEdges_iff.mpr semantic.1
    have connectedAccepted : graph.connected = true :=
      (graph.connected_iff_connected semantic.1).mpr semantic.2.1
    have acyclicAccepted : graph.isAcyclic = true :=
      graph.isAcyclic_eq_true_iff.mpr semantic.2.2
    simpa only [isTreeViaAcyclic, Bool.and_eq_true] using
      (show
        (graph.boundedEdges = true ∧ graph.connected = true) ∧
          graph.isAcyclic = true
        from ⟨⟨boundedAccepted, connectedAccepted⟩, acyclicAccepted⟩)

/-- The exponential acyclicity route and the existing reachability-plus-count
tree checker return the same Boolean on every finite multigraph. -/
theorem isTreeViaAcyclic_eq_isTree (graph : Graph) :
    graph.isTreeViaAcyclic = graph.isTree := by
  apply Bool.eq_iff_iff.mpr
  rw [graph.isTreeViaAcyclic_eq_true_iff, graph.isTree_iff_isTree]

end Graph

namespace Certificate

/-- Executable local test for a cusp-free directed-edge traversal. This is the
Boolean counterpart of `CuspFreeTraversal`; exact edge occurrences and their
orientations are retained in the input type. -/
def isCuspFreeTraversal (certificate : Certificate) :
    List certificate.fullGraph.DirectedEdge → Bool
  | [] => true
  | [_] => true
  | incoming :: outgoing :: rest =>
      !decide (certificate.Cusp incoming outgoing) &&
        certificate.isCuspFreeTraversal (outgoing :: rest)

/-- The executable local traversal test decides the proposition-level
colored-transition contract exactly. -/
theorem isCuspFreeTraversal_eq_true_iff (certificate : Certificate)
    (traversed : List certificate.fullGraph.DirectedEdge) :
    certificate.isCuspFreeTraversal traversed = true ↔
      certificate.CuspFreeTraversal traversed := by
  induction traversed with
  | nil => simp [isCuspFreeTraversal, CuspFreeTraversal]
  | cons incoming rest ih =>
      cases rest with
      | nil => simp [isCuspFreeTraversal, CuspFreeTraversal]
      | cons outgoing tail =>
          simp [isCuspFreeTraversal, CuspFreeTraversal, ih]

/-- Executable cyclic cusp-freedom. Besides checking every internal
transition, it checks the transition from the last edge back to the first. -/
def isCuspFreeCycleTraversal (certificate : Certificate) :
    List certificate.fullGraph.DirectedEdge → Bool
  | [] => false
  | first :: rest =>
      certificate.isCuspFreeTraversal (first :: rest) &&
        !decide (certificate.Cusp
          ((first :: rest).getLast (by simp)) first)

/-- On a proved exact simple cycle, the executable cyclic test is equivalent
to the proposition used by the generalized-Yeo development. -/
theorem isCuspFreeCycleTraversal_eq_true_iff
    (certificate : Certificate)
    (cycle : certificate.fullGraph.EdgeSimpleCycle) :
    certificate.isCuspFreeCycleTraversal cycle.traversed = true ↔
      certificate.CuspFreeCycle cycle := by
  cases traversalEquation : cycle.traversed with
  | nil => exact False.elim (cycle.nonempty traversalEquation)
  | cons first rest =>
      simp [isCuspFreeCycleTraversal, CuspFreeCycle, traversalEquation,
        certificate.isCuspFreeTraversal_eq_true_iff]

/-- Exhaustive search for an exact simple cycle whose cyclic transitions are
all cusp-free. This is a finite specification oracle, not the intended
optimized correctness algorithm. -/
def hasCuspFreeEdgeSimpleCycle (certificate : Certificate) : Bool :=
  certificate.fullGraph.edgeSimpleCycleTraversalCandidates.any fun traversed =>
    certificate.fullGraph.isEdgeSimpleCycleTraversal traversed &&
      certificate.isCuspFreeCycleTraversal traversed

/-- Exhaustive colored-cycle search returns true exactly when the
proposition-level witness used by `CuspAcyclic` exists. -/
theorem hasCuspFreeEdgeSimpleCycle_eq_true_iff
    (certificate : Certificate) :
    certificate.hasCuspFreeEdgeSimpleCycle = true ↔
      ∃ cycle : certificate.fullGraph.EdgeSimpleCycle,
        certificate.CuspFreeCycle cycle := by
  constructor
  · intro accepted
    rcases List.any_eq_true.mp accepted with
      ⟨traversed, _candidateMembership, candidateAccepted⟩
    have acceptedParts :
        certificate.fullGraph.isEdgeSimpleCycleTraversal traversed = true ∧
          certificate.isCuspFreeCycleTraversal traversed = true := by
      simpa only [Bool.and_eq_true] using candidateAccepted
    rcases Graph.isEdgeSimpleCycleTraversal_sound acceptedParts.1 with
      ⟨cycle, cycleTraversal⟩
    have cycleAccepted :
        certificate.isCuspFreeCycleTraversal cycle.traversed = true := by
      rw [cycleTraversal]
      exact acceptedParts.2
    exact ⟨cycle,
      (certificate.isCuspFreeCycleTraversal_eq_true_iff cycle).mp
        cycleAccepted⟩
  · rintro ⟨cycle, free⟩
    apply List.any_eq_true.mpr
    refine ⟨cycle.traversed, cycle.traversed_mem_candidates, ?_⟩
    simp only [Bool.and_eq_true]
    exact ⟨Graph.isEdgeSimpleCycleTraversal_complete cycle,
      (certificate.isCuspFreeCycleTraversal_eq_true_iff cycle).mpr free⟩

/-- Certified finite decision procedure for the colored acyclicity proposition
used by the splitting theorem. Candidate enumeration is exponential and this
definition is deliberately a differential oracle. -/
def isCuspAcyclic (certificate : Certificate) : Bool :=
  !certificate.hasCuspFreeEdgeSimpleCycle

/-- The exhaustive Boolean colored-cycle oracle exactly decides
`CuspAcyclic`. -/
theorem isCuspAcyclic_eq_true_iff (certificate : Certificate) :
    certificate.isCuspAcyclic = true ↔ certificate.CuspAcyclic := by
  constructor
  · intro accepted cycle free
    have absent : certificate.hasCuspFreeEdgeSimpleCycle = false := by
      simpa [isCuspAcyclic] using accepted
    have present : certificate.hasCuspFreeEdgeSimpleCycle = true :=
      certificate.hasCuspFreeEdgeSimpleCycle_eq_true_iff.mpr
        ⟨cycle, free⟩
    rw [present] at absent
    contradiction
  · intro acyclic
    have noWitness :
        certificate.hasCuspFreeEdgeSimpleCycle ≠ true := by
      intro present
      rcases certificate.hasCuspFreeEdgeSimpleCycle_eq_true_iff.mp present with
        ⟨cycle, free⟩
      exact acyclic cycle free
    have absent : certificate.hasCuspFreeEdgeSimpleCycle = false :=
      Bool.eq_false_iff.mpr noWitness
    simp [isCuspAcyclic, absent]

/-- Every declaratively correct certificate is accepted by the independently
executable colored-cycle oracle. -/
theorem DeclarativelyCorrect.isCuspAcyclic
    {certificate : Certificate}
    (correct : certificate.DeclarativelyCorrect) :
    certificate.isCuspAcyclic = true :=
  certificate.isCuspAcyclic_eq_true_iff.mpr correct.cuspAcyclic

/-- Checker acceptance implies acceptance by the colored-cycle oracle. This is
the first differential bridge; the converse requires the separately audited
switching-connectedness/tree argument. -/
theorem isCuspAcyclic_of_check (certificate : Certificate)
    (accepted : certificate.check = true) :
    certificate.isCuspAcyclic = true :=
  (certificate.check_iff_declarativelyCorrect.mp accepted).isCuspAcyclic

end Certificate

end ProofNetIR
