import ProofNetIR.Unification

namespace ProofNetIR

/-!
# Sequential unification primitives

This module begins the separate Guerrini Figures 7--8 implementation.  It
deliberately stops before the `σ`/ready/waiting scheduler.  The current slice
contains the bounded, globally tagged `NEXTAXIOM` search, a rank-scoped
initial/local totality theorem, and an independent dynamic Figure-5 start
refinement.

The search follows the stored left premise of a tensor or par producer.  At an
atom it returns the exact submitted axiom incidence.  A source-incidence table
is built once, so one search step does not rescan the submitted link list.
`SequentialRoute.lean` separately identifies the endpoint actually reached by
the search, which need not be the stored left endpoint of that axiom.

The dynamic start immediately assigns a fresh token and is not the delayed
Figures 7--8 `init`/`new` transition.  Total later-scheduler start selection,
the `σ`/`R`/`W` state, token-age sequencing, and whole-program cost remain
outside this module.
-/

namespace SequentialUnification

/-- One exact submitted link stored in the source-incidence table. -/
structure SourceIncidence where
  linkIndex : Nat
  link : Link
  deriving Repr, DecidableEq

/-- Per-occurrence source incidences.  `nextAxiomWithFuel?` accepts only a
singleton bucket and rejects zero or multiple source entries.
`StructurallyWellFormed.sourceIndex_lookup_eq_singleton` proves that every
in-bounds production bucket is a singleton on the structural theorem
domain.  For a submitted par lookup,
`StructurallyWellFormed.sourceIndex_lookup_eq_submitted_par` identifies that
singleton with the exact submitted link position and value, rather than only
with an equal formula label. -/
abbrev SourceIndex := Array (List SourceIncidence)

private def pushSource (index : SourceIndex) (vertex : Vertex)
    (source : SourceIncidence) : SourceIndex :=
  match index[vertex]? with
  | none => index
  | some sources =>
      index.setIfInBounds vertex (source :: sources)

@[simp] private theorem pushSource_size
    (index : SourceIndex) (vertex : Vertex)
    (source : SourceIncidence) :
    (pushSource index vertex source).size = index.size := by
  unfold pushSource
  split <;> simp

private def addSourceIncidences (index : SourceIndex)
    (entry : Link × Nat) : SourceIndex :=
  let source : SourceIncidence :=
    { linkIndex := entry.2, link := entry.1 }
  match entry.1 with
  | .axiom left right =>
      pushSource (pushSource index left source) right source
  | .tensor _ _ conclusion
  | .par _ _ conclusion =>
      pushSource index conclusion source

@[simp] private theorem addSourceIncidences_size
    (index : SourceIndex) (entry : Link × Nat) :
    (addSourceIncidences index entry).size = index.size := by
  rcases entry with ⟨link, linkIndex⟩
  cases link <;> simp [addSourceIncidences]

/-- Build the reusable occurrence-to-source table in one fold over submitted
links.  Axioms are registered at both endpoints; connectives are registered at
their conclusion. -/
def sourceIndex (certificate : Certificate) : SourceIndex :=
  certificate.links.zipIdx.foldl addSourceIncidences
    (Array.replicate certificate.formulas.size [])

private theorem foldl_addSourceIncidences_size
    (entries : List (Link × Nat)) (index : SourceIndex) :
    (entries.foldl addSourceIncidences index).size = index.size := by
  induction entries generalizing index with
  | nil =>
      rfl
  | cons head tail induction =>
      simp only [List.foldl_cons]
      rw [induction]
      exact addSourceIncidences_size index head

/-- Building the source table preserves the formula-occurrence carrier size. -/
@[simp] theorem sourceIndex_size (certificate : Certificate) :
    (sourceIndex certificate).size = certificate.formulas.size := by
  simp [sourceIndex, foldl_addSourceIncidences_size]

/- `sourceMultiplicity` deliberately counts the two stored endpoints of an
axiom separately.  Thus a malformed self-axiom contributes two entries to one
bucket.  The structural singleton theorem below eliminates that case through
`LinkWellFormed`, rather than silently identifying the two insertions. -/
private def sourceMultiplicity (vertex : Vertex) : Link → Nat
  | .axiom left right =>
      (if left = vertex then 1 else 0) +
        (if right = vertex then 1 else 0)
  | .tensor _ _ conclusion
  | .par _ _ conclusion =>
      if conclusion = vertex then 1 else 0

private theorem pushSource_bucket_length
    {index : SourceIndex} {vertex insertedVertex : Vertex}
    {source : SourceIncidence}
    (vertexBound : vertex < index.size) :
    (((pushSource index insertedVertex source)[vertex]?).getD []).length =
      (if insertedVertex = vertex then 1 else 0) +
        (((index[vertex]?).getD []).length) := by
  by_cases insertedBound : insertedVertex < index.size
  · by_cases same : insertedVertex = vertex
    · subst insertedVertex
      simp [pushSource, vertexBound, Nat.add_comm]
    · simp [pushSource, insertedBound, vertexBound, same]
  · have different : insertedVertex ≠ vertex := by
      intro equation
      subst insertedVertex
      exact insertedBound vertexBound
    have lookupNone : index[insertedVertex]? = none :=
      Array.getElem?_eq_none (Nat.le_of_not_gt insertedBound)
    simp [pushSource, lookupNone, vertexBound, different]

private theorem addSourceIncidences_bucket_length
    {index : SourceIndex} {entry : Link × Nat} {vertex : Vertex}
    (vertexBound : vertex < index.size) :
    (((addSourceIncidences index entry)[vertex]?).getD []).length =
      sourceMultiplicity vertex entry.1 +
        (((index[vertex]?).getD []).length) := by
  rcases entry with ⟨link, linkIndex⟩
  cases link with
  | «axiom» left right =>
      unfold addSourceIncidences
      rw [pushSource_bucket_length
        (index := pushSource index left
          { linkIndex := linkIndex, link := .axiom left right })
        (by simpa using vertexBound)]
      rw [pushSource_bucket_length (index := index) vertexBound]
      simp [sourceMultiplicity, Nat.add_assoc, Nat.add_left_comm]
  | tensor left right conclusion =>
      simpa [addSourceIncidences, sourceMultiplicity] using
        pushSource_bucket_length
          (index := index) (insertedVertex := conclusion)
          (source :=
            { linkIndex := linkIndex,
              link := .tensor left right conclusion })
          vertexBound
  | «par» left right conclusion =>
      simpa [addSourceIncidences, sourceMultiplicity] using
        pushSource_bucket_length
          (index := index) (insertedVertex := conclusion)
          (source :=
            { linkIndex := linkIndex,
              link := .par left right conclusion })
          vertexBound

private theorem foldl_addSourceIncidences_bucket_length
    (entries : List (Link × Nat)) {index : SourceIndex}
    {vertex : Vertex} (vertexBound : vertex < index.size) :
    (((entries.foldl addSourceIncidences index)[vertex]?).getD []).length =
      (entries.map (sourceMultiplicity vertex ∘ Prod.fst)).sum +
        (((index[vertex]?).getD []).length) := by
  induction entries generalizing index with
  | nil =>
      simp
  | cons head tail induction =>
      simp only [List.foldl_cons]
      rw [induction (index := addSourceIncidences index head)
        (by simpa using vertexBound)]
      rw [addSourceIncidences_bucket_length vertexBound]
      simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

private theorem sourceMultiplicity_eq_axiomIndicator_of_atom
    {certificate : Certificate} {vertex : Vertex} {link : Link}
    {name : String} {positive : Bool}
    (wellFormed : certificate.LinkWellFormed link)
    (formulaLookup :
      certificate.formula? vertex = some (.atom name positive)) :
    sourceMultiplicity vertex link =
      if link.containsAxiomEndpoint vertex = true then 1 else 0 := by
  cases link with
  | «axiom» left right =>
      by_cases leftAt : left = vertex <;>
      by_cases rightAt : right = vertex <;>
        simp_all [sourceMultiplicity, Link.containsAxiomEndpoint]
      exact wellFormed.1 rfl
  | tensor left right conclusion =>
      by_cases conclusionAt : conclusion = vertex
      · subst conclusion
        rcases wellFormed.tensor_conclusionFormula with
          ⟨leftFormula, rightFormula, conclusionLookup⟩
        rw [formulaLookup] at conclusionLookup
        cases Option.some.inj conclusionLookup
      · simp [sourceMultiplicity, Link.containsAxiomEndpoint,
          conclusionAt]
  | «par» left right conclusion =>
      by_cases conclusionAt : conclusion = vertex
      · subst conclusion
        rcases wellFormed.par_conclusionFormula with
          ⟨leftFormula, rightFormula, conclusionLookup⟩
        rw [formulaLookup] at conclusionLookup
        cases Option.some.inj conclusionLookup
      · simp [sourceMultiplicity, Link.containsAxiomEndpoint,
          conclusionAt]

private theorem sourceMultiplicity_eq_producerIndicator_of_compound
    {certificate : Certificate} {vertex : Vertex} {link : Link}
    {formula : Formula}
    (wellFormed : certificate.LinkWellFormed link)
    (formulaLookup : certificate.formula? vertex = some formula)
    (compound : formula.isAtom = false) :
    sourceMultiplicity vertex link =
      if link.produces vertex = true then 1 else 0 := by
  cases link with
  | «axiom» left right =>
      by_cases leftAt : left = vertex
      · subst left
        rcases wellFormed.axiom_endpointFormula (Or.inl rfl) with
          ⟨name, positive, atomLookup⟩
        rw [formulaLookup] at atomLookup
        have shape := Option.some.inj atomLookup
        subst formula
        simp [Formula.isAtom] at compound
      · by_cases rightAt : right = vertex
        · subst right
          rcases wellFormed.axiom_endpointFormula (Or.inr rfl) with
            ⟨name, positive, atomLookup⟩
          rw [formulaLookup] at atomLookup
          have shape := Option.some.inj atomLookup
          subst formula
          simp [Formula.isAtom] at compound
        · simp [sourceMultiplicity, Link.produces, leftAt, rightAt]
  | tensor left right conclusion =>
      simp [sourceMultiplicity, Link.produces]
  | «par» left right conclusion =>
      simp [sourceMultiplicity, Link.produces]

private theorem sum_sourceMultiplicity_eq_axiomCount
    {certificate : Certificate} {vertex : Vertex}
    {name : String} {positive : Bool}
    (formulaLookup :
      certificate.formula? vertex = some (.atom name positive))
    (links : List Link)
    (allWellFormed :
      ∀ link ∈ links, certificate.LinkWellFormed link) :
    (links.map (sourceMultiplicity vertex)).sum =
      (links.filter (·.containsAxiomEndpoint vertex)).length := by
  induction links with
  | nil =>
      simp
  | cons head tail induction =>
      have headWellFormed := allWellFormed head (by simp)
      have tailWellFormed :
          ∀ link ∈ tail, certificate.LinkWellFormed link := by
        intro link membership
        exact allWellFormed link (by simp [membership])
      rw [List.map_cons, List.sum_cons,
        sourceMultiplicity_eq_axiomIndicator_of_atom
          headWellFormed formulaLookup,
        induction tailWellFormed]
      by_cases accepted :
          head.containsAxiomEndpoint vertex = true <;>
        simp [accepted, Nat.add_comm]

private theorem sum_sourceMultiplicity_eq_producerCount
    {certificate : Certificate} {vertex : Vertex} {formula : Formula}
    (formulaLookup : certificate.formula? vertex = some formula)
    (compound : formula.isAtom = false)
    (links : List Link)
    (allWellFormed :
      ∀ link ∈ links, certificate.LinkWellFormed link) :
    (links.map (sourceMultiplicity vertex)).sum =
      (links.filter (·.produces vertex)).length := by
  induction links with
  | nil =>
      simp
  | cons head tail induction =>
      have headWellFormed := allWellFormed head (by simp)
      have tailWellFormed :
          ∀ link ∈ tail, certificate.LinkWellFormed link := by
        intro link membership
        exact allWellFormed link (by simp [membership])
      rw [List.map_cons, List.sum_cons,
        sourceMultiplicity_eq_producerIndicator_of_compound
          headWellFormed formulaLookup compound,
        induction tailWellFormed]
      by_cases accepted : head.produces vertex = true <;>
        simp [accepted, Nat.add_comm]

private theorem sourceIndex_bucket_length_eq_one
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {vertex : Vertex} (vertexBound : vertex < certificate.formulas.size) :
    ((((sourceIndex certificate)[vertex]?).getD []).length) = 1 := by
  have folded :=
    foldl_addSourceIncidences_bucket_length certificate.links.zipIdx
      (index := Array.replicate certificate.formulas.size [])
      (vertex := vertex) (by simpa using vertexBound)
  have initialLookup :
      (Array.replicate certificate.formulas.size
        ([] : List SourceIncidence))[vertex]? = some [] := by
    simp [vertexBound]
  rw [initialLookup] at folded
  simp only [Option.getD_some, List.length_nil, Nat.add_zero] at folded
  unfold sourceIndex
  rw [folded]
  rw [← List.map_map, List.zipIdx_map_fst]
  have node := structural.2.2.2.2.2 vertex vertexBound
  cases formulaEquation : certificate.formula? vertex with
  | none =>
      simp [Certificate.NodeWellFormed, formulaEquation] at node
  | some formula =>
      cases formula with
      | atom name positive =>
          rw [sum_sourceMultiplicity_eq_axiomCount formulaEquation
            certificate.links structural.2.2.2.2.1]
          simpa [Certificate.axiomCount,
            Certificate.NodeWellFormed, formulaEquation] using node.1
      | tensor left right =>
          rw [sum_sourceMultiplicity_eq_producerCount formulaEquation
            (by simp [Formula.isAtom]) certificate.links
            structural.2.2.2.2.1]
          simpa [Certificate.producerCount,
            Certificate.NodeWellFormed, formulaEquation] using node.1
      | «par» left right =>
          rw [sum_sourceMultiplicity_eq_producerCount formulaEquation
            (by simp [Formula.isAtom]) certificate.links
            structural.2.2.2.2.1]
          simpa [Certificate.producerCount,
            Certificate.NodeWellFormed, formulaEquation] using node.1

/-- Every in-bounds formula occurrence of a structurally well-formed
certificate has exactly one source-incidence entry.  In particular, the
executable singleton pattern used by `nextAxiomWithFuel?` cannot fail merely
because the input passed the structural checker. -/
theorem StructurallyWellFormed.sourceIndex_lookup_eq_singleton
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {vertex : Vertex} (vertexBound : vertex < certificate.formulas.size) :
    ∃ source,
      (sourceIndex certificate)[vertex]? = some [source] := by
  have sourceIndexBound :
      vertex < (sourceIndex certificate).size := by
    simpa using vertexBound
  have lookupSome :
      ∃ sources, (sourceIndex certificate)[vertex]? = some sources := by
    exact
      ⟨(sourceIndex certificate)[vertex],
        Array.getElem?_eq_getElem sourceIndexBound⟩
  rcases lookupSome with ⟨sources, lookup⟩
  have length : sources.length = 1 := by
    have bucketLength :=
      sourceIndex_bucket_length_eq_one structural vertexBound
    simpa [lookup] using bucketLength
  rcases List.length_eq_one_iff.mp length with ⟨source, rfl⟩
  exact ⟨source, lookup⟩

private theorem pushSource_mem_of_mem
    {index : SourceIndex} {inserted vertex : Vertex}
    {source candidate : SourceIncidence}
    (membership : candidate ∈ ((index[vertex]?).getD [])) :
    candidate ∈
      (((pushSource index inserted source)[vertex]?).getD []) := by
  by_cases insertedBound : inserted < index.size
  · by_cases same : inserted = vertex
    · subst inserted
      simpa [pushSource, insertedBound] using Or.inr membership
    · simp [pushSource, insertedBound, same]
      exact membership
  · have lookupNone : index[inserted]? = none :=
      Array.getElem?_eq_none (Nat.le_of_not_gt insertedBound)
    simpa [pushSource, lookupNone] using membership

private theorem addSourceIncidences_mem_of_mem
    {index : SourceIndex} {entry : Link × Nat}
    {vertex : Vertex} {candidate : SourceIncidence}
    (membership : candidate ∈ ((index[vertex]?).getD [])) :
    candidate ∈
      (((addSourceIncidences index entry)[vertex]?).getD []) := by
  rcases entry with ⟨link, linkIndex⟩
  cases link with
  | «axiom» left right =>
      exact pushSource_mem_of_mem (pushSource_mem_of_mem membership)
  | tensor left right conclusion =>
      exact pushSource_mem_of_mem membership
  | «par» left right conclusion =>
      exact pushSource_mem_of_mem membership

private theorem foldl_addSourceIncidences_mem_of_mem
    (entries : List (Link × Nat))
    {index : SourceIndex} {vertex : Vertex}
    {candidate : SourceIncidence}
    (membership : candidate ∈ ((index[vertex]?).getD [])) :
    candidate ∈
      (((entries.foldl addSourceIncidences index)[vertex]?).getD []) := by
  induction entries generalizing index with
  | nil => exact membership
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction (addSourceIncidences_mem_of_mem membership)

private theorem addSourceIncidences_par_mem
    {index : SourceIndex} {linkIndex : Nat}
    {left right conclusion : Vertex}
    (conclusionBound : conclusion < index.size) :
    ({
      linkIndex := linkIndex
      link := .par left right conclusion } : SourceIncidence) ∈
      (((addSourceIncidences index
        (.par left right conclusion, linkIndex))[conclusion]?).getD []) := by
  simp [addSourceIncidences, pushSource, conclusionBound]

private theorem foldl_addSourceIncidences_par_mem
    (entries : List (Link × Nat))
    {index : SourceIndex} {linkIndex : Nat}
    {left right conclusion : Vertex}
    (entryMembership :
      ((.par left right conclusion : Link), linkIndex) ∈ entries)
    (conclusionBound : conclusion < index.size) :
    ({
      linkIndex := linkIndex
      link := .par left right conclusion } : SourceIncidence) ∈
      (((entries.foldl addSourceIncidences index)[conclusion]?).getD []) := by
  induction entries generalizing index with
  | nil => simp at entryMembership
  | cons head tail induction =>
      simp only [List.mem_cons] at entryMembership
      rcases entryMembership with rfl | inTail
      · simp only [List.foldl_cons]
        exact foldl_addSourceIncidences_mem_of_mem tail
          (addSourceIncidences_par_mem conclusionBound)
      · simp only [List.foldl_cons]
        exact induction inTail (by
          simpa only [addSourceIncidences_size] using conclusionBound)

/-- An exact submitted par producer occurs at its exact submitted-link position
in the reusable source-incidence table.  This theorem preserves positional
identity even when distinct submitted slots contain equal-valued links. -/
theorem sourceIndex_par_mem
    {certificate : Certificate} {linkIndex : Nat}
    {left right conclusion : Vertex}
    (linkLookup : certificate.links[linkIndex]? =
      some (.par left right conclusion))
    (conclusionBound : conclusion < certificate.formulas.size) :
    ({
      linkIndex := linkIndex
      link := .par left right conclusion } : SourceIncidence) ∈
      (((sourceIndex certificate)[conclusion]?).getD []) := by
  unfold sourceIndex
  apply foldl_addSourceIncidences_par_mem
  · exact List.mk_mem_zipIdx_iff_getElem?.2 linkLookup
  · simpa using conclusionBound

private theorem lookup_eq_singleton_of_mem_length_one
    {α : Type} {values : Array (List α)} {index : Nat}
    {candidate : α}
    (membership : candidate ∈ ((values[index]?).getD []))
    (length : ((values[index]?).getD []).length = 1) :
    values[index]? = some [candidate] := by
  cases lookup : values[index]? with
  | none => simp [lookup] at length
  | some bucket =>
      have bucketLength : bucket.length = 1 := by
        simpa [lookup] using length
      rcases List.length_eq_one_iff.mp bucketLength with ⟨only, rfl⟩
      have same : candidate = only := by
        simpa [lookup] using membership
      subst only
      rfl

/-- A structurally well-formed certificate maps an exact submitted par
producer to that same exact submitted-link position in its singleton source
bucket.  The positional conclusion is stronger than bare source uniqueness. -/
theorem StructurallyWellFormed.sourceIndex_lookup_eq_submitted_par
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {linkIndex : Nat} {left right conclusion : Vertex}
    (linkLookup : certificate.links[linkIndex]? =
      some (.par left right conclusion)) :
    (sourceIndex certificate)[conclusion]? =
      some [{
        linkIndex := linkIndex
        link := .par left right conclusion }] := by
  have linkMembership :
      Link.par left right conclusion ∈ certificate.links :=
    List.mem_of_getElem? linkLookup
  have linkWellFormed :
      certificate.LinkWellFormed (.par left right conclusion) :=
    structural.2.2.2.2.1 _ linkMembership
  have conclusionBound : conclusion < certificate.formulas.size :=
    linkWellFormed.2.2.2.2.2.1
  apply lookup_eq_singleton_of_mem_length_one
  · exact sourceIndex_par_mem linkLookup conclusionBound
  · exact sourceIndex_bucket_length_eq_one structural conclusionBound

private theorem mem_pushSource_origin
    {index : SourceIndex} {vertex insertedVertex : Vertex}
    {source candidate : SourceIncidence}
    (membership :
      candidate ∈
        ((pushSource index insertedVertex source)[vertex]?).getD []) :
    (candidate = source ∧ vertex = insertedVertex) ∨
      candidate ∈ (index[vertex]?).getD [] := by
  by_cases insertedBound : insertedVertex < index.size
  · by_cases same : insertedVertex = vertex
    · subst vertex
      have introduced :
          candidate = source ∨
            candidate ∈ index[insertedVertex] := by
        simpa [pushSource, insertedBound] using membership
      rcases introduced with introduced | old
      · exact Or.inl ⟨introduced, rfl⟩
      · apply Or.inr
        rw [Array.getElem?_eq_getElem insertedBound]
        simpa using old
    · apply Or.inr
      simpa [pushSource, insertedBound, same] using membership
  · have lookupNone : index[insertedVertex]? = none :=
      Array.getElem?_eq_none (Nat.le_of_not_gt insertedBound)
    apply Or.inr
    simpa [pushSource, lookupNone] using membership

private theorem mem_addSourceIncidences_origin
    {index : SourceIndex} {entry : Link × Nat}
    {vertex : Vertex} {candidate : SourceIncidence}
    (membership :
      candidate ∈
        ((addSourceIncidences index entry)[vertex]?).getD []) :
    (candidate = { linkIndex := entry.2, link := entry.1 } ∧
      (entry.1.containsAxiomEndpoint vertex = true ∨
        entry.1.produces vertex = true)) ∨
      candidate ∈ (index[vertex]?).getD [] := by
  rcases entry with ⟨link, linkIndex⟩
  cases link with
  | «axiom» left right =>
      have rightOrigin := mem_pushSource_origin membership
      rcases rightOrigin with rightInserted | beforeRight
      · exact Or.inl
          ⟨rightInserted.1, by
            simp [Link.containsAxiomEndpoint, rightInserted.2]⟩
      · have leftOrigin := mem_pushSource_origin beforeRight
        rcases leftOrigin with leftInserted | old
        · exact Or.inl
            ⟨leftInserted.1, by
              simp [Link.containsAxiomEndpoint, leftInserted.2]⟩
        · exact Or.inr old
  | tensor left right conclusion =>
      rcases mem_pushSource_origin membership with introduced | old
      · exact Or.inl
          ⟨introduced.1, by
            simp [Link.produces, introduced.2]⟩
      · exact Or.inr old
  | «par» left right conclusion =>
      rcases mem_pushSource_origin membership with introduced | old
      · exact Or.inl
          ⟨introduced.1, by
            simp [Link.produces, introduced.2]⟩
      · exact Or.inr old

private theorem mem_foldl_addSourceIncidences_origin
    (entries : List (Link × Nat))
    {index : SourceIndex} {vertex : Vertex}
    {candidate : SourceIncidence}
    (membership :
      candidate ∈
        ((entries.foldl addSourceIncidences index)[vertex]?).getD []) :
    (∃ entry ∈ entries,
      candidate =
        { linkIndex := entry.2, link := entry.1 } ∧
      (entry.1.containsAxiomEndpoint vertex = true ∨
        entry.1.produces vertex = true)) ∨
      candidate ∈ (index[vertex]?).getD [] := by
  induction entries generalizing index with
  | nil =>
      exact Or.inr membership
  | cons head tail induction =>
      simp only [List.foldl_cons] at membership
      rcases induction membership with introduced | beforeTail
      · rcases introduced with
          ⟨entry, entryMembership, candidateEquation, source⟩
        exact Or.inl
          ⟨entry, by simp [entryMembership],
            candidateEquation, source⟩
      · rcases mem_addSourceIncidences_origin beforeTail with
          introduced | old
        · exact Or.inl
            ⟨head, by simp, introduced.1, introduced.2⟩
        · exact Or.inr old

/-- Every stored source incidence names the exact submitted link at its exact
list index and is genuinely incident as an axiom endpoint or connective
conclusion. -/
theorem mem_sourceIndex_origin
    {certificate : Certificate} {vertex : Vertex}
    {candidate : SourceIncidence}
    (membership :
      candidate ∈
        (((sourceIndex certificate)[vertex]?).getD [])) :
    certificate.links[candidate.linkIndex]? = some candidate.link ∧
      (candidate.link.containsAxiomEndpoint vertex = true ∨
        candidate.link.produces vertex = true) := by
  have foldedMembership :
      candidate ∈
        (((certificate.links.zipIdx.foldl addSourceIncidences
          (Array.replicate certificate.formulas.size
            ([] : List SourceIncidence)))[vertex]?).getD []) := by
    simpa [sourceIndex] using membership
  rcases mem_foldl_addSourceIncidences_origin certificate.links.zipIdx
      foldedMembership with introduced | initial
  · rcases introduced with
      ⟨entry, entryMembership, candidateEquation, source⟩
    subst candidate
    exact
      ⟨List.mk_mem_zipIdx_iff_getElem?.1 entryMembership, source⟩
  · by_cases vertexBound : vertex < certificate.formulas.size
    · have lookup :
          (Array.replicate certificate.formulas.size
            ([] : List SourceIncidence))[vertex]? = some [] := by
        simp [vertexBound]
      rw [lookup] at initial
      simp at initial
    · have lookup :
          (Array.replicate certificate.formulas.size
            ([] : List SourceIncidence))[vertex]? = none :=
        Array.getElem?_eq_none (by
          simpa using Nat.le_of_not_gt vertexBound)
      rw [lookup] at initial
      simp at initial

/-- Every table entry has exact submitted-link and source-incidence
provenance.  Supplying this proof separately lets the recursive executable
reuse one precomputed table without rebuilding it. -/
def SourceIndex.Sound (certificate : Certificate)
    (index : SourceIndex) : Prop :=
  ∀ {vertex : Vertex} {candidate : SourceIncidence},
    candidate ∈ (index[vertex]?).getD [] →
      certificate.links[candidate.linkIndex]? = some candidate.link ∧
        (candidate.link.containsAxiomEndpoint vertex = true ∨
          candidate.link.produces vertex = true)

/-- The production source-incidence table is sound. -/
theorem sourceIndex_sound (certificate : Certificate) :
    SourceIndex.Sound certificate (sourceIndex certificate) := by
  intro vertex candidate membership
  exact mem_sourceIndex_origin membership

/-- Successful bounded `NEXTAXIOM` search.

`trace` records the vertices actually followed by the recursive search.  The
partner endpoint of the returned axiom is tagged as required by Guerrini but
is not an additional recursive trace step. -/
structure NextAxiomResult (certificate : Certificate)
    (state : UnificationState) (fuel : Nat)
    (inputTags : Array Bool) where
  linkIndex : Nat
  left : Vertex
  right : Vertex
  tags : Array Bool
  trace : List Vertex
  exactLink :
    certificate.links[linkIndex]? = some (.axiom left right)
  leftReady : state.marks[left]? = some none
  rightReady : state.marks[right]? = some none
  traceLength : trace.length ≤ fuel
  tagsSize : tags.size = inputTags.size
  preservesTrue :
    ∀ {vertex : Vertex}, inputTags[vertex]? = some true →
      tags[vertex]? = some true
  traceNodup : trace.Nodup
  traceTagged :
    ∀ {vertex : Vertex}, vertex ∈ trace →
      inputTags[vertex]? = some false ∧
        tags[vertex]? = some true
  leftTagged :
    inputTags[left]? = some false ∧
      tags[left]? = some true
  rightTagged :
    inputTags[right]? = some false ∧
      tags[right]? = some true
  deriving Repr

/-- A vertex touched by one successful `NEXTAXIOM` call: either a recursive
trace vertex or one of the two returned axiom endpoints.  The partner endpoint
need not occur in `trace`, so it is named explicitly here. -/
def NextAxiomResult.Touched
    {certificate : Certificate} {state : UnificationState} {fuel : Nat}
    {inputTags : Array Bool}
    (result : NextAxiomResult certificate state fuel inputTags)
    (vertex : Vertex) : Prop :=
  vertex ∈ result.trace ∨
    vertex = result.left ∨ vertex = result.right

/-- A later successful search cannot return the same submitted axiom-link
index when its input already tags the earlier result's left endpoint.  This is
a structural property of the two results: their marking states, fuel bounds,
and search executions may all differ.  Distinct duplicate link slots are not
identified by this theorem. -/
theorem NextAxiomResult.linkIndex_ne_of_input_left_tagged
    {certificate : Certificate}
    {firstState secondState : UnificationState}
    {firstFuel secondFuel : Nat}
    {firstInput secondInput : Array Bool}
    (first :
      NextAxiomResult certificate firstState firstFuel firstInput)
    (second :
      NextAxiomResult certificate secondState secondFuel secondInput)
    (firstLeftTagged :
      secondInput[first.left]? = some true) :
    first.linkIndex ≠ second.linkIndex := by
  intro sameLinkIndex
  have sameAxiom :
      some (Link.axiom first.left first.right) =
        some (Link.axiom second.left second.right) := by
    calc
      some (Link.axiom first.left first.right) =
          certificate.links[first.linkIndex]? :=
        first.exactLink.symm
      _ = certificate.links[second.linkIndex]? := by
        rw [sameLinkIndex]
      _ = some (Link.axiom second.left second.right) :=
        second.exactLink
  have sameLink :
      Link.axiom first.left first.right =
        Link.axiom second.left second.right :=
    Option.some.inj sameAxiom
  have sameLeft : first.left = second.left := by
    injection sameLink
  rw [sameLeft] at firstLeftTagged
  rw [second.leftTagged.1] at firstLeftTagged
  contradiction

/-- Threading the complete output tag array of one successful search into the
next search prevents replay of the first submitted axiom-link index.  No
relation between the two unification states is required; distinct duplicate
link slots are outside this conclusion. -/
theorem NextAxiomResult.threaded_linkIndex_ne
    {certificate : Certificate}
    {firstState secondState : UnificationState}
    {firstFuel secondFuel : Nat}
    {inputTags : Array Bool}
    (first :
      NextAxiomResult certificate firstState firstFuel inputTags)
    (second :
      NextAxiomResult certificate secondState secondFuel first.tags) :
    first.linkIndex ≠ second.linkIndex :=
  first.linkIndex_ne_of_input_left_tagged second first.leftTagged.2

/-- Dynamic freshness through one formula-complexity rank.

This is a sufficient local precondition for the bounded `NEXTAXIOM` search,
not a reachable-state invariant for the complete Figure-7 scheduler.  It is
intentionally rank-scoped: all in-bounds occurrences no more complex than
`rank` must still be untagged and semantically unassigned. -/
def SearchClearThrough (certificate : Certificate)
    (state : UnificationState) (tags : Array Bool)
    (rank : Nat) : Prop :=
  ∀ {vertex : Vertex},
    vertex < certificate.formulas.size →
      certificate.formulaComplexityAt vertex ≤ rank →
        tags[vertex]? = some false ∧
          state.assignedToken? vertex = none

private def setTag (tags : Array Bool) (vertex : Vertex) :
    Array Bool :=
  tags.setIfInBounds vertex true

@[simp] private theorem setTag_size
    (tags : Array Bool) (vertex : Vertex) :
    (setTag tags vertex).size = tags.size := by
  simp [setTag]

private theorem setTag_self_true
    {tags : Array Bool} {vertex : Vertex}
    (inputFalse : tags[vertex]? = some false) :
    (setTag tags vertex)[vertex]? = some true := by
  have bound : vertex < tags.size :=
    (Array.getElem?_eq_some_iff.mp inputFalse).1
  simp [setTag, bound]

private theorem setTag_true_monotone
    {tags : Array Bool} {tagged vertex : Vertex}
    (inputTrue : tags[tagged]? = some true) :
    (setTag tags vertex)[tagged]? = some true := by
  by_cases same : vertex = tagged
  · subst tagged
    have bound : vertex < tags.size :=
      (Array.getElem?_eq_some_iff.mp inputTrue).1
    simp [setTag, bound]
  · simpa [setTag, same] using inputTrue

private theorem setTag_true_origin
    {tags : Array Bool} {tagged vertex : Vertex}
    (outputTrue : (setTag tags tagged)[vertex]? = some true) :
    tags[vertex]? = some true ∨ vertex = tagged := by
  by_cases same : tagged = vertex
  · exact Or.inr same.symm
  · exact Or.inl (by
      simpa [setTag, same] using outputTrue)

private theorem setTag_false_reflection
    {tags : Array Bool} {tagged vertex : Vertex}
    (outputFalse : (setTag tags tagged)[vertex]? = some false) :
    tags[vertex]? = some false ∧ vertex ≠ tagged := by
  by_cases same : tagged = vertex
  · subst vertex
    simp [setTag, Array.getElem?_setIfInBounds_self] at outputFalse
  · exact ⟨by simpa [setTag, same] using outputFalse,
      fun reverse => same reverse.symm⟩

/-- Tagging a strictly more complex parent preserves rank-scoped freshness
through a selected lower-complexity premise. -/
private theorem SearchClearThrough.setTag_of_strict
    {certificate : Certificate} {state : UnificationState}
    {tags : Array Bool} {parent child : Vertex}
    (clear :
      SearchClearThrough certificate state tags
        (certificate.formulaComplexityAt parent))
    (strict :
      certificate.formulaComplexityAt child <
        certificate.formulaComplexityAt parent) :
    SearchClearThrough certificate state (setTag tags parent)
      (certificate.formulaComplexityAt child) := by
  intro candidate candidateBound candidateRank
  have candidateClear :=
    clear candidateBound
      (Nat.le_trans candidateRank (Nat.le_of_lt strict))
  have different : parent ≠ candidate := by
    intro same
    subst candidate
    omega
  refine ⟨?_, candidateClear.2⟩
  simpa [setTag, different] using candidateClear.1

/-- Bounded, tagged `NEXTAXIOM`.

The search fails closed on out-of-domain, already tagged, already marked,
missing, or non-unique source buckets.  Compound producers deterministically
continue through their stored left premise. -/
def nextAxiomWithFuel? (certificate : Certificate)
    (state : UnificationState) (index : SourceIndex)
    (indexSound : SourceIndex.Sound certificate index) :
    (fuel : Nat) → (tags : Array Bool) → Vertex →
      Option (NextAxiomResult certificate state fuel tags)
  | 0, _tags, _vertex => none
  | fuel + 1, tags, vertex =>
      if vertexTag : tags[vertex]? = some false then
        if vertexReady : state.marks[vertex]? = some none then
          match sourceLookup : index[vertex]? with
          | some [source] =>
              have sourceMembership :
                  source ∈ (index[vertex]?).getD [] := by
                simp [sourceLookup]
              have sourceOrigin :=
                indexSound sourceMembership
              match linkEquation : source.link with
              | .axiom left right =>
                  if different : left ≠ right then
                    if atEndpoint :
                        vertex = left ∨ vertex = right then
                      if leftTag : tags[left]? = some false then
                        if rightTag : tags[right]? = some false then
                          if leftReady :
                              state.marks[left]? = some none then
                            if rightReady :
                                state.marks[right]? = some none then
                              some {
                                linkIndex := source.linkIndex
                                left
                                right
                                tags :=
                                  setTag (setTag tags left) right
                                trace := [vertex]
                                exactLink := by
                                  simpa [linkEquation] using sourceOrigin.1
                                leftReady
                                rightReady
                                traceLength := by simp
                                tagsSize := by
                                  simp
                                preservesTrue := by
                                  intro tagged inputTrue
                                  exact setTag_true_monotone
                                    (setTag_true_monotone inputTrue)
                                traceNodup := by simp
                                traceTagged := by
                                  intro tagged membership
                                  simp only [List.mem_singleton] at membership
                                  subst tagged
                                  refine ⟨vertexTag, ?_⟩
                                  rcases atEndpoint with rfl | rfl
                                  · exact setTag_true_monotone
                                      (setTag_self_true leftTag)
                                  · have rightAfterLeft :
                                        (setTag tags left)[vertex]? =
                                          some false := by
                                      simpa [setTag, different] using vertexTag
                                    exact setTag_self_true rightAfterLeft
                                leftTagged := by
                                  refine ⟨leftTag, ?_⟩
                                  exact setTag_true_monotone
                                    (setTag_self_true leftTag)
                                rightTagged := by
                                  refine ⟨rightTag, ?_⟩
                                  have rightAfterLeft :
                                      (setTag tags left)[right]? =
                                        some false := by
                                    simpa [setTag, different] using rightTag
                                  exact setTag_self_true rightAfterLeft
                              }
                            else none
                          else none
                        else none
                      else none
                    else none
                  else none
              | .tensor left _right conclusion
              | .par left _right conclusion =>
                  if produced : conclusion = vertex then
                    match nextAxiomWithFuel? certificate state index
                        indexSound fuel (setTag tags vertex) left with
                    | none => none
                    | some result =>
                        some {
                          linkIndex := result.linkIndex
                          left := result.left
                          right := result.right
                          tags := result.tags
                          trace := vertex :: result.trace
                          exactLink := result.exactLink
                          leftReady := result.leftReady
                          rightReady := result.rightReady
                          traceLength := by
                            simpa using
                              Nat.succ_le_succ result.traceLength
                          tagsSize := by
                            simpa using result.tagsSize
                          preservesTrue := by
                            intro tagged inputTrue
                            exact result.preservesTrue
                              (setTag_true_monotone inputTrue)
                          traceNodup := by
                            rw [List.nodup_cons]
                            refine ⟨?_, result.traceNodup⟩
                            intro membership
                            have recursiveFalse :=
                              (result.traceTagged membership).1
                            have currentTrue :=
                              setTag_self_true vertexTag
                            rw [currentTrue] at recursiveFalse
                            contradiction
                          traceTagged := by
                            intro tagged membership
                            simp only [List.mem_cons] at membership
                            rcases membership with rfl | membership
                            · refine ⟨vertexTag, ?_⟩
                              exact result.preservesTrue
                                (setTag_self_true vertexTag)
                            · have recursive :=
                                result.traceTagged membership
                              exact
                                ⟨(setTag_false_reflection recursive.1).1,
                                  recursive.2⟩
                          leftTagged := by
                            exact
                              ⟨(setTag_false_reflection
                                  result.leftTagged.1).1,
                                result.leftTagged.2⟩
                          rightTagged := by
                            exact
                              ⟨(setTag_false_reflection
                                  result.rightTagged.1).1,
                                result.rightTagged.2⟩
                        }
                      else none
          | _ => none
        else none
      else none

/-- Every true output tag of one successful executable `NEXTAXIOM` call comes
from the input carrier or the exact trace/endpoints touched by that call.  The
execution equation is essential: the public result record by itself permits
manual inhabitants that do not arise from the search. -/
private theorem nextAxiomWithFuel?_true_origin
    {certificate : Certificate} {state : UnificationState}
    {index : SourceIndex} {fuel : Nat} {tags : Array Bool}
    {indexSound : SourceIndex.Sound certificate index}
    {start : Vertex}
    {result : NextAxiomResult certificate state fuel tags}
    (equation :
      nextAxiomWithFuel? certificate state index indexSound fuel tags start =
        some result) :
    ∀ {tagged : Vertex},
      result.tags[tagged]? = some true →
        tags[tagged]? = some true ∨ result.Touched tagged := by
  induction fuel generalizing tags start with
  | zero =>
      simp [nextAxiomWithFuel?] at equation
  | succ fuel induction =>
      simp only [nextAxiomWithFuel?] at equation
      repeat
        first
        | split at equation
        | contradiction
      all_goals simp at equation
      case h_1.isTrue.isTrue.isTrue.isTrue.isTrue.isTrue =>
        rename_i vertexTag vertexReady source sourceLookup left right
          linkEquation different atEndpoint leftTag rightTag leftReady
          rightReady
        subst result
        intro tagged outputTrue
        rcases setTag_true_origin outputTrue with
          taggedAfterLeft | rfl
        · rcases setTag_true_origin taggedAfterLeft with
            inputTrue | rfl
          · exact Or.inl inputTrue
          · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
      case h_2 =>
        rename_i vertexTag vertexReady source sourceLookup left right
          conclusion linkEquation
        rcases equation with ⟨produced, equation⟩
        split at equation
        · simp at equation
        · rename_i recursiveResult recursiveEquation
          simp at equation
          subst result
          intro tagged outputTrue
          rcases induction recursiveEquation outputTrue with
            recursiveInput | recursiveTouched
          · rcases setTag_true_origin recursiveInput with inputTrue | rfl
            · exact Or.inl inputTrue
            · exact Or.inr (Or.inl (by simp))
          · rcases recursiveTouched with inTrace | sameLeft | sameRight
            · exact Or.inr (Or.inl (by simp [inTrace]))
            · exact Or.inr (Or.inr (Or.inl sameLeft))
            · exact Or.inr (Or.inr (Or.inr sameRight))
      case h_3 =>
        rename_i vertexTag vertexReady source sourceLookup left right
          conclusion linkEquation
        rcases equation with ⟨produced, equation⟩
        split at equation
        · simp at equation
        · rename_i recursiveResult recursiveEquation
          simp at equation
          subst result
          intro tagged outputTrue
          rcases induction recursiveEquation outputTrue with
            recursiveInput | recursiveTouched
          · rcases setTag_true_origin recursiveInput with inputTrue | rfl
            · exact Or.inl inputTrue
            · exact Or.inr (Or.inl (by simp))
          · rcases recursiveTouched with inTrace | sameLeft | sameRight
            · exact Or.inr (Or.inl (by simp [inTrace]))
            · exact Or.inr (Or.inr (Or.inl sameLeft))
            · exact Or.inr (Or.inr (Or.inr sameRight))

/-- On the production source index, structural well-formedness and
rank-scoped dynamic freshness make bounded `NEXTAXIOM` locally total whenever
the fuel strictly exceeds the starting formula complexity.

This theorem discharges the static missing/non-unique-source, malformed
orientation, out-of-bounds, and recursive-fuel failure modes for this local
call.  It does not state that an arbitrary later Figure-7 `new` call satisfies
the freshness premise. -/
theorem nextAxiomWithFuel?_exists_of_structural_clearThrough
    {certificate : Certificate} {state : UnificationState}
    {fuel : Nat} {tags : Array Bool} {vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (abstractable : state.Abstractable certificate)
    (vertexBound : vertex < certificate.formulas.size)
    (clear :
      SearchClearThrough certificate state tags
        (certificate.formulaComplexityAt vertex))
    (fuelEnough :
      certificate.formulaComplexityAt vertex < fuel) :
    ∃ result,
      nextAxiomWithFuel? certificate state
          (sourceIndex certificate) (sourceIndex_sound certificate)
          fuel tags vertex =
        some result := by
  let startRank := certificate.formulaComplexityAt vertex
  have general :
      ∀ rank,
        rank ≤ startRank →
          ∀ (candidate : Vertex) (remainingFuel : Nat)
              (candidateTags : Array Bool),
            certificate.formulaComplexityAt candidate = rank →
              candidate < certificate.formulas.size →
                SearchClearThrough certificate state candidateTags rank →
                  rank < remainingFuel →
                    ∃ result,
                      nextAxiomWithFuel? certificate state
                          (sourceIndex certificate)
                          (sourceIndex_sound certificate)
                          remainingFuel candidateTags candidate =
                        some result := by
    intro rank rankAtMostStart
    induction rank using Nat.strongRecOn with
    | ind rank induction =>
        intro candidate remainingFuel candidateTags
          candidateRank candidateBound candidateClear remainingEnough
        cases remainingFuel with
        | zero =>
            omega
        | succ remainingFuel =>
            have currentClear :
                candidateTags[candidate]? = some false ∧
                  state.assignedToken? candidate = none := by
              exact candidateClear candidateBound
                (by simp [candidateRank])
            have currentReady :
                state.marks[candidate]? = some none :=
              abstractable.markSlotReady_of_unassigned
                candidateBound currentClear.2
            rcases
                StructurallyWellFormed.sourceIndex_lookup_eq_singleton
                  structural candidateBound with
              ⟨source, sourceLookup⟩
            have sourceMembership :
                source ∈
                  (((sourceIndex certificate)[candidate]?).getD []) := by
              simp [sourceLookup]
            have sourceOrigin :=
              sourceIndex_sound certificate sourceMembership
            have linkMembership :
                source.link ∈ certificate.links :=
              List.mem_of_getElem? sourceOrigin.1
            have sourceWellFormed :
                certificate.LinkWellFormed source.link :=
              structural.2.2.2.2.1 source.link linkMembership
            cases linkEquation : source.link with
            | «axiom» left right =>
                have axiomWellFormed :
                    certificate.LinkWellFormed (.axiom left right) := by
                  simpa [linkEquation] using sourceWellFormed
                have endpoint :
                    candidate = left ∨ candidate = right := by
                  have incident := sourceOrigin.2
                  simp [linkEquation, Link.containsAxiomEndpoint,
                    Link.produces] at incident
                  rcases incident with incident | incident
                  · exact .inl incident.symm
                  · exact .inr incident.symm
                have leftBound :
                    left < certificate.formulas.size :=
                  axiomWellFormed.2.1
                have rightBound :
                    right < certificate.formulas.size :=
                  axiomWellFormed.2.2.1
                rcases
                    axiomWellFormed.axiom_endpointFormula (Or.inl rfl) with
                  ⟨leftName, leftPositive, leftFormula⟩
                rcases
                    axiomWellFormed.axiom_endpointFormula (Or.inr rfl) with
                  ⟨rightName, rightPositive, rightFormula⟩
                have leftRank :
                    certificate.formulaComplexityAt left = 0 := by
                  simp [Certificate.formulaComplexityAt, leftFormula,
                    Formula.complexity]
                have rightRank :
                    certificate.formulaComplexityAt right = 0 := by
                  simp [Certificate.formulaComplexityAt, rightFormula,
                    Formula.complexity]
                have leftClear :=
                  candidateClear leftBound (by simp [leftRank])
                have rightClear :=
                  candidateClear rightBound (by simp [rightRank])
                have leftReady :
                    state.marks[left]? = some none :=
                  abstractable.markSlotReady_of_unassigned
                    leftBound leftClear.2
                have rightReady :
                    state.marks[right]? = some none :=
                  abstractable.markSlotReady_of_unassigned
                    rightBound rightClear.2
                unfold nextAxiomWithFuel?
                simp only [dif_pos currentClear.1, dif_pos currentReady]
                split
                · rename_i sourceInFunction lookupInFunction
                  have sameSingleton :
                      (some [sourceInFunction] :
                          Option (List SourceIncidence)) =
                        some [source] := by
                    exact lookupInFunction.symm.trans sourceLookup
                  have sameSource : sourceInFunction = source := by
                    simpa using sameSingleton
                  subst sourceInFunction
                  split <;> simp_all
                  exact ⟨_, axiomWellFormed.1, rfl⟩
                · simp_all
            | tensor left right conclusion =>
                have tensorWellFormed :
                    certificate.LinkWellFormed
                      (.tensor left right conclusion) := by
                  simpa [linkEquation] using sourceWellFormed
                have produced : conclusion = candidate := by
                  have incident := sourceOrigin.2
                  simpa [linkEquation, Link.containsAxiomEndpoint,
                    Link.produces] using incident
                subst conclusion
                have leftBound :
                    left < certificate.formulas.size :=
                  tensorWellFormed.2.2.2.1
                have strict :
                    certificate.formulaComplexityAt left <
                      certificate.formulaComplexityAt candidate := by
                  simpa [Certificate.linkConclusionComplexity] using
                    tensorWellFormed.premise_complexity_lt_conclusion
                      (premise := left) (by simp [Link.premises])
                have strictRank :
                    certificate.formulaComplexityAt left < rank := by
                  simpa [candidateRank] using strict
                have remainingEnough :
                    certificate.formulaComplexityAt left <
                      remainingFuel := by
                  omega
                have recursiveClear :
                    SearchClearThrough certificate state
                      (setTag candidateTags candidate)
                      (certificate.formulaComplexityAt left) := by
                  have clearAtCandidate :
                      SearchClearThrough certificate state candidateTags
                        (certificate.formulaComplexityAt candidate) := by
                    intro visited visitedBound visitedRank
                    exact candidateClear visitedBound
                      (by simpa [candidateRank] using visitedRank)
                  intro visited visitedBound visitedRank
                  exact
                    SearchClearThrough.setTag_of_strict
                      (certificate := certificate) (state := state)
                      (tags := candidateTags) (parent := candidate)
                      (child := left) (vertex := visited)
                      clearAtCandidate strict visitedBound visitedRank
                rcases induction
                    (certificate.formulaComplexityAt left) strictRank
                    (Nat.le_trans (Nat.le_of_lt strictRank)
                      rankAtMostStart)
                    left remainingFuel
                    (setTag candidateTags candidate) rfl leftBound
                    recursiveClear remainingEnough with
                  ⟨result, recursiveEquation⟩
                unfold nextAxiomWithFuel?
                simp only [dif_pos currentClear.1, dif_pos currentReady]
                split
                · rename_i sourceInFunction lookupInFunction
                  have sameSingleton :
                      (some [sourceInFunction] :
                          Option (List SourceIncidence)) =
                        some [source] := by
                    exact lookupInFunction.symm.trans sourceLookup
                  have sameSource : sourceInFunction = source := by
                    simpa using sameSingleton
                  subst sourceInFunction
                  split <;> simp_all
                · simp_all
            | «par» left right conclusion =>
                have parWellFormed :
                    certificate.LinkWellFormed
                      (.par left right conclusion) := by
                  simpa [linkEquation] using sourceWellFormed
                have produced : conclusion = candidate := by
                  have incident := sourceOrigin.2
                  simpa [linkEquation, Link.containsAxiomEndpoint,
                    Link.produces] using incident
                subst conclusion
                have leftBound :
                    left < certificate.formulas.size :=
                  parWellFormed.2.2.2.1
                have strict :
                    certificate.formulaComplexityAt left <
                      certificate.formulaComplexityAt candidate := by
                  simpa [Certificate.linkConclusionComplexity] using
                    parWellFormed.premise_complexity_lt_conclusion
                      (premise := left) (by simp [Link.premises])
                have strictRank :
                    certificate.formulaComplexityAt left < rank := by
                  simpa [candidateRank] using strict
                have remainingEnough :
                    certificate.formulaComplexityAt left <
                      remainingFuel := by
                  omega
                have recursiveClear :
                    SearchClearThrough certificate state
                      (setTag candidateTags candidate)
                      (certificate.formulaComplexityAt left) := by
                  have clearAtCandidate :
                      SearchClearThrough certificate state candidateTags
                        (certificate.formulaComplexityAt candidate) := by
                    intro visited visitedBound visitedRank
                    exact candidateClear visitedBound
                      (by simpa [candidateRank] using visitedRank)
                  intro visited visitedBound visitedRank
                  exact
                    SearchClearThrough.setTag_of_strict
                      (certificate := certificate) (state := state)
                      (tags := candidateTags) (parent := candidate)
                      (child := left) (vertex := visited)
                      clearAtCandidate strict visitedBound visitedRank
                rcases induction
                    (certificate.formulaComplexityAt left) strictRank
                    (Nat.le_trans (Nat.le_of_lt strictRank)
                      rankAtMostStart)
                    left remainingFuel
                    (setTag candidateTags candidate) rfl leftBound
                    recursiveClear remainingEnough with
                  ⟨result, recursiveEquation⟩
                unfold nextAxiomWithFuel?
                simp only [dif_pos currentClear.1, dif_pos currentReady]
                split
                · rename_i sourceInFunction lookupInFunction
                  have sameSingleton :
                      (some [sourceInFunction] :
                          Option (List SourceIncidence)) =
                        some [source] := by
                    exact lookupInFunction.symm.trans sourceLookup
                  have sameSource : sourceInFunction = source := by
                    simpa using sameSingleton
                  subst sourceInFunction
                  split <;> simp_all
                · simp_all
  exact
    general startRank (Nat.le_refl startRank) vertex fuel tags rfl
      vertexBound clear fuelEnough

/-- Initial/local totality corollary.  If every formula occurrence is still
untagged and unassigned, any in-bounds start succeeds with the exact
formula-rank budget.  This is sufficient for the initial Figure-7 `init`
search; it is not the later scheduler's `new`-call invariant. -/
theorem nextAxiomWithFuel?_exists_of_structural_carrierClear
    {certificate : Certificate} {state : UnificationState}
    {tags : Array Bool} {vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (abstractable : state.Abstractable certificate)
    (vertexBound : vertex < certificate.formulas.size)
    (carrierClear :
      ∀ {candidate : Vertex},
        candidate < certificate.formulas.size →
          tags[candidate]? = some false ∧
            state.assignedToken? candidate = none) :
    ∃ result,
      nextAxiomWithFuel? certificate state
          (sourceIndex certificate) (sourceIndex_sound certificate)
          (certificate.formulaComplexityAt vertex + 1)
          tags vertex =
        some result := by
  apply nextAxiomWithFuel?_exists_of_structural_clearThrough
    structural abstractable vertexBound
  · intro candidate candidateBound _candidateRank
    exact carrierClear candidateBound
  · omega

/-- Production wrapper with the formula carrier as the conservative recursive
search budget. -/
def nextAxiom? (certificate : Certificate)
    (state : UnificationState) (index : SourceIndex)
    (indexSound : SourceIndex.Sound certificate index)
    (tags : Array Bool) (vertex : Vertex) :
    Option
      (NextAxiomResult certificate state certificate.formulas.size tags) :=
  nextAxiomWithFuel? certificate state index indexSound
    certificate.formulas.size tags vertex

/-- A successful search returns one exact submitted axiom whose two endpoint
occurrences were unmarked in the input state. -/
theorem nextAxiomWithFuel?_sound
    {certificate : Certificate} {state : UnificationState}
    {index : SourceIndex} {fuel : Nat} {tags : Array Bool}
    {indexSound : SourceIndex.Sound certificate index}
    {vertex : Vertex}
    {result : NextAxiomResult certificate state fuel tags}
    (_equation :
      nextAxiomWithFuel? certificate state index indexSound fuel tags vertex =
        some result) :
    certificate.links[result.linkIndex]? =
        some (.axiom result.left result.right) ∧
      state.assignedToken? result.left = none ∧
      state.assignedToken? result.right = none ∧
      result.trace.length ≤ fuel := by
  refine
    ⟨result.exactLink, ?_, ?_, result.traceLength⟩
  · simp [UnificationState.assignedToken?, result.leftReady]
  · simp [UnificationState.assignedToken?, result.rightReady]

/-- A successful bounded search preserves the tag carrier and all input `true`
tags, never repeats a recursively visited vertex, and changes every trace
vertex and both returned axiom endpoints from input `false` to output `true`.

These guarantees are per call.  Successive-call disjointness below requires
threading the first call's output tag array into the second call. -/
theorem nextAxiomWithFuel?_tag_trace_invariants
    {certificate : Certificate} {state : UnificationState}
    {index : SourceIndex} {fuel : Nat} {tags : Array Bool}
    {indexSound : SourceIndex.Sound certificate index}
    {vertex : Vertex}
    {result : NextAxiomResult certificate state fuel tags}
    (_equation :
      nextAxiomWithFuel? certificate state index indexSound fuel tags vertex =
        some result) :
    result.tags.size = tags.size ∧
      (∀ {visited : Vertex},
        tags[visited]? = some true →
          result.tags[visited]? = some true) ∧
      result.trace.Nodup ∧
      (∀ {visited : Vertex}, visited ∈ result.trace →
        tags[visited]? = some false ∧
          result.tags[visited]? = some true) ∧
      (tags[result.left]? = some false ∧
        result.tags[result.left]? = some true) ∧
      (tags[result.right]? = some false ∧
        result.tags[result.right]? = some true) := by
  exact
    ⟨result.tagsSize, result.preservesTrue, result.traceNodup,
      result.traceTagged, result.leftTagged, result.rightTagged⟩

/-- Every touched vertex of a successful search changed from input `false` to
output `true`.  This includes the non-recursive partner endpoint. -/
theorem nextAxiomWithFuel?_touched_tagged
    {certificate : Certificate} {state : UnificationState}
    {index : SourceIndex} {fuel : Nat} {tags : Array Bool}
    {indexSound : SourceIndex.Sound certificate index}
    {vertex touched : Vertex}
    {result : NextAxiomResult certificate state fuel tags}
    (_equation :
      nextAxiomWithFuel? certificate state index indexSound fuel tags vertex =
        some result)
    (isTouched : result.Touched touched) :
    tags[touched]? = some false ∧
      result.tags[touched]? = some true := by
  rcases isTouched with inTrace | rfl | rfl
  · exact result.traceTagged inTrace
  · exact result.leftTagged
  · exact result.rightTagged

/-- A successful bounded search contains no unexplained true tag: every output
true tag was already true on input or was touched by this exact execution. -/
theorem nextAxiomWithFuel?_tagged_iff_input_or_touched
    {certificate : Certificate} {state : UnificationState}
    {index : SourceIndex} {fuel : Nat} {tags : Array Bool}
    {indexSound : SourceIndex.Sound certificate index}
    {start : Vertex}
    {result : NextAxiomResult certificate state fuel tags}
    (equation :
      nextAxiomWithFuel? certificate state index indexSound fuel tags start =
        some result)
    {vertex : Vertex} :
    result.tags[vertex]? = some true ↔
      tags[vertex]? = some true ∨ result.Touched vertex := by
  constructor
  · exact nextAxiomWithFuel?_true_origin equation
  · rintro (inputTrue | touched)
    · exact result.preservesTrue inputTrue
    · rcases touched with inTrace | sameLeft | sameRight
      · exact (result.traceTagged inTrace).2
      · subst vertex
        exact result.leftTagged.2
      · subst vertex
        exact result.rightTagged.2

/-- Production-wrapper form of
`nextAxiomWithFuel?_tagged_iff_input_or_touched`. -/
theorem nextAxiom?_tagged_iff_input_or_touched
    {certificate : Certificate} {state : UnificationState}
    {index : SourceIndex} {tags : Array Bool}
    {indexSound : SourceIndex.Sound certificate index}
    {start : Vertex}
    {result :
      NextAxiomResult certificate state certificate.formulas.size tags}
    (equation :
      nextAxiom? certificate state index indexSound tags start =
        some result)
    {vertex : Vertex} :
    result.tags[vertex]? = some true ↔
      tags[vertex]? = some true ∨ result.Touched vertex := by
  exact nextAxiomWithFuel?_tagged_iff_input_or_touched (by
    simpa [nextAxiom?] using equation)

/-- Two successful calls, including calls across different marking states,
have disjoint touched sets when, and only as claimed here, the first call's
output tags are threaded into the second call. -/
theorem nextAxiomWithFuel?_threaded_touched_disjoint
    {certificate : Certificate}
    {firstState secondState : UnificationState}
    {index : SourceIndex} {firstFuel secondFuel : Nat}
    {tags : Array Bool}
    {indexSound : SourceIndex.Sound certificate index}
    {firstVertex secondVertex : Vertex}
    {first :
      NextAxiomResult certificate firstState firstFuel tags}
    (firstEquation :
      nextAxiomWithFuel? certificate firstState index indexSound
          firstFuel tags firstVertex = some first)
    {second :
      NextAxiomResult certificate secondState secondFuel first.tags}
    (secondEquation :
      nextAxiomWithFuel? certificate secondState index indexSound
          secondFuel first.tags secondVertex = some second) :
    ∀ {touched : Vertex},
      first.Touched touched → second.Touched touched → False := by
  intro touched firstTouched secondTouched
  have firstTrue :=
    (nextAxiomWithFuel?_touched_tagged
      firstEquation firstTouched).2
  have secondFalse :=
    (nextAxiomWithFuel?_touched_tagged
      secondEquation secondTouched).1
  rw [firstTrue] at secondFalse
  contradiction

/-- The token-semantic result of dynamically starting the axiom found by
`NEXTAXIOM`.  Parsed-component scheduling is intentionally left to the later
`σ`/ready/waiting layer. -/
structure DynamicStartResult (certificate : Certificate)
    (before : UnificationState) (fuel : Nat)
    (inputTags : Array Bool) where
  search : NextAxiomResult certificate before fuel inputTags
  after : UnificationState
  after_eq :
    after = before.startMarking search.left search.right
  deriving Repr

/-- Search for one new axiom and apply exactly the Figure-5 token marking
update. -/
def dynamicStartWithFuel? (certificate : Certificate)
    (before : UnificationState) (index : SourceIndex)
    (indexSound : SourceIndex.Sound certificate index)
    (fuel : Nat) (tags : Array Bool) (vertex : Vertex) :
    Option (DynamicStartResult certificate before fuel tags) :=
  (nextAxiomWithFuel? certificate before index indexSound
      fuel tags vertex).map
    fun search =>
      { search
        after := before.startMarking search.left search.right
        after_eq := rfl }

/-- A successful dynamic start after arbitrary prior ordered unions refines
one independent Figure-5 `start` transition. -/
theorem DynamicStartResult.refinesStart
    {certificate : Certificate} {before : UnificationState}
    {fuel : Nat} {inputTags : Array Bool}
    (result : DynamicStartResult certificate before fuel inputTags)
    (abstractable : before.Abstractable certificate)
    (ordered : before.OrderedParents) :
    ∃ afterAbstractable : result.after.Abstractable certificate,
      UnificationStep certificate
        (before.toMarking certificate abstractable)
        (result.after.toMarking certificate afterAbstractable) := by
  have leftBound : result.search.left < certificate.formulas.size := by
    have inMarks :
        result.search.left < before.marks.size :=
      (Array.getElem?_eq_some_iff.mp result.search.leftReady).1
    simpa [abstractable.markArraySize] using inMarks
  have rightBound : result.search.right < certificate.formulas.size := by
    have inMarks :
        result.search.right < before.marks.size :=
      (Array.getElem?_eq_some_iff.mp result.search.rightReady).1
    simpa [abstractable.markArraySize] using inMarks
  have leftUnmarked :
      before.assignedToken? result.search.left = none := by
    simp [UnificationState.assignedToken?,
      result.search.leftReady]
  have rightUnmarked :
      before.assignedToken? result.search.right = none := by
    simp [UnificationState.assignedToken?,
      result.search.rightReady]
  have linkMembership :
      Link.axiom result.search.left result.search.right ∈
        certificate.links :=
    List.mem_of_getElem? result.search.exactLink
  let markedAbstractable :=
    abstractable.startMarking_ordered ordered leftBound rightBound
  let afterAbstractable : result.after.Abstractable certificate := by
    simpa [result.after_eq] using markedAbstractable
  refine ⟨afterAbstractable, ?_⟩
  have step := before.startMarking_startStep_ordered
      abstractable ordered linkMembership
      leftBound rightBound leftUnmarked rightUnmarked
  simpa [result.after_eq] using step

end SequentialUnification

end ProofNetIR
