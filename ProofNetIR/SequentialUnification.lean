import ProofNetIR.Unification

namespace ProofNetIR

/-!
# Sequential unification primitives

This module begins the separate Guerrini Figures 7--8 implementation.  It
deliberately stops before the `σ`/ready/waiting scheduler: the first slice is
the bounded, globally tagged `NEXTAXIOM` search and its dynamic Figure-5 start
step.

The search follows the stored left premise of a tensor or par producer.  At an
atom it returns the exact submitted axiom incidence.  A source-incidence table
is built once, so one search step does not rescan the submitted link list.
-/

namespace SequentialUnification

/-- One exact submitted link stored in the source-incidence table. -/
structure SourceIncidence where
  linkIndex : Nat
  link : Link
  deriving Repr, DecidableEq

/-- Per-occurrence source incidences.  `nextAxiomWithFuel?` accepts only a
singleton bucket and rejects zero or multiple source entries.  The later
totality layer must separately expose the structural-to-singleton bridge. -/
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
    (state : UnificationState) (fuel : Nat) where
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
  deriving Repr

private def setTag (tags : Array Bool) (vertex : Vertex) :
    Array Bool :=
  tags.setIfInBounds vertex true

/-- Bounded, tagged `NEXTAXIOM`.

The search fails closed on out-of-domain, already tagged, already marked,
missing, or non-unique source buckets.  Compound producers deterministically
continue through their stored left premise. -/
def nextAxiomWithFuel? (certificate : Certificate)
    (state : UnificationState) (index : SourceIndex)
    (indexSound : SourceIndex.Sound certificate index) :
    (fuel : Nat) → Array Bool → Vertex →
      Option (NextAxiomResult certificate state fuel)
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
                          result with
                          trace := vertex :: result.trace
                          traceLength := by
                            simpa using
                              Nat.succ_le_succ result.traceLength
                        }
                  else none
          | _ => none
        else none
      else none

/-- Production wrapper with the formula carrier as the conservative recursive
search budget. -/
def nextAxiom? (certificate : Certificate)
    (state : UnificationState) (index : SourceIndex)
    (indexSound : SourceIndex.Sound certificate index)
    (tags : Array Bool) (vertex : Vertex) :
    Option
      (NextAxiomResult certificate state certificate.formulas.size) :=
  nextAxiomWithFuel? certificate state index indexSound
    certificate.formulas.size tags vertex

/-- A successful search returns one exact submitted axiom whose two endpoint
occurrences were unmarked in the input state. -/
theorem nextAxiomWithFuel?_sound
    {certificate : Certificate} {state : UnificationState}
    {index : SourceIndex} {fuel : Nat} {tags : Array Bool}
    {indexSound : SourceIndex.Sound certificate index}
    {vertex : Vertex}
    {result : NextAxiomResult certificate state fuel}
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

/-- The token-semantic result of dynamically starting the axiom found by
`NEXTAXIOM`.  Parsed-component scheduling is intentionally left to the later
`σ`/ready/waiting layer. -/
structure DynamicStartResult (certificate : Certificate)
    (before : UnificationState) (fuel : Nat) where
  search : NextAxiomResult certificate before fuel
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
    Option (DynamicStartResult certificate before fuel) :=
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
    {fuel : Nat} (result : DynamicStartResult certificate before fuel)
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
