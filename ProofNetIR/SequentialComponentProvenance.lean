import ProofNetIR.Unification
import ProofNetIR.SequentialSchedulerBridge

namespace ProofNetIR

/-!
# Occurrence-exact component provenance

This file is a proof-only provenance layer for the runtime
`UnificationComponent`.  It records the exact submitted link indices and the
formula vertices covered by a partial derivation.  In particular, formula
labels are never used as occurrence identities.
-/

namespace Certificate

/-- One premise selection keeps both exact views needed by the two existing
executables: the production picker selects the first matching vertex, while
the derivation picker records the occurrence position stored in the runtime
tree.  Keeping both equations avoids identifying repeated formula labels. -/
structure ExactOccurrencePick
    {source remaining : List Vertex}
    (vertex index : Nat) : Prop where
  first :
    FirstOccurrencePick source vertex index remaining
  positional :
    CutFreeDerivation.pick? source index =
      some (vertex, remaining)

namespace ExactOccurrencePick

/-- The stable public production-picker bridge supplies the positional half
of an exact occurrence selection. -/
theorem ofFirst
    {source remaining : List Vertex}
    {vertex index : Nat}
    (picked :
      FirstOccurrencePick source vertex index remaining) :
    ExactOccurrencePick vertex index
      (source := source) (remaining := remaining) := {
  first := picked
  positional := FirstOccurrencePick.positional picked }

end ExactOccurrencePick

/-- Exact occurrence-level provenance for a runtime derivation component.

`usedLinks` records submitted link positions, not link values.  `owned`
records every certificate formula vertex covered by the partial derivation:
both endpoints for an axiom and, recursively, every premise occurrence plus
the newly introduced connective conclusion. -/
inductive OccurrenceDerivation (certificate : Certificate) :
    CutFreeDerivation → List Vertex → List Nat → List Vertex → Prop where
  | axiom
      (linkIndex left right : Nat)
      (name : String) (positive : Bool)
      (linkLookup :
        certificate.links[linkIndex]? =
          some (.axiom left right))
      (leftFormula :
        certificate.formula? left =
          some (.atom name positive)) :
      OccurrenceDerivation certificate
        (.axiom name positive)
        [left, right] [linkIndex] [left, right]
  | par
      {premise : CutFreeDerivation}
      {frontier : List Vertex}
      {usedLinks owned : List Nat}
      (premiseWitness :
        OccurrenceDerivation certificate premise frontier
          usedLinks owned)
      (linkIndex left right conclusion leftFocus rightFocus : Nat)
      (afterLeft context : List Vertex)
      (linkLookup :
        certificate.links[linkIndex]? =
          some (.par left right conclusion))
      (leftPick :
        ExactOccurrencePick left leftFocus
          (source := frontier) (remaining := afterLeft))
      (rightPick :
        ExactOccurrencePick right rightFocus
          (source := afterLeft) (remaining := context)) :
      OccurrenceDerivation certificate
        (.par leftFocus rightFocus premise)
        (context ++ [conclusion])
        (linkIndex :: usedLinks)
        (conclusion :: owned)
  | tensor
      {leftTree rightTree : CutFreeDerivation}
      {leftFrontier rightFrontier : List Vertex}
      {leftUsed rightUsed leftOwned rightOwned : List Nat}
      (leftWitness :
        OccurrenceDerivation certificate leftTree leftFrontier
          leftUsed leftOwned)
      (rightWitness :
        OccurrenceDerivation certificate rightTree rightFrontier
          rightUsed rightOwned)
      (linkIndex left right conclusion leftFocus rightFocus : Nat)
      (leftContext rightContext : List Vertex)
      (linkLookup :
        certificate.links[linkIndex]? =
          some (.tensor left right conclusion))
      (leftPick :
        ExactOccurrencePick left leftFocus
          (source := leftFrontier) (remaining := leftContext))
      (rightPick :
        ExactOccurrencePick right rightFocus
          (source := rightFrontier) (remaining := rightContext)) :
      OccurrenceDerivation certificate
        (.tensor leftFocus rightFocus leftTree rightTree)
        (conclusion :: (leftContext ++ rightContext))
        (linkIndex :: (leftUsed ++ rightUsed))
        (conclusion :: (leftOwned ++ rightOwned))
  | exchange
      {premise : CutFreeDerivation}
      {frontier usedLinks owned : List Nat}
      (premiseWitness :
        OccurrenceDerivation certificate premise frontier
          usedLinks owned)
      (order : List Nat) (reordered : List Vertex)
      (reorderEquation :
        CutFreeDerivation.reorder? frontier order =
          some reordered) :
      OccurrenceDerivation certificate
        (.exchange order premise) reordered usedLinks owned

/-- A live component has one occurrence-exact derivation and locally linear
link/vertex accounting.  This is a proposition only; it adds no runtime data
to `UnificationComponent`. -/
structure ComponentOccurrenceWitness
    (certificate : Certificate) (component : UnificationComponent)
    (usedLinks owned : List Nat) : Prop where
  derivation :
    OccurrenceDerivation certificate component.tree component.frontier
      usedLinks owned
  usedLinks_nodup : usedLinks.Nodup
  owned_nodup : owned.Nodup

/-- Every occurrence owned by one live raw component slot is accounted for
at that exact slot.  A marked occurrence's raw age must resolve to the slot;
an unmarked occurrence must still be exposed on the same component frontier.
-/
def OwnedOccurrenceAccounted
    (state : UnificationState) (index : Nat)
    (component : UnificationComponent) (owned : List Vertex) : Prop :=
  ∀ vertex ∈ owned,
    (∃ rawAge,
      state.marks[vertex]? = some (some rawAge) ∧
        state.representative rawAge = index) ∨
      (state.marks[vertex]? = some none ∧
        vertex ∈ component.frontier)

/-- Conversely, every concrete raw mark belongs to an occurrence owned by
the live component stored at its exact current representative slot. -/
def MarkedOccurrencesOwned
    (state : UnificationState) (ownedAt : Nat → List Vertex) : Prop :=
  ∀ {vertex rawAge},
    state.marks[vertex]? = some (some rawAge) →
      ∃ index component,
        state.representative rawAge = index ∧
          state.components[index]? = some (some component) ∧
          vertex ∈ ownedAt index

/-- Proof-only forest accounting for all live component slots.

Each live slot receives exact local provenance, and distinct live slots own
disjoint submitted links and formula vertices.  Ownership is exact in both
directions: each owned vertex is either unmarked on that same frontier or
marked into that slot's representative class, and every concrete raw mark is
owned by the component at its representative.  This predicate is independent
of the older executable `Produced` relation. -/
def ComponentForestProvenance
    (certificate : Certificate) (state : UnificationState) : Prop :=
  ∃ usedAt ownedAt : Nat → List Nat,
    (∀ {index : Nat} {component : UnificationComponent},
      state.components[index]? = some (some component) →
        ComponentOccurrenceWitness certificate component
            (usedAt index) (ownedAt index) ∧
          OwnedOccurrenceAccounted state index component
            (ownedAt index)) ∧
    (∀ {leftIndex rightIndex : Nat}
          {leftComponent rightComponent : UnificationComponent},
        state.components[leftIndex]? = some (some leftComponent) →
        state.components[rightIndex]? = some (some rightComponent) →
        leftIndex ≠ rightIndex →
          (∀ linkIndex ∈ usedAt leftIndex,
            linkIndex ∉ usedAt rightIndex) ∧
          ∀ vertex ∈ ownedAt leftIndex,
            vertex ∉ ownedAt rightIndex) ∧
    MarkedOccurrencesOwned state ownedAt

namespace OccurrenceDerivation

/-- Mapping formulas through an exact positional pick selects the formula at
that same occurrence and maps the exact remaining occurrence list. -/
private theorem pick_mapM
    (mapping : Vertex → Option Formula)
    {source remaining : List Vertex}
    {vertex index : Nat}
    {sequent : List Formula} {formula : Formula}
    (picked :
      CutFreeDerivation.pick? source index =
        some (vertex, remaining))
    (mapped : source.mapM mapping = some sequent)
    (formulaAt : mapping vertex = some formula) :
    ∃ remainingSequent,
      CutFreeDerivation.pick? sequent index =
        some (formula, remainingSequent) ∧
      remaining.mapM mapping = some remainingSequent := by
  induction source generalizing index remaining sequent with
  | nil =>
      simp [CutFreeDerivation.pick?] at picked
  | cons head tail induction =>
      cases index with
      | zero =>
          simp [CutFreeDerivation.pick?] at picked
          rcases picked with ⟨rfl, rfl⟩
          cases tailMapped : tail.mapM mapping with
          | none =>
              simp [formulaAt, tailMapped] at mapped
          | some tailSequent =>
              simp [formulaAt, tailMapped] at mapped
              subst sequent
              exact ⟨tailSequent, rfl, rfl⟩
      | succ prior =>
          simp only [CutFreeDerivation.pick?] at picked
          cases tailPick :
              CutFreeDerivation.pick? tail prior with
          | none =>
              simp [tailPick] at picked
          | some result =>
              rcases result with ⟨selected, tailRemaining⟩
              simp [tailPick] at picked
              rcases picked with ⟨rfl, rfl⟩
              cases headMapped : mapping head with
              | none =>
                  simp [headMapped] at mapped
              | some headFormula =>
                  simp [headMapped] at mapped
                  cases tailMapped : tail.mapM mapping with
                  | none =>
                      simp [tailMapped] at mapped
                  | some tailSequent =>
                      simp [tailMapped] at mapped
                      subst sequent
                      rcases induction tailPick tailMapped with
                        ⟨remainingSequent, selectedPick, restMapped⟩
                      exact ⟨headFormula :: remainingSequent, by
                        simp [CutFreeDerivation.pick?, selectedPick],
                        by simp [headMapped, restMapped]⟩

private theorem mapM_eq_some_map_getD
    (mapping : Vertex → Option Formula)
    (fallback : Formula)
    {values : List Vertex} {mapped : List Formula}
    (equation : values.mapM mapping = some mapped) :
    values.map (fun vertex => (mapping vertex).getD fallback) =
      mapped := by
  induction values generalizing mapped with
  | nil =>
      simp at equation
      subst mapped
      rfl
  | cons head tail induction =>
      cases headEquation : mapping head with
      | none =>
          simp [headEquation] at equation
      | some headFormula =>
          cases tailEquation : tail.mapM mapping with
          | none =>
              simp [headEquation, tailEquation] at equation
          | some tailFormulas =>
              simp [headEquation, tailEquation] at equation
              subst mapped
              simp [headEquation, induction tailEquation]

private theorem mapM_defined_of_mem
    (mapping : Vertex → Option Formula)
    {source : List Vertex} {mapped : List Formula}
    {vertex : Vertex}
    (sourceMapped : source.mapM mapping = some mapped)
    (membership : vertex ∈ source) :
    ∃ formula, mapping vertex = some formula := by
  induction source generalizing mapped with
    | nil =>
        simp at membership
    | cons head tail induction =>
        cases headEquation : mapping head with
        | none =>
            simp [headEquation] at sourceMapped
        | some headFormula =>
            cases tailEquation : tail.mapM mapping with
            | none =>
                simp [headEquation, tailEquation] at sourceMapped
            | some tailFormulas =>
                simp [headEquation, tailEquation] at sourceMapped
                by_cases same : head = vertex
                · subst head
                  exact ⟨headFormula, headEquation⟩
                · have tailMembership : vertex ∈ tail := by
                    simp only [List.mem_cons] at membership
                    rcases membership with headEqual | inTail
                    · exact False.elim (same headEqual.symm)
                    · exact inTail
                  exact induction tailEquation tailMembership

private theorem mapM_eq_some_map_of_pointwise
    (mapping : Vertex → Option Formula)
    (fallback : Formula)
    (values : List Vertex)
    (defined :
      ∀ vertex ∈ values,
        mapping vertex =
          some ((mapping vertex).getD fallback)) :
    values.mapM mapping =
      some (values.map fun vertex =>
        (mapping vertex).getD fallback) := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      have headDefined := defined head (by simp)
      have tailDefined :
          ∀ vertex ∈ tail,
            mapping vertex =
              some ((mapping vertex).getD fallback) := by
        intro vertex membership
        exact defined vertex (by simp [membership])
      rw [List.mapM_cons, headDefined, induction tailDefined]
      rfl

private theorem mapM_getD_of_perm
    (mapping : Vertex → Option Formula)
    (fallback : Formula)
    {source target : List Vertex} {mapped : List Formula}
    (sourceMapped : source.mapM mapping = some mapped)
    (permutation : source.Perm target) :
    target.mapM mapping =
      some (target.map fun vertex =>
        (mapping vertex).getD fallback) := by
  have defined :
      ∀ vertex ∈ target,
        mapping vertex =
          some ((mapping vertex).getD fallback) := by
    intro vertex targetMembership
    have sourceMembership :
        vertex ∈ source :=
      permutation.mem_iff.mpr targetMembership
    rcases mapM_defined_of_mem mapping sourceMapped sourceMembership with
      ⟨formula, formulaAt⟩
    simp [formulaAt]
  exact mapM_eq_some_map_of_pointwise mapping fallback target defined

/-- Exact occurrence reordering commutes with successful formula lookup,
using the same index order even when formula labels repeat. -/
private theorem reorder_mapM
    (certificate : Certificate)
    {source target : List Vertex}
    {sourceFormulas : List Formula} {order : List Nat}
    (sourceMapped :
      source.mapM certificate.formula? = some sourceFormulas)
    (reordered :
      CutFreeDerivation.reorder? source order = some target) :
    ∃ targetFormulas,
      target.mapM certificate.formula? = some targetFormulas ∧
        CutFreeDerivation.reorder? sourceFormulas order =
          some targetFormulas := by
  let fallback : Formula := .atom "" false
  let label := fun vertex =>
    (certificate.formula? vertex).getD fallback
  have sourceLabels :
      source.map label = sourceFormulas :=
    mapM_eq_some_map_getD certificate.formula? fallback sourceMapped
  have targetMapped :
      target.mapM certificate.formula? =
        some (target.map label) :=
    mapM_getD_of_perm certificate.formula? fallback sourceMapped
      (CutFreeDerivation.reorder?_perm reordered)
  have formulaReorder :
      CutFreeDerivation.reorder? (source.map label) order =
        some (target.map label) :=
    CutFreeDerivation.reorder?_map_of_eq_some label reordered
  exact ⟨target.map label, targetMapped, by
    rw [sourceLabels] at formulaReorder
    exact formulaReorder⟩

/-- Every recorded link position is an exact submitted-list lookup. -/
theorem usedLink_lookup
    {certificate : Certificate}
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned)
    {linkIndex : Nat} (membership : linkIndex ∈ usedLinks) :
    ∃ link, certificate.links[linkIndex]? = some link := by
  induction witness with
  | «axiom» submittedIndex left right name positive linkLookup leftFormula =>
      simp only [List.mem_singleton] at membership
      subst linkIndex
      exact ⟨.axiom left right, linkLookup⟩
  | par premiseWitness submittedIndex left right conclusion
      leftFocus rightFocus afterLeft context linkLookup leftPick rightPick
      induction =>
      simp only [List.mem_cons] at membership
      rcases membership with rfl | oldMembership
      · exact ⟨.par left right conclusion, linkLookup⟩
      · exact induction oldMembership
  | tensor leftWitness rightWitness submittedIndex left right conclusion
      leftFocus rightFocus leftContext rightContext linkLookup
      leftPick rightPick leftInduction rightInduction =>
      simp only [List.mem_cons, List.mem_append] at membership
      rcases membership with rfl | leftMembership | rightMembership
      · exact ⟨.tensor left right conclusion, linkLookup⟩
      · exact leftInduction leftMembership
      · exact rightInduction rightMembership
  | exchange premiseWitness order reordered reorderEquation induction =>
      exact induction membership

/-- Recorded submitted positions are in bounds in the exact input link list. -/
theorem usedLinkIndex_lt
    {certificate : Certificate}
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned)
    {linkIndex : Nat} (membership : linkIndex ∈ usedLinks) :
    linkIndex < certificate.links.length := by
  rcases witness.usedLink_lookup membership with ⟨link, lookup⟩
  exact (List.getElem?_eq_some_iff.mp lookup).1

/-- The conclusion of every recorded submitted connective belongs to the
component's exact owned-occurrence list. -/
theorem usedConnectiveConclusion_owned
    {certificate : Certificate}
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned)
    {linkIndex left right conclusion : Nat}
    (membership : linkIndex ∈ usedLinks)
    (submitted :
      certificate.links[linkIndex]? =
          some (.tensor left right conclusion) ∨
        certificate.links[linkIndex]? =
          some (.par left right conclusion)) :
    conclusion ∈ owned := by
  induction witness generalizing linkIndex left right conclusion with
  | «axiom» submittedIndex axiomLeft axiomRight name positive
      linkLookup leftFormula =>
      simp only [List.mem_singleton] at membership
      subst linkIndex
      rw [linkLookup] at submitted
      simp at submitted
  | par premiseWitness submittedIndex parLeft parRight parConclusion
      leftFocus rightFocus afterLeft context linkLookup leftPick rightPick
      induction =>
      simp only [List.mem_cons] at membership ⊢
      rcases membership with rfl | oldMembership
      · rw [linkLookup] at submitted
        rcases submitted with tensorLookup | parLookup
        · simp at tensorLookup
        · simp at parLookup
          exact .inl parLookup.2.2.symm
      · exact .inr (induction oldMembership submitted)
  | tensor leftWitness rightWitness submittedIndex tensorLeft tensorRight
      tensorConclusion leftFocus rightFocus leftContext rightContext
      linkLookup leftPick rightPick leftInduction rightInduction =>
      simp only [List.mem_cons, List.mem_append] at membership ⊢
      rcases membership with rfl | leftMembership | rightMembership
      · rw [linkLookup] at submitted
        rcases submitted with tensorLookup | parLookup
        · simp at tensorLookup
          exact .inl tensorLookup.2.2.symm
        · simp at parLookup
      · exact .inr (.inl
          (leftInduction leftMembership submitted))
      · exact .inr (.inr
          (rightInduction rightMembership submitted))
  | exchange premiseWitness order reordered reorderEquation induction =>
      exact induction membership submitted

/-- Every exposed frontier occurrence is owned by the same component. -/
theorem frontier_subset_owned
    {certificate : Certificate}
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned) :
    ∀ vertex ∈ frontier, vertex ∈ owned := by
  induction witness with
  | «axiom» submittedIndex left right name positive linkLookup leftFormula =>
      simp
  | par premiseWitness submittedIndex left right conclusion
      leftFocus rightFocus afterLeft context linkLookup leftPick rightPick
      induction =>
      intro vertex membership
      rw [List.mem_append] at membership
      rcases membership with contextMembership | conclusionMembership
      · have inAfterLeft :
            vertex ∈ afterLeft :=
          (CutFreeDerivation.pick?_perm
            rightPick.positional).mem_iff.mpr (by
              simp [contextMembership])
        have inFrontier :
            vertex ∈ _ :=
          (CutFreeDerivation.pick?_perm
            leftPick.positional).mem_iff.mpr (by
              simp [inAfterLeft])
        simp [induction vertex inFrontier]
      · have same : vertex = conclusion := by
          simpa using conclusionMembership
        subst vertex
        simp
  | tensor leftWitness rightWitness submittedIndex left right conclusion
      leftFocus rightFocus leftContext rightContext linkLookup
      leftPick rightPick leftInduction rightInduction =>
      intro vertex membership
      simp only [List.mem_cons, List.mem_append] at membership ⊢
      rcases membership with rfl | leftContextMembership |
          rightContextMembership
      · exact .inl rfl
      · have inLeft :
            vertex ∈ _ :=
          (CutFreeDerivation.pick?_perm
            leftPick.positional).mem_iff.mpr (by
              simp [leftContextMembership])
        exact .inr (.inl (leftInduction vertex inLeft))
      · have inRight :
            vertex ∈ _ :=
          (CutFreeDerivation.pick?_perm
            rightPick.positional).mem_iff.mpr (by
              simp [rightContextMembership])
        exact .inr (.inr (rightInduction vertex inRight))
  | exchange premiseWitness order reordered reorderEquation induction =>
      intro vertex membership
      have oldMembership :
          vertex ∈ _ :=
        (CutFreeDerivation.reorder?_perm
          reorderEquation).mem_iff.mpr membership
      exact induction vertex oldMembership

/-- Under certificate structural well-formedness, every owned formula
occurrence is an in-bounds input vertex. -/
theorem owned_inBounds
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned) :
    ∀ vertex ∈ owned, vertex < certificate.formulas.size := by
  induction witness with
  | «axiom» linkIndex left right name positive linkLookup leftFormula =>
      have wellFormed :
          certificate.LinkWellFormed (.axiom left right) :=
        structural.2.2.2.2.1 _ (List.mem_of_getElem? linkLookup)
      intro vertex membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl | rfl
      · exact wellFormed.2.1
      · exact wellFormed.2.2.1
  | par premiseWitness linkIndex left right conclusion leftFocus
      rightFocus afterLeft context linkLookup leftPick rightPick induction =>
      have wellFormed :
          certificate.LinkWellFormed (.par left right conclusion) :=
        structural.2.2.2.2.1 _ (List.mem_of_getElem? linkLookup)
      intro vertex membership
      simp only [List.mem_cons] at membership
      rcases membership with rfl | oldMembership
      · exact wellFormed.2.2.2.2.2.1
      · exact induction vertex oldMembership
  | tensor leftWitness rightWitness linkIndex left right conclusion
      leftFocus rightFocus leftContext rightContext linkLookup
      leftPick rightPick leftInduction rightInduction =>
      have wellFormed :
          certificate.LinkWellFormed (.tensor left right conclusion) :=
        structural.2.2.2.2.1 _ (List.mem_of_getElem? linkLookup)
      intro vertex membership
      simp only [List.mem_cons, List.mem_append] at membership
      rcases membership with rfl | leftMembership | rightMembership
      · exact wellFormed.2.2.2.2.2.1
      · exact leftInduction vertex leftMembership
      · exact rightInduction vertex rightMembership
  | exchange premiseWitness order reordered reorderEquation induction =>
      exact induction

/-- Occurrence provenance implies the existing formula-consistency contract
without ever equating vertices merely because their formula labels agree. -/
theorem formulaConsistent
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned) :
    ({ tree := tree, frontier := frontier } :
      UnificationComponent).FormulaConsistent certificate := by
  induction witness with
  | «axiom» linkIndex left right name positive linkLookup leftFormula =>
      have wellFormed :
          certificate.LinkWellFormed (.axiom left right) :=
        structural.2.2.2.2.1 _ (List.mem_of_getElem? linkLookup)
      rcases wellFormed with
        ⟨different, leftBound, rightBound, typing⟩
      rw [leftFormula] at typing
      cases rightLookup : certificate.formula? right with
      | none =>
          simp [rightLookup] at typing
      | some rightFormula =>
          simp [rightLookup] at typing
          subst rightFormula
          exact ⟨[.atom name positive,
            (Formula.atom name positive).dual], rfl, by
              simp [leftFormula, rightLookup]⟩
  | par premiseWitness linkIndex left right conclusion leftFocus
      rightFocus afterLeft context linkLookup leftPick rightPick induction =>
      rcases induction with ⟨sequent, inferred, mapped⟩
      have wellFormed :
          certificate.LinkWellFormed (.par left right conclusion) :=
        structural.2.2.2.2.1 _ (List.mem_of_getElem? linkLookup)
      rcases wellFormed.par_formulaData with
        ⟨leftFormula, rightFormula, leftFormulaAt,
          rightFormulaAt, conclusionFormula⟩
      rcases pick_mapM certificate.formula?
          leftPick.positional mapped leftFormulaAt with
        ⟨afterLeftSequent, leftSelected, afterLeftMapped⟩
      rcases pick_mapM certificate.formula?
          rightPick.positional afterLeftMapped rightFormulaAt with
        ⟨contextSequent, rightSelected, contextMapped⟩
      refine ⟨contextSequent ++ [.par leftFormula rightFormula], ?_, ?_⟩
      · simp [CutFreeDerivation.infer?, inferred,
          leftSelected, rightSelected]
      · simp [contextMapped, conclusionFormula]
  | tensor leftWitness rightWitness linkIndex left right conclusion
      leftFocus rightFocus leftContext rightContext linkLookup
      leftPick rightPick leftInduction rightInduction =>
      rcases leftInduction with
        ⟨leftSequent, leftInferred, leftMapped⟩
      rcases rightInduction with
        ⟨rightSequent, rightInferred, rightMapped⟩
      have wellFormed :
          certificate.LinkWellFormed (.tensor left right conclusion) :=
        structural.2.2.2.2.1 _ (List.mem_of_getElem? linkLookup)
      rcases wellFormed.tensor_formulaData with
        ⟨leftFormula, rightFormula, leftFormulaAt,
          rightFormulaAt, conclusionFormula⟩
      rcases pick_mapM certificate.formula?
          leftPick.positional leftMapped leftFormulaAt with
        ⟨leftContextSequent, leftSelected, leftContextMapped⟩
      rcases pick_mapM certificate.formula?
          rightPick.positional rightMapped rightFormulaAt with
        ⟨rightContextSequent, rightSelected, rightContextMapped⟩
      refine ⟨.tensor leftFormula rightFormula ::
        (leftContextSequent ++ rightContextSequent), ?_, ?_⟩
      · simp [CutFreeDerivation.infer?, leftInferred, rightInferred,
          leftSelected, rightSelected]
      · simp [conclusionFormula, leftContextMapped, rightContextMapped]
  | exchange premiseWitness order reordered reorderEquation induction =>
      rcases induction with ⟨sequent, inferred, mapped⟩
      rcases reorder_mapM certificate mapped reorderEquation with
        ⟨reorderedSequent, reorderedMapped, formulaReorder⟩
      exact ⟨reorderedSequent, by
        simp [CutFreeDerivation.infer?, inferred, formulaReorder],
        reorderedMapped⟩

/-- A local delayed-par queue extends occurrence provenance once the caller
supplies the exact submitted link position and lookup, the only link-identity
facts absent from `QueueParStep`. -/
theorem ofQueueParStep
    {certificate : Certificate}
    {before after : UnificationState}
    {left right conclusion : Vertex}
    (step : QueueParStep before after left right conclusion)
    {usedLinks owned : List Nat}
    (componentWitness :
      OccurrenceDerivation certificate step.component.tree
        step.component.frontier usedLinks owned)
    (linkIndex : Nat)
    (linkLookup :
      certificate.links[linkIndex]? =
        some (.par left right conclusion)) :
    OccurrenceDerivation certificate
      (.par step.leftFocus step.rightFocus step.component.tree)
      (step.context ++ [conclusion])
      (linkIndex :: usedLinks) (conclusion :: owned) :=
  .par componentWitness linkIndex left right conclusion
    step.leftFocus step.rightFocus step.afterLeft step.context
    linkLookup
    (ExactOccurrencePick.ofFirst step.left_pick)
    (ExactOccurrencePick.ofFirst step.right_pick)

/-- A local delayed-tensor queue has the analogous strongest sound extension:
the queue witness supplies exact component/picker data, while the caller must
supply only the submitted tensor index and lookup. -/
theorem ofQueueTensorStep
    {certificate : Certificate}
    {before after : UnificationState}
    {left right conclusion : Vertex}
    (step : QueueTensorStep before after left right conclusion)
    {leftUsed rightUsed leftOwned rightOwned : List Nat}
    (leftWitness :
      OccurrenceDerivation certificate step.leftComponent.tree
        step.leftComponent.frontier leftUsed leftOwned)
    (rightWitness :
      OccurrenceDerivation certificate step.rightComponent.tree
        step.rightComponent.frontier rightUsed rightOwned)
    (linkIndex : Nat)
    (linkLookup :
      certificate.links[linkIndex]? =
        some (.tensor left right conclusion)) :
    OccurrenceDerivation certificate
      (.tensor step.leftFocus step.rightFocus
        step.leftComponent.tree step.rightComponent.tree)
      (conclusion :: (step.leftContext ++ step.rightContext))
      (linkIndex :: (leftUsed ++ rightUsed))
      (conclusion :: (leftOwned ++ rightOwned)) :=
  .tensor leftWitness rightWitness linkIndex left right conclusion
    step.leftFocus step.rightFocus step.leftContext step.rightContext
    linkLookup
    (ExactOccurrencePick.ofFirst step.left_pick)
    (ExactOccurrencePick.ofFirst step.right_pick)

end OccurrenceDerivation

namespace ComponentOccurrenceWitness

/-- Exact locally linear witness for one submitted, well-formed axiom in its
stored endpoint orientation. -/
theorem axiom_of_submitted
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {linkIndex left right : Nat}
    {name : String} {positive : Bool}
    (linkLookup :
      certificate.links[linkIndex]? =
        some (.axiom left right))
    (leftFormula :
      certificate.formula? left =
        some (.atom name positive)) :
    ComponentOccurrenceWitness certificate
      { tree := .axiom name positive, frontier := [left, right] }
      [linkIndex] [left, right] := by
  have wellFormed :
      certificate.LinkWellFormed (.axiom left right) :=
    structural.2.2.2.2.1 _ (List.mem_of_getElem? linkLookup)
  exact {
    derivation :=
      .axiom linkIndex left right name positive linkLookup leftFormula
    usedLinks_nodup := by simp
    owned_nodup := by simp [wellFormed.1] }

end ComponentOccurrenceWitness

/-- Reserving a submitted axiom installs an exact occurrence-provenance
witness at the freshly appended component slot. -/
theorem reserveAxiomAt?_componentOccurrenceWitness
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {before after : UnificationState} {linkIndex : Nat}
    (equation :
      certificate.reserveAxiomAt? before linkIndex = some after) :
    ∃ left right name positive,
      certificate.links[linkIndex]? =
          some (.axiom left right) ∧
      after.components[before.components.size]? =
          some (some {
            tree := .axiom name positive
            frontier := [left, right] }) ∧
      ComponentOccurrenceWitness certificate
        { tree := .axiom name positive, frontier := [left, right] }
        [linkIndex] [left, right] := by
  rcases certificate.reserveAxiomAt?_exact equation with
    ⟨left, right, component, linkLookup, ready, componentLookup,
      frontier, marksEquation, parentsEquation, componentsEquation,
      counterEquation, firedEquation⟩
  rcases UnificationComponent.axiom?_success componentLookup with
    ⟨name, positive, leftFormula, componentEquation⟩
  subst component
  refine ⟨left, right, name, positive, linkLookup, ?_, ?_⟩
  · rw [componentsEquation]
    simp
  · exact ComponentOccurrenceWitness.axiom_of_submitted
      structural linkLookup leftFormula

/-- Equal formula labels do not let a different certificate vertex satisfy
an occurrence-position witness.  This is the local repeated-label rejection
gate used by later provenance-preservation proofs. -/
theorem ExactOccurrencePick.rejects_same_formula_alias
    {certificate : Certificate}
    {head alias : Vertex} {tail remaining : List Vertex}
    (different : head ≠ alias)
    (_sameFormula :
      certificate.formula? head = certificate.formula? alias)
    (picked :
      ExactOccurrencePick alias 0
        (source := head :: tail) (remaining := remaining)) :
    False := by
  have selected := picked.positional
  simp [CutFreeDerivation.pick?] at selected
  exact different selected.1

end Certificate
end ProofNetIR
