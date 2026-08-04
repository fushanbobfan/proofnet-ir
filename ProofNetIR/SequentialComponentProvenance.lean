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

/-- Exact occurrence picks preserve local frontier linearity.  Unlike the
value-level `frontier_subset_owned` lemma, this proof follows each positional
pick (and each exchange permutation), so duplicate frontier occurrences cannot
be hidden by ordinary membership. -/
theorem frontier_nodup_of_owned_nodup
    {certificate : Certificate}
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned)
    (ownedNodup : owned.Nodup) :
    frontier.Nodup := by
  induction witness with
  | «axiom» linkIndex left right name positive linkLookup leftFormula =>
      simpa using ownedNodup
  | par premiseWitness linkIndex left right conclusion leftFocus
      rightFocus afterLeft context linkLookup leftPick rightPick induction =>
      have ownedParts := List.nodup_cons.mp ownedNodup
      have premiseNodup := induction ownedParts.2
      have afterLeftWithPickNodup : (left :: afterLeft).Nodup :=
        (CutFreeDerivation.pick?_perm leftPick.positional).nodup_iff.mp
          premiseNodup
      have afterLeftNodup :=
        (List.nodup_cons.mp afterLeftWithPickNodup).2
      have contextWithPickNodup : (right :: context).Nodup :=
        (CutFreeDerivation.pick?_perm rightPick.positional).nodup_iff.mp
          afterLeftNodup
      apply List.nodup_append.mpr
      refine ⟨(List.nodup_cons.mp contextWithPickNodup).2, by simp, ?_⟩
      intro vertex contextMembership candidate candidateMembership
      have candidateEq : candidate = conclusion := by
        simpa using candidateMembership
      subst candidate
      intro same
      subst vertex
      apply ownedParts.1
      apply premiseWitness.frontier_subset_owned conclusion
      apply (CutFreeDerivation.pick?_perm leftPick.positional).mem_iff.mpr
      apply List.mem_cons_of_mem left
      apply (CutFreeDerivation.pick?_perm rightPick.positional).mem_iff.mpr
      exact List.mem_cons_of_mem right contextMembership
  | tensor leftWitness rightWitness linkIndex left right conclusion
      leftFocus rightFocus leftContext rightContext linkLookup
      leftPick rightPick leftInduction rightInduction =>
      have ownedParts := List.nodup_cons.mp ownedNodup
      have splitOwned := List.nodup_append.mp ownedParts.2
      have leftFrontierNodup := leftInduction splitOwned.1
      have rightFrontierNodup := rightInduction splitOwned.2.1
      have leftPickedNodup : (left :: leftContext).Nodup :=
        (CutFreeDerivation.pick?_perm leftPick.positional).nodup_iff.mp
          leftFrontierNodup
      have rightPickedNodup : (right :: rightContext).Nodup :=
        (CutFreeDerivation.pick?_perm rightPick.positional).nodup_iff.mp
          rightFrontierNodup
      have leftContextNodup := (List.nodup_cons.mp leftPickedNodup).2
      have rightContextNodup := (List.nodup_cons.mp rightPickedNodup).2
      apply List.nodup_cons.mpr
      constructor
      · intro conclusionMembership
        simp only [List.mem_append] at conclusionMembership
        rcases conclusionMembership with leftMembership | rightMembership
        · apply ownedParts.1
          exact List.mem_append_left _
            (leftWitness.frontier_subset_owned conclusion
              ((CutFreeDerivation.pick?_perm leftPick.positional).mem_iff.mpr
                (List.mem_cons_of_mem left leftMembership)))
        · apply ownedParts.1
          exact List.mem_append_right _
            (rightWitness.frontier_subset_owned conclusion
              ((CutFreeDerivation.pick?_perm rightPick.positional).mem_iff.mpr
                (List.mem_cons_of_mem right rightMembership)))
      · apply List.nodup_append.mpr
        refine ⟨leftContextNodup, rightContextNodup, ?_⟩
        intro leftVertex leftMembership rightVertex rightMembership same
        have leftOwnedMembership :=
          leftWitness.frontier_subset_owned leftVertex
            ((CutFreeDerivation.pick?_perm leftPick.positional).mem_iff.mpr
              (List.mem_cons_of_mem left leftMembership))
        have rightOwnedMembership :=
          rightWitness.frontier_subset_owned rightVertex
            ((CutFreeDerivation.pick?_perm rightPick.positional).mem_iff.mpr
              (List.mem_cons_of_mem right rightMembership))
        exact splitOwned.2.2 leftVertex leftOwnedMembership rightVertex
          rightOwnedMembership same
  | exchange premiseWitness order reordered reorderEquation induction =>
      exact (CutFreeDerivation.reorder?_perm reorderEquation).nodup_iff.mp
        (induction ownedNodup)

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

/-- Every submitted axiom used by an occurrence derivation owns both exact
endpoint occurrences.  This follows the submitted link index, never merely a
formula label. -/
theorem usedAxiomEndpoints_owned
    {certificate : Certificate}
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness : OccurrenceDerivation certificate tree frontier usedLinks owned)
    {linkIndex left right : Nat}
    (membership : linkIndex ∈ usedLinks)
    (submitted : certificate.links[linkIndex]? = some (.axiom left right)) :
    left ∈ owned ∧ right ∈ owned := by
  induction witness generalizing linkIndex left right with
  | «axiom» submittedIndex axiomLeft axiomRight name positive
      linkLookup leftFormula =>
      simp only [List.mem_singleton] at membership
      subst linkIndex
      have linkEquation :
          Link.axiom axiomLeft axiomRight = .axiom left right :=
        Option.some.inj (linkLookup.symm.trans submitted)
      injection linkEquation with leftEquation rightEquation
      subst left
      subst right
      simp
  | par premiseWitness submittedIndex parLeft parRight conclusion
      leftFocus rightFocus afterLeft context linkLookup leftPick rightPick
      induction =>
      simp only [List.mem_cons] at membership
      rcases membership with rfl | oldMembership
      · rw [linkLookup] at submitted
        simp at submitted
      · have oldOwned := induction oldMembership submitted
        exact ⟨List.mem_cons_of_mem _ oldOwned.1,
          List.mem_cons_of_mem _ oldOwned.2⟩
  | tensor leftWitness rightWitness submittedIndex tensorLeft tensorRight
      conclusion leftFocus rightFocus leftContext rightContext linkLookup
      leftPick rightPick leftInduction rightInduction =>
      simp only [List.mem_cons, List.mem_append] at membership
      rcases membership with rfl | leftMembership | rightMembership
      · rw [linkLookup] at submitted
        simp at submitted
      · have oldOwned := leftInduction leftMembership submitted
        exact ⟨
          List.mem_cons_of_mem _ (List.mem_append_left _ oldOwned.1),
          List.mem_cons_of_mem _ (List.mem_append_left _ oldOwned.2)⟩
      · have oldOwned := rightInduction rightMembership submitted
        exact ⟨
          List.mem_cons_of_mem _ (List.mem_append_right _ oldOwned.1),
          List.mem_cons_of_mem _ (List.mem_append_right _ oldOwned.2)⟩
  | exchange premiseWitness order reordered reorderEquation induction =>
      exact induction membership submitted

end OccurrenceDerivation

namespace ComponentOccurrenceWitness

/-- A locally linear occurrence witness has a duplicate-free exposed
frontier.  The proof uses the derivation's exact positional picks, rather than
merely the value-level inclusion of the frontier in `owned`. -/
theorem frontier_nodup
    {certificate : Certificate} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (witness :
      ComponentOccurrenceWitness certificate component usedLinks owned) :
    component.frontier.Nodup :=
  witness.derivation.frontier_nodup_of_owned_nodup witness.owned_nodup

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

/-- Merge two locally linear occurrence witnesses through one exact submitted
tensor queue.

The runtime survivor slot is deliberately absent from this statement: the
derivation follows the submitted left/right premise orientation retained by
`QueueTensorStep`, while a later forest theorem may store the resulting
component at either raw root.  Every separation hypothesis is occurrence- or
submitted-index-exact; formula labels play no role. -/
theorem ofQueueTensorStep
    {certificate : Certificate}
    {before after : UnificationState}
    {left right conclusion : Vertex}
    (step : QueueTensorStep before after left right conclusion)
    {leftUsed rightUsed : List Nat}
    {leftOwned rightOwned : List Vertex}
    (leftWitness :
      ComponentOccurrenceWitness certificate step.leftComponent
        leftUsed leftOwned)
    (rightWitness :
      ComponentOccurrenceWitness certificate step.rightComponent
        rightUsed rightOwned)
    (linkIndex : Nat)
    (linkLookup :
      certificate.links[linkIndex]? =
        some (.tensor left right conclusion))
    (linkFreshLeft : linkIndex ∉ leftUsed)
    (linkFreshRight : linkIndex ∉ rightUsed)
    (conclusionFreshLeft : conclusion ∉ leftOwned)
    (conclusionFreshRight : conclusion ∉ rightOwned)
    (usedDisjoint :
      ∀ candidate ∈ leftUsed, candidate ∉ rightUsed)
    (ownedDisjoint :
      ∀ vertex ∈ leftOwned, vertex ∉ rightOwned) :
    ComponentOccurrenceWitness certificate
      { tree :=
          .tensor step.leftFocus step.rightFocus
            step.leftComponent.tree step.rightComponent.tree
        frontier :=
          conclusion :: (step.leftContext ++ step.rightContext) }
      (linkIndex :: (leftUsed ++ rightUsed))
      (conclusion :: (leftOwned ++ rightOwned)) := by
  refine {
    derivation :=
      OccurrenceDerivation.ofQueueTensorStep step
        leftWitness.derivation rightWitness.derivation
        linkIndex linkLookup
    usedLinks_nodup := ?_
    owned_nodup := ?_ }
  · apply List.nodup_cons.mpr
    constructor
    · simpa [List.mem_append] using
        And.intro linkFreshLeft linkFreshRight
    · apply List.nodup_append.mpr
      refine ⟨leftWitness.usedLinks_nodup,
        rightWitness.usedLinks_nodup, ?_⟩
      intro leftLink leftMembership rightLink rightMembership same
      subst rightLink
      exact usedDisjoint leftLink leftMembership rightMembership
  · apply List.nodup_cons.mpr
    constructor
    · simpa [List.mem_append] using
        And.intro conclusionFreshLeft conclusionFreshRight
    · apply List.nodup_append.mpr
      refine ⟨leftWitness.owned_nodup,
        rightWitness.owned_nodup, ?_⟩
      intro leftVertex leftMembership rightVertex rightMembership same
      subst rightVertex
      exact ownedDisjoint leftVertex leftMembership rightMembership

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

namespace ComponentForestProvenance

private theorem flatMap_nodup_of_getElem?_local_disjoint
    {α β : Type} [DecidableEq β]
    (values : List α) (mapping : α → List β)
    (locallyNodup : ∀ {index : Nat} {value : α},
      values[index]? = some value →
      (mapping value).Nodup)
    (disjoint : ∀ {leftIndex rightIndex : Nat}
        {leftValue rightValue : α},
      values[leftIndex]? = some leftValue →
      values[rightIndex]? = some rightValue →
      leftIndex ≠ rightIndex →
      ∀ candidate ∈ mapping leftValue,
        candidate ∉ mapping rightValue) :
    (values.flatMap mapping).Nodup := by
  induction values with
  | nil => simp
  | cons head tail induction =>
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨locallyNodup (index := 0) (by simp), ?_, ?_⟩
      · apply induction
        · intro index value lookup
          apply locallyNodup (index := index + 1)
          simpa [Nat.add_comm] using lookup
        · intro leftIndex rightIndex leftValue rightValue
            leftLookup rightLookup different
          apply disjoint (leftIndex := leftIndex + 1)
            (rightIndex := rightIndex + 1)
          · simpa [Nat.add_comm] using leftLookup
          · simpa [Nat.add_comm] using rightLookup
          · intro same
            exact different (Nat.add_right_cancel same)
      · intro leftVertex leftMembership rightVertex rightMembership same
        subst rightVertex
        rcases List.mem_flatMap.mp rightMembership with
          ⟨rightValue, valueMembership, rightMembership⟩
        rcases List.mem_iff_getElem?.mp valueMembership with
          ⟨rightIndex, rightLookup⟩
        exact (disjoint (leftIndex := 0)
          (rightIndex := rightIndex + 1) (by simp)
          (by simpa [Nat.add_comm] using rightLookup)
          (Nat.zero_ne_add_one rightIndex) leftVertex leftMembership)
            rightMembership

/-- Occurrence-exact forest provenance already implies global duplicate
freedom of all live component frontiers.  The statement is written against the
component carrier directly so this upstream module does not import the
downstream scheduler definition `UnificationState.liveFrontierVertices`. -/
theorem liveFrontiers_nodup
    {certificate : Certificate} {state : UnificationState}
    (forest : certificate.ComponentForestProvenance state) :
    (state.components.toList.flatMap fun cell =>
      (cell.map UnificationComponent.frontier).getD []).Nodup := by
  rcases forest with ⟨usedAt, ownedAt, live, separated, covered⟩
  apply flatMap_nodup_of_getElem?_local_disjoint
  · intro index cell cellLookup
    cases cell with
    | none => simp
    | some component =>
        have componentLookup :
            state.components[index]? = some (some component) := by
          rw [← Array.getElem?_toList]
          exact cellLookup
        simpa using (live componentLookup).1.frontier_nodup
  · intro leftIndex rightIndex leftCell rightCell
      leftLookup rightLookup different
    cases leftCell with
    | none => simp
    | some leftComponent =>
        cases rightCell with
        | none => simp
        | some rightComponent =>
            have leftComponentLookup :
                state.components[leftIndex]? =
                  some (some leftComponent) := by
              rw [← Array.getElem?_toList]
              exact leftLookup
            have rightComponentLookup :
                state.components[rightIndex]? =
                  some (some rightComponent) := by
              rw [← Array.getElem?_toList]
              exact rightLookup
            have ownerSeparation :=
              (separated leftComponentLookup rightComponentLookup
                different).2
            intro vertex leftFrontier rightFrontier
            apply ownerSeparation vertex
              ((live leftComponentLookup).1.derivation.frontier_subset_owned
                vertex leftFrontier)
            exact (live rightComponentLookup).1.derivation.frontier_subset_owned
              vertex rightFrontier

/-- Marking one occurrence preserves the complete component forest when the
selected occurrence lies on the live frontier at the raw age's current
representative.  The successful update itself supplies raw-unmarkedness and
leaves both component and parent carriers unchanged. -/
theorem markReadyRaw?_of_representative_frontier
    {certificate : Certificate}
    {before after : UnificationState}
    {selected rawAge : Nat}
    (forest : certificate.ComponentForestProvenance before)
    (owner : ∃ component,
      before.components[before.representative rawAge]? =
          some (some component) ∧
        selected ∈ component.frontier)
    (equation : before.markReadyRaw? selected rawAge = .ok after) :
    certificate.ComponentForestProvenance after := by
  rcases forest with ⟨usedAt, ownedAt, live, disjoint, covered⟩
  rcases owner with ⟨ownerComponent, ownerLookup, ownerFrontier⟩
  rcases UnificationState.markReadyRaw?_exact equation with
    ⟨_selectedUnmarked, marksEq, parentsEq, componentsEq,
      _startedEq, _firedEq, selectedMarked⟩
  have ownerFacts := live ownerLookup
  have selectedOwned :
      selected ∈ ownedAt (before.representative rawAge) :=
    ownerFacts.1.derivation.frontier_subset_owned selected ownerFrontier
  have representativeEq : ∀ token,
      after.representative token = before.representative token := by
    intro token
    unfold UnificationState.representative
    rw [parentsEq]
  refine ⟨usedAt, ownedAt, ?_, ?_, ?_⟩
  · intro index component afterLookup
    have beforeLookup :
        before.components[index]? = some (some component) := by
      rw [componentsEq] at afterLookup
      exact afterLookup
    rcases live beforeLookup with ⟨witness, accounted⟩
    refine ⟨witness, ?_⟩
    intro candidate candidateOwned
    by_cases same : candidate = selected
    · subst candidate
      have indexEq : index = before.representative rawAge := by
        by_cases equal : index = before.representative rawAge
        · exact equal
        · exfalso
          have separation :=
            (disjoint beforeLookup ownerLookup equal).2
              selected candidateOwned
          exact separation selectedOwned
      apply Or.inl
      refine ⟨rawAge, selectedMarked, ?_⟩
      rw [representativeEq]
      exact indexEq.symm
    · have selectedNe : selected ≠ candidate := Ne.symm same
      rcases accounted candidate candidateOwned with
        ⟨oldRawAge, oldMarked, oldRepresentative⟩ |
          ⟨oldUnmarked, oldFrontier⟩
      · apply Or.inl
        refine ⟨oldRawAge, ?_, ?_⟩
        · rw [marksEq]
          simpa [Array.getElem?_setIfInBounds, selectedNe] using
            oldMarked
        · rw [representativeEq]
          exact oldRepresentative
      · apply Or.inr
        refine ⟨?_, oldFrontier⟩
        rw [marksEq]
        simpa [Array.getElem?_setIfInBounds, selectedNe] using
          oldUnmarked
  · intro leftIndex rightIndex leftComponent rightComponent
      leftLookup rightLookup different
    have leftBefore :
        before.components[leftIndex]? = some (some leftComponent) := by
      rw [componentsEq] at leftLookup
      exact leftLookup
    have rightBefore :
        before.components[rightIndex]? = some (some rightComponent) := by
      rw [componentsEq] at rightLookup
      exact rightLookup
    exact disjoint leftBefore rightBefore different
  · intro candidate candidateRawAge afterMarked
    by_cases same : candidate = selected
    · subst candidate
      have ageEq : candidateRawAge = rawAge := by
        rw [selectedMarked] at afterMarked
        simpa using afterMarked.symm
      subst candidateRawAge
      refine ⟨before.representative rawAge, ownerComponent, ?_, ?_,
        selectedOwned⟩
      · exact representativeEq rawAge
      · rw [componentsEq]
        exact ownerLookup
    · have selectedNe : selected ≠ candidate := Ne.symm same
      have beforeMarked :
          before.marks[candidate]? = some (some candidateRawAge) := by
        rw [marksEq] at afterMarked
        simpa [Array.getElem?_setIfInBounds, selectedNe] using
          afterMarked
      rcases covered beforeMarked with
        ⟨index, component, representative, componentLookup,
          candidateOwned⟩
      refine ⟨index, component, ?_, ?_, candidateOwned⟩
      · rw [representativeEq]
        exact representative
      · rw [componentsEq]
        exact componentLookup

/-- Root-form convenience wrapper for scheduler callers, whose active raw
age is already known to be the representative of its live component slot. -/
theorem markReadyRaw?_of_root_frontier
    {certificate : Certificate}
    {before after : UnificationState}
    {selected rawAge : Nat}
    (forest : certificate.ComponentForestProvenance before)
    (root : before.representative rawAge = rawAge)
    (owner : ∃ component,
      before.components[rawAge]? = some (some component) ∧
        selected ∈ component.frontier)
    (equation : before.markReadyRaw? selected rawAge = .ok after) :
    certificate.ComponentForestProvenance after := by
  apply forest.markReadyRaw?_of_representative_frontier
  · rcases owner with ⟨component, componentLookup, frontier⟩
    refine ⟨component, ?_, frontier⟩
    rw [root]
    exact componentLookup
  · exact equation

/-- Replacing one exact live component by a submitted delayed-par extension
preserves the complete occurrence-exact forest.

The caller supplies the exact active component slot and proves that the new
conclusion occurrence is absent from every old live owner.  This occurrence
freshness also forces the submitted `linkIndex` to be absent from every old
`usedAt` list: otherwise `usedConnectiveConclusion_owned` would put the same
exact conclusion in that old owner.  No formula-label equality is used.

The theorem updates only the active proof witnesses, from `usedAt`/`ownedAt`
to `linkIndex :: usedAt` and `conclusion :: ownedAt`; every other witness is
retained verbatim. -/
theorem queueParStep_of_active_fresh
    {certificate : Certificate}
    {before after : UnificationState}
    {left right conclusion : Vertex}
    (forest : certificate.ComponentForestProvenance before)
    (step : QueueParStep before after left right conclusion)
    (linkIndex : Nat)
    (linkLookup :
      certificate.links[linkIndex]? =
        some (.par left right conclusion))
    (activeLookup :
      before.components[step.outputToken]? =
        some (some step.component))
    (conclusionFresh :
      ∀ {index component owned},
        before.components[index]? = some (some component) →
        OwnedOccurrenceAccounted before index component owned →
        conclusion ∉ owned) :
    certificate.ComponentForestProvenance after := by
  rcases forest with ⟨usedAt, ownedAt, live, disjoint, covered⟩
  let nextComponent : UnificationComponent := {
    tree := .par step.leftFocus step.rightFocus step.component.tree
    frontier := step.context ++ [conclusion] }
  let newUsedAt : Nat → List Nat := fun index =>
    if index = step.outputToken then
      linkIndex :: usedAt index
    else
      usedAt index
  let newOwnedAt : Nat → List Vertex := fun index =>
    if index = step.outputToken then
      conclusion :: ownedAt index
    else
      ownedAt index
  have activeFacts := live activeLookup
  have activeConclusionFresh :
      conclusion ∉ ownedAt step.outputToken :=
    conclusionFresh activeLookup activeFacts.2
  have oldLinkFresh : ∀ {index component},
      before.components[index]? = some (some component) →
        linkIndex ∉ usedAt index := by
    intro index component componentLookup linkUsed
    have conclusionOwned : conclusion ∈ ownedAt index :=
      (live componentLookup).1.derivation.usedConnectiveConclusion_owned
        linkUsed (.inr linkLookup)
    exact (conclusionFresh componentLookup (live componentLookup).2)
      conclusionOwned
  have nextWitness :
      ComponentOccurrenceWitness certificate nextComponent
        (linkIndex :: usedAt step.outputToken)
        (conclusion :: ownedAt step.outputToken) := {
    derivation := by
      simpa [nextComponent] using
        OccurrenceDerivation.ofQueueParStep step
          activeFacts.1.derivation linkIndex linkLookup
    usedLinks_nodup :=
      List.nodup_cons.mpr ⟨oldLinkFresh activeLookup,
        activeFacts.1.usedLinks_nodup⟩
    owned_nodup :=
      List.nodup_cons.mpr ⟨activeConclusionFresh,
        activeFacts.1.owned_nodup⟩ }
  have outputBound : step.outputToken < before.components.size :=
    (Array.getElem?_eq_some_iff.mp activeLookup).1
  have afterComponents :
      after.components =
        before.components.setIfInBounds step.outputToken
          (some nextComponent) := by
    simpa [nextComponent] using
      congrArg (fun state : UnificationState => state.components)
        step.after_eq
  have afterMarks : after.marks = before.marks := by
    simpa using
      congrArg (fun state : UnificationState => state.marks)
        step.after_eq
  have afterParents : after.parents = before.parents := by
    simpa using
      congrArg (fun state : UnificationState => state.parents)
        step.after_eq
  have representativeUnchanged : ∀ token,
      after.representative token = before.representative token := by
    intro token
    unfold UnificationState.representative
    rw [afterParents]
  have forwardGuards :=
    UnificationState.forwardToken?_success step.token_guard
  have leftMarked : ∃ rawAge,
      before.marks[left]? = some (some rawAge) := by
    rcases before.tokenAt?_some_witness forwardGuards.2.1 with
      ⟨rawAge, assigned, _representative⟩
    exact ⟨rawAge, UnificationState.assignedToken?_some_raw assigned⟩
  have rightMarked : ∃ rawAge,
      before.marks[right]? = some (some rawAge) := by
    rcases before.tokenAt?_some_witness forwardGuards.2.2 with
      ⟨rawAge, assigned, _representative⟩
    exact ⟨rawAge, UnificationState.assignedToken?_some_raw assigned⟩
  refine ⟨newUsedAt, newOwnedAt, ?_, ?_, ?_⟩
  · intro index component afterLookup
    by_cases isActive : index = step.outputToken
    · subst index
      rw [afterComponents] at afterLookup
      simp [outputBound] at afterLookup
      subst component
      refine ⟨?_, ?_⟩
      · simpa [newUsedAt, newOwnedAt] using nextWitness
      · intro vertex vertexOwned
        simp only [newOwnedAt, if_pos, List.mem_cons] at vertexOwned
        rcases vertexOwned with rfl | oldOwned
        · apply Or.inr
          refine ⟨?_, ?_⟩
          · rw [afterMarks]
            exact forwardGuards.1
          · simp [nextComponent]
        · rcases activeFacts.2 vertex oldOwned with
            ⟨rawAge, marked, representative⟩ |
              ⟨unmarked, frontierMembership⟩
          · apply Or.inl
            refine ⟨rawAge, ?_, ?_⟩
            · rw [afterMarks]
              exact marked
            · rw [representativeUnchanged]
              exact representative
          · have vertexNeLeft : vertex ≠ left := by
              intro same
              subst vertex
              rcases leftMarked with ⟨rawAge, marked⟩
              rw [unmarked] at marked
              simp at marked
            have vertexNeRight : vertex ≠ right := by
              intro same
              subst vertex
              rcases rightMarked with ⟨rawAge, marked⟩
              rw [unmarked] at marked
              simp at marked
            have afterLeftMembership : vertex ∈ step.afterLeft := by
              have membership : vertex ∈ left :: step.afterLeft :=
                (CutFreeDerivation.pick?_perm
                  (FirstOccurrencePick.positional step.left_pick)).mem_iff.mp
                    frontierMembership
              simpa [vertexNeLeft] using membership
            have contextMembership : vertex ∈ step.context := by
              have membership : vertex ∈ right :: step.context :=
                (CutFreeDerivation.pick?_perm
                  (FirstOccurrencePick.positional step.right_pick)).mem_iff.mp
                    afterLeftMembership
              simpa [vertexNeRight] using membership
            apply Or.inr
            refine ⟨?_, ?_⟩
            · rw [afterMarks]
              exact unmarked
            · simp [nextComponent, contextMembership]
    · have oldLookup :
          before.components[index]? = some (some component) := by
        rw [afterComponents] at afterLookup
        simpa [Array.getElem?_setIfInBounds, Ne.symm isActive] using
          afterLookup
      rcases live oldLookup with ⟨oldWitness, oldAccounted⟩
      refine ⟨?_, ?_⟩
      · simpa [newUsedAt, newOwnedAt, isActive] using oldWitness
      · intro vertex vertexOwned
        have oldOwned : vertex ∈ ownedAt index := by
          simpa [newOwnedAt, isActive] using vertexOwned
        rcases oldAccounted vertex oldOwned with
          ⟨rawAge, marked, representative⟩ |
            ⟨unmarked, frontierMembership⟩
        · apply Or.inl
          refine ⟨rawAge, ?_, ?_⟩
          · rw [afterMarks]
            exact marked
          · rw [representativeUnchanged]
            exact representative
        · apply Or.inr
          refine ⟨?_, frontierMembership⟩
          rw [afterMarks]
          exact unmarked
  · intro leftIndex rightIndex leftComponent rightComponent
      leftLookup rightLookup different
    by_cases leftActive : leftIndex = step.outputToken
    · subst leftIndex
      by_cases rightActive : rightIndex = step.outputToken
      · exact False.elim (different rightActive.symm)
      · have rightOld :
            before.components[rightIndex]? = some (some rightComponent) := by
          rw [afterComponents] at rightLookup
          simpa [Array.getElem?_setIfInBounds, Ne.symm rightActive] using
            rightLookup
        have oldSeparation := disjoint activeLookup rightOld different
        constructor
        · intro candidate candidateLeft candidateRight
          have rightOldMembership : candidate ∈ usedAt rightIndex := by
            simpa [newUsedAt, rightActive] using candidateRight
          have leftMembership :
              candidate = linkIndex ∨
                candidate ∈ usedAt step.outputToken := by
            simpa [newUsedAt] using candidateLeft
          rcases leftMembership with rfl | oldMembership
          · exact (oldLinkFresh rightOld) rightOldMembership
          · exact oldSeparation.1 candidate oldMembership rightOldMembership
        · intro vertex vertexLeft vertexRight
          have rightOldMembership : vertex ∈ ownedAt rightIndex := by
            simpa [newOwnedAt, rightActive] using vertexRight
          have leftMembership :
              vertex = conclusion ∨
                vertex ∈ ownedAt step.outputToken := by
            simpa [newOwnedAt] using vertexLeft
          rcases leftMembership with rfl | oldMembership
          · exact (conclusionFresh rightOld (live rightOld).2)
              rightOldMembership
          · exact oldSeparation.2 vertex oldMembership rightOldMembership
    · have leftOld :
          before.components[leftIndex]? = some (some leftComponent) := by
        rw [afterComponents] at leftLookup
        simpa [Array.getElem?_setIfInBounds, Ne.symm leftActive] using
          leftLookup
      by_cases rightActive : rightIndex = step.outputToken
      · subst rightIndex
        have oldSeparation := disjoint leftOld activeLookup different
        constructor
        · intro candidate candidateLeft candidateRight
          have leftOldMembership : candidate ∈ usedAt leftIndex := by
            simpa [newUsedAt, leftActive] using candidateLeft
          have rightMembership :
              candidate = linkIndex ∨
                candidate ∈ usedAt step.outputToken := by
            simpa [newUsedAt] using candidateRight
          rcases rightMembership with rfl | oldMembership
          · exact (oldLinkFresh leftOld) leftOldMembership
          · exact oldSeparation.1 candidate leftOldMembership oldMembership
        · intro vertex vertexLeft vertexRight
          have leftOldMembership : vertex ∈ ownedAt leftIndex := by
            simpa [newOwnedAt, leftActive] using vertexLeft
          have rightMembership :
              vertex = conclusion ∨
                vertex ∈ ownedAt step.outputToken := by
            simpa [newOwnedAt] using vertexRight
          rcases rightMembership with rfl | oldMembership
          · exact (conclusionFresh leftOld (live leftOld).2)
              leftOldMembership
          · exact oldSeparation.2 vertex leftOldMembership oldMembership
      · have rightOld :
            before.components[rightIndex]? = some (some rightComponent) := by
          rw [afterComponents] at rightLookup
          simpa [Array.getElem?_setIfInBounds, Ne.symm rightActive] using
            rightLookup
        have oldSeparation := disjoint leftOld rightOld different
        simpa [newUsedAt, newOwnedAt, leftActive, rightActive] using
          oldSeparation
  · intro vertex rawAge afterMarked
    have beforeMarked :
        before.marks[vertex]? = some (some rawAge) := by
      rw [afterMarks] at afterMarked
      exact afterMarked
    rcases covered beforeMarked with
      ⟨index, component, representative, componentLookup, vertexOwned⟩
    by_cases isActive : index = step.outputToken
    · have vertexOwnedActive : vertex ∈ ownedAt step.outputToken := by
        simpa [isActive] using vertexOwned
      refine ⟨step.outputToken, nextComponent, ?_, ?_, ?_⟩
      · rw [representativeUnchanged]
        exact representative.trans isActive
      · rw [afterComponents]
        simp [outputBound]
      · simp [newOwnedAt, vertexOwnedActive]
    · refine ⟨index, component, ?_, ?_, ?_⟩
      · rw [representativeUnchanged]
        exact representative
      · rw [afterComponents]
        simpa [Array.getElem?_setIfInBounds, Ne.symm isActive] using
          componentLookup
      · simpa [newOwnedAt, isActive] using vertexOwned

/-- Root-form wrapper for a scheduler caller whose delayed-par output token is
already known to be the active representative.  The retained `QueueParStep`
then supplies the exact component lookup needed by
`queueParStep_of_active_fresh`. -/
theorem queueParStep_of_root_fresh
    {certificate : Certificate}
    {before after : UnificationState}
    {left right conclusion : Vertex}
    (forest : certificate.ComponentForestProvenance before)
    (step : QueueParStep before after left right conclusion)
    (root : before.representative step.outputToken = step.outputToken)
    (linkIndex : Nat)
    (linkLookup :
      certificate.links[linkIndex]? =
        some (.par left right conclusion))
    (conclusionFresh :
      ∀ {index component owned},
        before.components[index]? = some (some component) →
        OwnedOccurrenceAccounted before index component owned →
        conclusion ∉ owned) :
    certificate.ComponentForestProvenance after := by
  apply forest.queueParStep_of_active_fresh step linkIndex linkLookup
  · have rawLookup :=
      UnificationState.componentAt?_some_raw step.component_lookup
    simpa [root] using rawLookup
  · exact conclusionFresh

/-- Merge two distinct raw-root live components through one exact submitted
tensor queue while preserving the complete occurrence-exact forest.

The successful token guard and `Abstractable` prove that the two runtime tokens
are allocated roots.  The smaller root survives and the larger root is retired,
but the new derivation itself retains the submitted left/right orientation from
`QueueTensorStep`.  Thus neither component storage order nor formula-label
equality participates in the proof.

The explicit occurrence-freshness premise is essential.  Raw-unmarkedness of
the conclusion alone does not exclude a malformed old forest from already
owning that unmarked internal occurrence. -/
theorem queueTensorStep_of_roots_fresh
    {certificate : Certificate}
    {before after : UnificationState}
    {left right conclusion : Vertex}
    (abstractable : before.Abstractable certificate)
    (ordered : before.OrderedParents)
    (forest : certificate.ComponentForestProvenance before)
    (step : QueueTensorStep before after left right conclusion)
    (linkIndex : Nat)
    (linkLookup :
      certificate.links[linkIndex]? =
        some (.tensor left right conclusion))
    (conclusionFresh :
      ∀ {index component owned},
        before.components[index]? = some (some component) →
        OwnedOccurrenceAccounted before index component owned →
        conclusion ∉ owned) :
    certificate.ComponentForestProvenance after := by
  rcases forest with ⟨usedAt, ownedAt, live, disjoint, covered⟩
  have guards := UnificationState.unifyTokens?_success step.token_guard
  have leftBound : step.leftToken < before.parents.size :=
    abstractable.tokenAt?_bound guards.2.1
  have rightBound : step.rightToken < before.parents.size :=
    abstractable.tokenAt?_bound guards.2.2.1
  have leftRoot :
      before.representative step.leftToken = step.leftToken :=
    abstractable.tokenAt?_root guards.2.1
  have rightRoot :
      before.representative step.rightToken = step.rightToken :=
    abstractable.tokenAt?_root guards.2.2.1
  have tokensDifferent : step.leftToken ≠ step.rightToken :=
    guards.2.2.2
  let survivor := min step.leftToken step.rightToken
  let retired := max step.leftToken step.rightToken
  let nextComponent : UnificationComponent := {
    tree :=
      .tensor step.leftFocus step.rightFocus
        step.leftComponent.tree step.rightComponent.tree
    frontier := conclusion :: (step.leftContext ++ step.rightContext) }
  have survivorLt : survivor < retired := by
    rcases Nat.lt_or_gt_of_ne tokensDifferent with leftLt | rightLt
    · simpa [survivor, retired, Nat.min_eq_left (Nat.le_of_lt leftLt),
        Nat.max_eq_right (Nat.le_of_lt leftLt)] using leftLt
    · simpa [survivor, retired, Nat.min_eq_right (Nat.le_of_lt rightLt),
        Nat.max_eq_left (Nat.le_of_lt rightLt)] using rightLt
  have survivorNeRetired : survivor ≠ retired := Nat.ne_of_lt survivorLt
  have retiredNeSurvivor : retired ≠ survivor := Ne.symm survivorNeRetired
  have survivorBound : survivor < before.parents.size := by
    rcases Nat.le_total step.leftToken step.rightToken with order | order
    · simpa [survivor, Nat.min_eq_left order] using leftBound
    · simpa [survivor, Nat.min_eq_right order] using rightBound
  have retiredBound : retired < before.parents.size := by
    rcases Nat.le_total step.leftToken step.rightToken with order | order
    · simpa [retired, Nat.max_eq_right order] using rightBound
    · simpa [retired, Nat.max_eq_left order] using leftBound
  have survivorRoot : before.representative survivor = survivor := by
    rcases Nat.le_total step.leftToken step.rightToken with order | order
    · simpa [survivor, Nat.min_eq_left order] using leftRoot
    · simpa [survivor, Nat.min_eq_right order] using rightRoot
  have retiredRoot : before.representative retired = retired := by
    rcases Nat.le_total step.leftToken step.rightToken with order | order
    · simpa [retired, Nat.max_eq_right order] using rightRoot
    · simpa [retired, Nat.max_eq_left order] using leftRoot
  have leftLookup :
      before.components[step.leftToken]? =
        some (some step.leftComponent) := by
    have raw :=
      UnificationState.componentAt?_some_raw step.left_component
    simpa [leftRoot] using raw
  have rightLookup :
      before.components[step.rightToken]? =
        some (some step.rightComponent) := by
    have raw :=
      UnificationState.componentAt?_some_raw step.right_component
    simpa [rightRoot] using raw
  have leftComponentBound :
      step.leftToken < before.components.size :=
    (Array.getElem?_eq_some_iff.mp leftLookup).1
  have rightComponentBound :
      step.rightToken < before.components.size :=
    (Array.getElem?_eq_some_iff.mp rightLookup).1
  have survivorComponentBound : survivor < before.components.size := by
    rcases Nat.le_total step.leftToken step.rightToken with order | order
    · simpa [survivor, Nat.min_eq_left order] using leftComponentBound
    · simpa [survivor, Nat.min_eq_right order] using rightComponentBound
  have retiredComponentBound : retired < before.components.size := by
    rcases Nat.le_total step.leftToken step.rightToken with order | order
    · simpa [retired, Nat.max_eq_right order] using rightComponentBound
    · simpa [retired, Nat.max_eq_left order] using leftComponentBound
  have leftFacts := live leftLookup
  have rightFacts := live rightLookup
  have leftRightSeparation :=
    disjoint leftLookup rightLookup tokensDifferent
  have conclusionFreshAt : ∀ {index component},
      before.components[index]? = some (some component) →
      conclusion ∉ ownedAt index := by
    intro index component componentLookup
    exact conclusionFresh componentLookup (live componentLookup).2
  have oldLinkFreshAt : ∀ {index component},
      before.components[index]? = some (some component) →
      linkIndex ∉ usedAt index := by
    intro index component componentLookup linkUsed
    have conclusionOwned : conclusion ∈ ownedAt index :=
      (live componentLookup).1.derivation.usedConnectiveConclusion_owned
        linkUsed (.inl linkLookup)
    exact (conclusionFreshAt componentLookup) conclusionOwned
  have nextWitness :
      ComponentOccurrenceWitness certificate nextComponent
        (linkIndex ::
          (usedAt step.leftToken ++ usedAt step.rightToken))
        (conclusion ::
          (ownedAt step.leftToken ++ ownedAt step.rightToken)) := by
    simpa [nextComponent] using
      ComponentOccurrenceWitness.ofQueueTensorStep step
        leftFacts.1 rightFacts.1 linkIndex linkLookup
        (oldLinkFreshAt leftLookup) (oldLinkFreshAt rightLookup)
        (conclusionFreshAt leftLookup) (conclusionFreshAt rightLookup)
        leftRightSeparation.1 leftRightSeparation.2
  let newUsedAt : Nat → List Nat := fun index =>
    if index = survivor then
      linkIndex :: (usedAt step.leftToken ++ usedAt step.rightToken)
    else
      usedAt index
  let newOwnedAt : Nat → List Vertex := fun index =>
    if index = survivor then
      conclusion :: (ownedAt step.leftToken ++ ownedAt step.rightToken)
    else
      ownedAt index
  have afterComponents :
      after.components =
        Array.setIfInBounds
          (before.components.setIfInBounds survivor (some nextComponent))
          retired none := by
    simpa [survivor, retired, nextComponent] using
      congrArg (fun state : UnificationState => state.components)
        step.after_eq
  have afterParents :
      after.parents =
        before.parents.setIfInBounds retired survivor := by
    simpa [survivor, retired] using
      congrArg (fun state : UnificationState => state.parents)
        step.after_eq
  have afterMarks : after.marks = before.marks := by
    simpa using
      congrArg (fun state : UnificationState => state.marks)
        step.after_eq
  have afterRepresentative : ∀ rawAge,
      rawAge < before.parents.size →
      after.representative rawAge =
        if before.representative rawAge = retired then
          survivor
        else
          before.representative rawAge := by
    intro rawAge rawBound
    calc
      after.representative rawAge =
          (before.setParent retired survivor).representative rawAge := by
        unfold UnificationState.representative
        simp [UnificationState.setParent, afterParents]
      _ = if before.representative rawAge = retired then
            survivor
          else
            before.representative rawAge :=
        ordered.setParent_representative survivorBound retiredBound
          survivorLt survivorRoot retiredRoot rawBound
  have leftMergesToSurvivor :
      (if step.leftToken = retired then survivor else step.leftToken) =
        survivor := by
    rcases Nat.lt_or_gt_of_ne tokensDifferent with leftLt | rightLt
    · simp [survivor, retired, Nat.min_eq_left (Nat.le_of_lt leftLt),
        Nat.max_eq_right (Nat.le_of_lt leftLt)]
    · simp [survivor, retired, Nat.min_eq_right (Nat.le_of_lt rightLt),
        Nat.max_eq_left (Nat.le_of_lt rightLt)]
  have rightMergesToSurvivor :
      (if step.rightToken = retired then survivor else step.rightToken) =
        survivor := by
    rcases Nat.lt_or_gt_of_ne tokensDifferent with leftLt | rightLt
    · simp [survivor, retired, Nat.min_eq_left (Nat.le_of_lt leftLt),
        Nat.max_eq_right (Nat.le_of_lt leftLt)]
    · simp [survivor, retired, Nat.min_eq_right (Nat.le_of_lt rightLt),
        Nat.max_eq_left (Nat.le_of_lt rightLt)]
  have leftAtEdge :
      step.leftToken = survivor ∨ step.leftToken = retired := by
    rcases Nat.lt_or_gt_of_ne tokensDifferent with leftLt | rightLt
    · exact Or.inl (by simp [survivor,
        Nat.min_eq_left (Nat.le_of_lt leftLt)])
    · exact Or.inr (by simp [retired,
        Nat.max_eq_left (Nat.le_of_lt rightLt)])
  have rightAtEdge :
      step.rightToken = survivor ∨ step.rightToken = retired := by
    rcases Nat.lt_or_gt_of_ne tokensDifferent with leftLt | rightLt
    · exact Or.inr (by simp [retired,
        Nat.max_eq_right (Nat.le_of_lt leftLt)])
    · exact Or.inl (by simp [survivor,
        Nat.min_eq_right (Nat.le_of_lt rightLt)])
  have afterSurvivorLookup :
      after.components[survivor]? = some (some nextComponent) := by
    rw [afterComponents]
    simp [survivorComponentBound, retiredNeSurvivor]
  have oldOfAfter : ∀ {index component},
      after.components[index]? = some (some component) →
      index ≠ survivor →
      index ≠ retired ∧
        before.components[index]? = some (some component) := by
    intro index component componentLookup indexNeSurvivor
    have indexNeRetired : index ≠ retired := by
      intro same
      subst index
      rw [afterComponents] at componentLookup
      simp [retiredComponentBound] at componentLookup
    constructor
    · exact indexNeRetired
    · rw [afterComponents] at componentLookup
      simpa [Array.getElem?_setIfInBounds,
        Ne.symm indexNeSurvivor, Ne.symm indexNeRetired] using
          componentLookup
  have leftMarked : ∃ rawAge,
      before.marks[left]? = some (some rawAge) := by
    rcases before.tokenAt?_some_witness guards.2.1 with
      ⟨rawAge, assigned, _⟩
    exact ⟨rawAge, UnificationState.assignedToken?_some_raw assigned⟩
  have rightMarked : ∃ rawAge,
      before.marks[right]? = some (some rawAge) := by
    rcases before.tokenAt?_some_witness guards.2.2.1 with
      ⟨rawAge, assigned, _⟩
    exact ⟨rawAge, UnificationState.assignedToken?_some_raw assigned⟩
  refine ⟨newUsedAt, newOwnedAt, ?_, ?_, ?_⟩
  · intro index component componentLookup
    by_cases isSurvivor : index = survivor
    · subst index
      have componentEq : component = nextComponent := by
        rw [afterSurvivorLookup] at componentLookup
        exact Option.some.inj (Option.some.inj componentLookup.symm)
      subst component
      refine ⟨?_, ?_⟩
      · simpa [newUsedAt, newOwnedAt] using nextWitness
      · intro vertex vertexOwned
        simp only [newOwnedAt, if_pos, List.mem_cons,
          List.mem_append] at vertexOwned
        rcases vertexOwned with rfl | leftOwned | rightOwned
        · apply Or.inr
          refine ⟨?_, by simp [nextComponent]⟩
          rw [afterMarks]
          exact guards.1
        · rcases leftFacts.2 vertex leftOwned with
            ⟨rawAge, marked, representative⟩ |
              ⟨unmarked, frontierMembership⟩
          · apply Or.inl
            refine ⟨rawAge, ?_, ?_⟩
            · rw [afterMarks]
              exact marked
            · have rawBound : rawAge < before.parents.size := by
                apply abstractable.markedTokenBound
                unfold UnificationState.assignedToken?
                rw [marked]
                rfl
              rw [afterRepresentative rawAge rawBound, representative]
              exact leftMergesToSurvivor
          · have vertexNeLeft : vertex ≠ left := by
              intro same
              subst vertex
              rcases leftMarked with ⟨rawAge, marked⟩
              rw [unmarked] at marked
              simp at marked
            have contextMembership : vertex ∈ step.leftContext := by
              have membership : vertex ∈ left :: step.leftContext :=
                (CutFreeDerivation.pick?_perm
                  (FirstOccurrencePick.positional step.left_pick)).mem_iff.mp
                    frontierMembership
              simpa [vertexNeLeft] using membership
            apply Or.inr
            refine ⟨?_, by simp [nextComponent, contextMembership]⟩
            rw [afterMarks]
            exact unmarked
        · rcases rightFacts.2 vertex rightOwned with
            ⟨rawAge, marked, representative⟩ |
              ⟨unmarked, frontierMembership⟩
          · apply Or.inl
            refine ⟨rawAge, ?_, ?_⟩
            · rw [afterMarks]
              exact marked
            · have rawBound : rawAge < before.parents.size := by
                apply abstractable.markedTokenBound
                unfold UnificationState.assignedToken?
                rw [marked]
                rfl
              rw [afterRepresentative rawAge rawBound, representative]
              exact rightMergesToSurvivor
          · have vertexNeRight : vertex ≠ right := by
              intro same
              subst vertex
              rcases rightMarked with ⟨rawAge, marked⟩
              rw [unmarked] at marked
              simp at marked
            have contextMembership : vertex ∈ step.rightContext := by
              have membership : vertex ∈ right :: step.rightContext :=
                (CutFreeDerivation.pick?_perm
                  (FirstOccurrencePick.positional step.right_pick)).mem_iff.mp
                    frontierMembership
              simpa [vertexNeRight] using membership
            apply Or.inr
            refine ⟨?_, by simp [nextComponent, contextMembership]⟩
            rw [afterMarks]
            exact unmarked
    · rcases oldOfAfter componentLookup isSurvivor with
        ⟨isRetired, oldLookup⟩
      rcases live oldLookup with ⟨oldWitness, oldAccounted⟩
      refine ⟨?_, ?_⟩
      · simpa [newUsedAt, newOwnedAt, isSurvivor] using oldWitness
      · intro vertex vertexOwned
        have oldOwned : vertex ∈ ownedAt index := by
          simpa [newOwnedAt, isSurvivor] using vertexOwned
        rcases oldAccounted vertex oldOwned with
          ⟨rawAge, marked, representative⟩ |
            ⟨unmarked, frontierMembership⟩
        · apply Or.inl
          refine ⟨rawAge, ?_, ?_⟩
          · rw [afterMarks]
            exact marked
          · have rawBound : rawAge < before.parents.size := by
              apply abstractable.markedTokenBound
              unfold UnificationState.assignedToken?
              rw [marked]
              rfl
            rw [afterRepresentative rawAge rawBound, representative]
            simp [isRetired]
        · apply Or.inr
          refine ⟨?_, frontierMembership⟩
          rw [afterMarks]
          exact unmarked
  · intro leftIndex rightIndex leftComponent rightComponent
      leftAfter rightAfter indexesDifferent
    by_cases leftSurvivor : leftIndex = survivor
    · subst leftIndex
      have leftComponentEq : leftComponent = nextComponent := by
        rw [afterSurvivorLookup] at leftAfter
        exact Option.some.inj (Option.some.inj leftAfter.symm)
      subst leftComponent
      by_cases rightSurvivor : rightIndex = survivor
      · exact False.elim (indexesDifferent rightSurvivor.symm)
      · rcases oldOfAfter rightAfter rightSurvivor with
          ⟨rightRetired, rightOld⟩
        have rightNeLeftToken : rightIndex ≠ step.leftToken := by
          intro same
          subst rightIndex
          rcases leftAtEdge with atSurvivor | atRetired
          · exact rightSurvivor atSurvivor
          · exact rightRetired atRetired
        have rightNeRightToken : rightIndex ≠ step.rightToken := by
          intro same
          subst rightIndex
          rcases rightAtEdge with atSurvivor | atRetired
          · exact rightSurvivor atSurvivor
          · exact rightRetired atRetired
        have leftSep := disjoint leftLookup rightOld (Ne.symm rightNeLeftToken)
        have rightSep := disjoint rightLookup rightOld (Ne.symm rightNeRightToken)
        constructor
        · intro candidate candidateLeft candidateRight
          have rightOldMembership : candidate ∈ usedAt rightIndex := by
            simpa [newUsedAt, rightSurvivor] using candidateRight
          have nextMembership :
              candidate = linkIndex ∨
                candidate ∈ usedAt step.leftToken ∨
                candidate ∈ usedAt step.rightToken := by
            simpa [newUsedAt, List.mem_append] using candidateLeft
          rcases nextMembership with rfl | leftMembership | rightMembership
          · exact (oldLinkFreshAt rightOld) rightOldMembership
          · exact leftSep.1 candidate leftMembership rightOldMembership
          · exact rightSep.1 candidate rightMembership rightOldMembership
        · intro vertex vertexLeft vertexRight
          have rightOldMembership : vertex ∈ ownedAt rightIndex := by
            simpa [newOwnedAt, rightSurvivor] using vertexRight
          have nextMembership :
              vertex = conclusion ∨
                vertex ∈ ownedAt step.leftToken ∨
                vertex ∈ ownedAt step.rightToken := by
            simpa [newOwnedAt, List.mem_append] using vertexLeft
          rcases nextMembership with rfl | leftMembership | rightMembership
          · exact (conclusionFreshAt rightOld) rightOldMembership
          · exact leftSep.2 vertex leftMembership rightOldMembership
          · exact rightSep.2 vertex rightMembership rightOldMembership
    · rcases oldOfAfter leftAfter leftSurvivor with
        ⟨leftRetired, leftOld⟩
      by_cases rightSurvivor : rightIndex = survivor
      · subst rightIndex
        have rightComponentEq : rightComponent = nextComponent := by
          rw [afterSurvivorLookup] at rightAfter
          exact Option.some.inj (Option.some.inj rightAfter.symm)
        subst rightComponent
        have leftNeLeftToken : leftIndex ≠ step.leftToken := by
          intro same
          subst leftIndex
          rcases leftAtEdge with atSurvivor | atRetired
          · exact leftSurvivor atSurvivor
          · exact leftRetired atRetired
        have leftNeRightToken : leftIndex ≠ step.rightToken := by
          intro same
          subst leftIndex
          rcases rightAtEdge with atSurvivor | atRetired
          · exact leftSurvivor atSurvivor
          · exact leftRetired atRetired
        have leftSep := disjoint leftOld leftLookup leftNeLeftToken
        have rightSep := disjoint leftOld rightLookup leftNeRightToken
        constructor
        · intro candidate candidateLeft candidateRight
          have leftOldMembership : candidate ∈ usedAt leftIndex := by
            simpa [newUsedAt, leftSurvivor] using candidateLeft
          have nextMembership :
              candidate = linkIndex ∨
                candidate ∈ usedAt step.leftToken ∨
                candidate ∈ usedAt step.rightToken := by
            simpa [newUsedAt, List.mem_append] using candidateRight
          rcases nextMembership with rfl | leftMembership | rightMembership
          · exact (oldLinkFreshAt leftOld) leftOldMembership
          · exact leftSep.1 candidate leftOldMembership leftMembership
          · exact rightSep.1 candidate leftOldMembership rightMembership
        · intro vertex vertexLeft vertexRight
          have leftOldMembership : vertex ∈ ownedAt leftIndex := by
            simpa [newOwnedAt, leftSurvivor] using vertexLeft
          have nextMembership :
              vertex = conclusion ∨
                vertex ∈ ownedAt step.leftToken ∨
                vertex ∈ ownedAt step.rightToken := by
            simpa [newOwnedAt, List.mem_append] using vertexRight
          rcases nextMembership with rfl | leftMembership | rightMembership
          · exact (conclusionFreshAt leftOld) leftOldMembership
          · exact leftSep.2 vertex leftOldMembership leftMembership
          · exact rightSep.2 vertex leftOldMembership rightMembership
      · rcases oldOfAfter rightAfter rightSurvivor with
          ⟨rightRetired, rightOld⟩
        have oldSeparation := disjoint leftOld rightOld indexesDifferent
        simpa [newUsedAt, newOwnedAt, leftSurvivor, rightSurvivor] using
          oldSeparation
  · intro vertex rawAge afterMarked
    have beforeMarked :
        before.marks[vertex]? = some (some rawAge) := by
      rw [afterMarks] at afterMarked
      exact afterMarked
    have rawBound : rawAge < before.parents.size := by
      apply abstractable.markedTokenBound
      unfold UnificationState.assignedToken?
      rw [beforeMarked]
      rfl
    rcases covered beforeMarked with
      ⟨index, component, representative, oldLookup, vertexOwned⟩
    by_cases indexSurvivor : index = survivor
    · have afterRep : after.representative rawAge = survivor := by
        rw [afterRepresentative rawAge rawBound, representative,
          indexSurvivor]
        simp [survivorNeRetired]
      refine ⟨survivor, nextComponent, afterRep,
        afterSurvivorLookup, ?_⟩
      rcases leftAtEdge with leftIsSurvivor | leftIsRetired
      · have rightIsRetired : step.rightToken = retired := by
          rcases rightAtEdge with rightIsSurvivor | rightIsRetired
          · exact False.elim
              (tokensDifferent (leftIsSurvivor.trans rightIsSurvivor.symm))
          · exact rightIsRetired
        simpa [newOwnedAt, leftIsSurvivor, rightIsRetired,
          indexSurvivor, List.mem_append] using
            Or.inr (Or.inl vertexOwned)
      · have rightIsSurvivor : step.rightToken = survivor := by
          rcases rightAtEdge with rightIsSurvivor | rightIsRetired
          · exact rightIsSurvivor
          · exact False.elim
              (tokensDifferent (leftIsRetired.trans rightIsRetired.symm))
        simpa [newOwnedAt, leftIsRetired, rightIsSurvivor,
          indexSurvivor, List.mem_append] using
            Or.inr (Or.inr vertexOwned)
    · by_cases indexRetired : index = retired
      · have afterRep : after.representative rawAge = survivor := by
          rw [afterRepresentative rawAge rawBound, representative,
            indexRetired]
          simp
        refine ⟨survivor, nextComponent, afterRep,
          afterSurvivorLookup, ?_⟩
        rcases leftAtEdge with leftIsSurvivor | leftIsRetired
        · have rightIsRetired : step.rightToken = retired := by
            rcases rightAtEdge with rightIsSurvivor | rightIsRetired
            · exact False.elim
                (tokensDifferent (leftIsSurvivor.trans rightIsSurvivor.symm))
            · exact rightIsRetired
          simpa [newOwnedAt, leftIsSurvivor, rightIsRetired,
            indexRetired, List.mem_append] using
              Or.inr (Or.inr vertexOwned)
        · have rightIsSurvivor : step.rightToken = survivor := by
            rcases rightAtEdge with rightIsSurvivor | rightIsRetired
            · exact rightIsSurvivor
            · exact False.elim
                (tokensDifferent (leftIsRetired.trans rightIsRetired.symm))
          simpa [newOwnedAt, leftIsRetired, rightIsSurvivor,
            indexRetired, List.mem_append] using
              Or.inr (Or.inl vertexOwned)
      · have afterRep : after.representative rawAge = index := by
          rw [afterRepresentative rawAge rawBound, representative]
          simp [indexRetired]
        refine ⟨index, component, afterRep, ?_, ?_⟩
        · rw [afterComponents]
          simpa [Array.getElem?_setIfInBounds,
            Ne.symm indexSurvivor, Ne.symm indexRetired] using oldLookup
        · simpa [newOwnedAt, indexSurvivor] using vertexOwned

/-- Appending a fresh submitted axiom preserves the occurrence-exact live
component forest when both exact endpoints are absent from every old owner. -/
theorem reserveAxiomAt?_of_fresh
    {certificate : Certificate} {before after : UnificationState}
    {linkIndex : Nat}
    (structural : certificate.StructurallyWellFormed)
    (ordered : before.OrderedParents)
    (forest : certificate.ComponentForestProvenance before)
    (fresh : ∀ {left right},
      certificate.links[linkIndex]? = some (.axiom left right) →
      ∀ {index component owned},
        before.components[index]? = some (some component) →
        OwnedOccurrenceAccounted before index component owned →
        left ∉ owned ∧ right ∉ owned)
    (equation : certificate.reserveAxiomAt? before linkIndex = some after) :
    certificate.ComponentForestProvenance after := by
  rcases forest with ⟨usedAt, ownedAt, live, disjoint, covered⟩
  rcases certificate.reserveAxiomAt?_exact equation with
    ⟨left, right, newComponent, linkLookup, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  rcases UnificationComponent.axiom?_success componentLookup with
    ⟨name, positive, leftFormula, newComponentEq⟩
  let freshIndex := before.components.size
  let newUsedAt : Nat → List Nat := fun index =>
    if index = freshIndex then [linkIndex] else usedAt index
  let newOwnedAt : Nat → List Nat := fun index =>
    if index = freshIndex then [left, right] else ownedAt index
  have newWitness :
      ComponentOccurrenceWitness certificate newComponent
        [linkIndex] [left, right] := by
    rw [newComponentEq]
    exact ComponentOccurrenceWitness.axiom_of_submitted
      structural linkLookup leftFormula
  have oldRepresentative : ∀ token,
      after.representative token = before.representative token := by
    intro token
    exact certificate.reserveAxiomAt?_old_representative ordered equation
  have oldEndpointFresh : ∀ {index component},
      before.components[index]? = some (some component) →
      left ∉ ownedAt index ∧ right ∉ ownedAt index := by
    intro index component oldLookup
    exact fresh linkLookup oldLookup (live oldLookup).2
  have oldLinkFresh : ∀ {index component},
      before.components[index]? = some (some component) →
      linkIndex ∉ usedAt index := by
    intro index component oldLookup linkUsed
    have endpoints :=
      (live oldLookup).1.derivation.usedAxiomEndpoints_owned
        linkUsed linkLookup
    exact (oldEndpointFresh oldLookup).1 endpoints.1
  refine ⟨newUsedAt, newOwnedAt, ?_, ?_, ?_⟩
  · intro index component afterLookup
    by_cases isFresh : index = freshIndex
    · subst index
      have componentEq : component = newComponent := by
        rw [componentsEq] at afterLookup
        simpa [freshIndex] using afterLookup.symm
      subst component
      refine ⟨?_, ?_⟩
      · simpa [newUsedAt, newOwnedAt] using newWitness
      · intro vertex vertexOwned
        simp only [newOwnedAt, if_pos, List.mem_cons,
          List.not_mem_nil, or_false] at vertexOwned
        rcases vertexOwned with rfl | rfl
        · apply Or.inr
          refine ⟨?_, ?_⟩
          · rw [marksEq]
            exact ready.2.1
          · rw [frontier]
            simp
        · apply Or.inr
          refine ⟨?_, ?_⟩
          · rw [marksEq]
            exact ready.2.2.1
          · rw [frontier]
            simp
    · have oldLookup : before.components[index]? = some (some component) := by
        rw [componentsEq] at afterLookup
        simpa [Array.getElem?_push, freshIndex, isFresh] using afterLookup
      rcases live oldLookup with ⟨oldWitness, oldAccounted⟩
      refine ⟨?_, ?_⟩
      · simpa [newUsedAt, newOwnedAt, isFresh] using oldWitness
      · intro vertex vertexOwned
        have oldOwned : vertex ∈ ownedAt index := by
          simpa [newOwnedAt, isFresh] using vertexOwned
        rcases oldAccounted vertex oldOwned with
          ⟨rawAge, marked, representative⟩ | ⟨unmarked, inFrontier⟩
        · apply Or.inl
          refine ⟨rawAge, ?_, ?_⟩
          · rw [marksEq]
            exact marked
          · rw [oldRepresentative]
            exact representative
        · apply Or.inr
          refine ⟨?_, inFrontier⟩
          rw [marksEq]
          exact unmarked
  · intro leftIndex rightIndex leftComponent rightComponent
      leftLookup rightLookup different
    by_cases leftFresh : leftIndex = freshIndex
    · subst leftIndex
      by_cases rightFresh : rightIndex = freshIndex
      · exact False.elim (different rightFresh.symm)
      · have rightOld : before.components[rightIndex]? = some (some rightComponent) := by
          rw [componentsEq] at rightLookup
          simpa [Array.getElem?_push, freshIndex, rightFresh] using rightLookup
        have leftComponentEq : leftComponent = newComponent := by
          rw [componentsEq] at leftLookup
          simpa [freshIndex] using leftLookup.symm
        subst leftComponent
        have endpointFresh := oldEndpointFresh rightOld
        have linkFresh := oldLinkFresh rightOld
        constructor
        · intro candidate candidateMembership candidateInRight
          have candidateEq : candidate = linkIndex := by
            simpa [newUsedAt] using candidateMembership
          subst candidate
          have oldMembership : linkIndex ∈ usedAt rightIndex := by
            simpa [newUsedAt, rightFresh] using candidateInRight
          exact linkFresh oldMembership
        · intro vertex vertexMembership vertexInRight
          have endpoint : vertex = left ∨ vertex = right := by
            simpa [newOwnedAt] using vertexMembership
          have oldMembership : vertex ∈ ownedAt rightIndex := by
            simpa [newOwnedAt, rightFresh] using vertexInRight
          rcases endpoint with rfl | rfl
          · exact endpointFresh.1 oldMembership
          · exact endpointFresh.2 oldMembership
    · have leftOld : before.components[leftIndex]? = some (some leftComponent) := by
        rw [componentsEq] at leftLookup
        simpa [Array.getElem?_push, freshIndex, leftFresh] using leftLookup
      by_cases rightFresh : rightIndex = freshIndex
      · subst rightIndex
        have rightComponentEq : rightComponent = newComponent := by
          rw [componentsEq] at rightLookup
          simpa [freshIndex] using rightLookup.symm
        subst rightComponent
        have endpointFresh := oldEndpointFresh leftOld
        have linkFresh := oldLinkFresh leftOld
        constructor
        · intro candidate candidateMembership candidateInRight
          have oldMembership : candidate ∈ usedAt leftIndex := by
            simpa [newUsedAt, leftFresh] using candidateMembership
          have candidateEq : candidate = linkIndex := by
            simpa [newUsedAt] using candidateInRight
          subst candidate
          exact linkFresh oldMembership
        · intro vertex vertexMembership vertexInRight
          have oldMembership : vertex ∈ ownedAt leftIndex := by
            simpa [newOwnedAt, leftFresh] using vertexMembership
          have endpoint : vertex = left ∨ vertex = right := by
            simpa [newOwnedAt] using vertexInRight
          rcases endpoint with rfl | rfl
          · exact endpointFresh.1 oldMembership
          · exact endpointFresh.2 oldMembership
      · have rightOld : before.components[rightIndex]? = some (some rightComponent) := by
          rw [componentsEq] at rightLookup
          simpa [Array.getElem?_push, freshIndex, rightFresh] using rightLookup
        have oldDisjoint := disjoint leftOld rightOld different
        simpa [newUsedAt, newOwnedAt, leftFresh, rightFresh] using oldDisjoint
  · intro vertex rawAge afterMarked
    have beforeMarked : before.marks[vertex]? = some (some rawAge) := by
      rw [marksEq] at afterMarked
      exact afterMarked
    rcases covered beforeMarked with
      ⟨index, component, representative, componentLookupOld, vertexOwned⟩
    have indexBound := (Array.getElem?_eq_some_iff.mp componentLookupOld).1
    have indexNotFresh : index ≠ freshIndex := by
      intro same
      rw [same] at indexBound
      change freshIndex < before.components.size at indexBound
      dsimp [freshIndex] at indexBound
      exact (Nat.lt_irrefl _) indexBound
    refine ⟨index, component, ?_, ?_, ?_⟩
    · rw [oldRepresentative]
      exact representative
    · rw [componentsEq]
      simpa [Array.getElem?_push, freshIndex, indexNotFresh] using componentLookupOld
    · simpa [newOwnedAt, indexNotFresh] using vertexOwned

end ComponentForestProvenance

/-- The empty executable core admits a canonical empty
component-provenance witness: no live slot has a witness and no concrete raw
mark needs an owner. -/
theorem initialUnificationState_componentForestProvenance
    (certificate : Certificate) :
    certificate.ComponentForestProvenance
      certificate.initialUnificationState := by
  refine ⟨(fun _ => []), (fun _ => []), ?_, ?_, ?_⟩
  · intro index component lookup
    simp [Certificate.initialUnificationState] at lookup
  · intro leftIndex rightIndex leftComponent rightComponent leftLookup
    simp [Certificate.initialUnificationState] at leftLookup
  · intro vertex rawAge marked
    simp [Certificate.initialUnificationState,
      Array.getElem?_replicate] at marked

/-- Reserving the first submitted axiom over the empty executable core creates
the singleton component-provenance forest at raw slot zero. -/
theorem reserveAxiomAt?_componentForestProvenance_of_initial
    {certificate : Certificate} {after : UnificationState}
    {linkIndex : Nat}
    (structural : certificate.StructurallyWellFormed)
    (equation :
      certificate.reserveAxiomAt?
          certificate.initialUnificationState linkIndex = some after) :
    certificate.ComponentForestProvenance after := by
  rcases certificate.reserveAxiomAt?_exact equation with
    ⟨left, right, component, linkLookup, ready, componentLookup,
      frontier, marksEq, _parentsEq, componentsEq, _counterEq, _firedEq⟩
  rcases UnificationComponent.axiom?_success componentLookup with
    ⟨name, positive, leftFormula, componentEq⟩
  let usedAt : Nat → List Nat :=
    fun index => if index = 0 then [linkIndex] else []
  let ownedAt : Nat → List Nat :=
    fun index => if index = 0 then [left, right] else []
  have witness :
      certificate.ComponentOccurrenceWitness component
        [linkIndex] [left, right] := by
    rw [componentEq]
    exact ComponentOccurrenceWitness.axiom_of_submitted
      structural linkLookup leftFormula
  have componentsSingleton :
      after.components = #[some component] := by
    simpa [Certificate.initialUnificationState] using componentsEq
  refine ⟨usedAt, ownedAt, ?_, ?_, ?_⟩
  · intro index candidate afterLookup
    rw [componentsSingleton] at afterLookup
    have indexZero : index = 0 := by
      have indexBound := (Array.getElem?_eq_some_iff.mp afterLookup).1
      simpa using indexBound
    subst index
    have candidateEq : candidate = component := by
      simpa using afterLookup.symm
    subst candidate
    simp [usedAt, ownedAt]
    refine ⟨witness, ?_⟩
    intro vertex vertexOwned
    simp only [List.mem_cons, List.not_mem_nil, or_false] at vertexOwned
    rcases vertexOwned with rfl | rfl
    · apply Or.inr
      refine ⟨?_, ?_⟩
      · rw [marksEq]
        exact ready.2.1
      · rw [frontier]
        simp
    · apply Or.inr
      refine ⟨?_, ?_⟩
      · rw [marksEq]
        exact ready.2.2.1
      · rw [frontier]
        simp
  · intro leftIndex rightIndex leftComponent rightComponent
      leftLookup rightLookup different
    rw [componentsSingleton] at leftLookup rightLookup
    have leftZero : leftIndex = 0 := by
      have bound := (Array.getElem?_eq_some_iff.mp leftLookup).1
      simpa using bound
    have rightZero : rightIndex = 0 := by
      have bound := (Array.getElem?_eq_some_iff.mp rightLookup).1
      simpa using bound
    exact False.elim (different (leftZero.trans rightZero.symm))
  · intro vertex rawAge marked
    rw [marksEq] at marked
    simp [Certificate.initialUnificationState,
      Array.getElem?_replicate] at marked

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
