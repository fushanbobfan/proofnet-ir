import ProofNetIR.Graph

namespace ProofNetIR

namespace Certificate

def fixedEdges (certificate : Certificate) : List Edge :=
  certificate.links.flatMap fun
    | .axiom left right => [{ first := left, second := right }]
    | .tensor left right conclusion =>
        [{ first := left, second := conclusion },
         { first := right, second := conclusion }]
    | .par _ _ _ => []

def parChoices (certificate : Certificate) : List (Edge × Edge) :=
  certificate.links.filterMap fun
    | .par left right conclusion =>
        some ({ first := left, second := conclusion },
          { first := right, second := conclusion })
    | _ => none

def enumerateChoices : List (Edge × Edge) → List (List Edge)
  | [] => [[]]
  | (left, right) :: rest =>
      (enumerateChoices rest).flatMap fun suffix =>
        [left :: suffix, right :: suffix]

/-- Independent semantics for selecting exactly one edge from every par-link
choice. -/
inductive ChoiceSelection : List (Edge × Edge) → List Edge → Prop where
  | nil : ChoiceSelection [] []
  | left {left right : Edge} {rest : List (Edge × Edge)}
      {selected : List Edge} :
      ChoiceSelection rest selected →
      ChoiceSelection ((left, right) :: rest) (left :: selected)
  | right {left right : Edge} {rest : List (Edge × Edge)}
      {selected : List Edge} :
      ChoiceSelection rest selected →
      ChoiceSelection ((left, right) :: rest) (right :: selected)

theorem enumerateChoices_sound (choices : List (Edge × Edge))
    {selected : List Edge} (membership : selected ∈ enumerateChoices choices) :
    ChoiceSelection choices selected := by
  induction choices generalizing selected with
  | nil =>
      simp [enumerateChoices] at membership
      subst selected
      exact .nil
  | cons choice rest ih =>
      rcases choice with ⟨left, right⟩
      simp [enumerateChoices, List.mem_flatMap] at membership
      rcases membership with
        ⟨suffix, suffixMembership, same⟩
      rcases same with same | same
      · subst selected
        exact .left (ih suffixMembership)
      · subst selected
        exact .right (ih suffixMembership)

theorem enumerateChoices_complete {choices : List (Edge × Edge)}
    {selected : List Edge} (selection : ChoiceSelection choices selected) :
    selected ∈ enumerateChoices choices := by
  induction selection with
  | nil => simp [enumerateChoices]
  | left prior ih =>
      simp only [enumerateChoices, List.mem_flatMap]
      exact ⟨_, ih, by simp⟩
  | right prior ih =>
      simp only [enumerateChoices, List.mem_flatMap]
      exact ⟨_, ih, by simp⟩

theorem mem_enumerateChoices_iff (choices : List (Edge × Edge))
    (selected : List Edge) :
    selected ∈ enumerateChoices choices ↔ ChoiceSelection choices selected :=
  ⟨enumerateChoices_sound choices, enumerateChoices_complete⟩

def graphForSelection (certificate : Certificate)
    (selected : List Edge) : Graph :=
  { vertexCount := certificate.formulas.size
    edges := certificate.fixedEdges ++ selected }

def switchingGraphs (certificate : Certificate) : List Graph :=
  (enumerateChoices certificate.parChoices).map certificate.graphForSelection

/-- A switching graph stated without referring to the enumeration algorithm. -/
def SwitchingGraph (certificate : Certificate) (graph : Graph) : Prop :=
  ∃ selected,
    ChoiceSelection certificate.parChoices selected ∧
    graph = certificate.graphForSelection selected

theorem mem_switchingGraphs_iff (certificate : Certificate) (graph : Graph) :
    graph ∈ certificate.switchingGraphs ↔ certificate.SwitchingGraph graph := by
  constructor
  · intro membership
    simp only [switchingGraphs, List.mem_map] at membership
    rcases membership with ⟨selected, selectedMembership, same⟩
    exact ⟨selected, enumerateChoices_sound certificate.parChoices
      selectedMembership, same.symm⟩
  · rintro ⟨selected, selection, rfl⟩
    simp only [switchingGraphs, List.mem_map]
    exact ⟨selected, enumerateChoices_complete selection, rfl⟩

def allTrees : List Graph → Bool
  | [] => true
  | graph :: rest => graph.isTree && allTrees rest

/-- The kernel-executable ProofNet-IR checker. -/
def check (certificate : Certificate) : Bool :=
  certificate.wellFormed && allTrees certificate.switchingGraphs

/-- The mathematical contract promised by an accepted certificate. -/
def Correct (certificate : Certificate) : Prop :=
  certificate.wellFormed = true ∧
    ∀ graph ∈ certificate.switchingGraphs, graph.IsTree

/-- Correctness quantified over the independent switching-choice relation. -/
def DeclarativelyCorrect (certificate : Certificate) : Prop :=
  certificate.StructurallyWellFormed ∧
    ∀ graph, certificate.SwitchingGraph graph → graph.IsTree

theorem correct_iff_declarative (certificate : Certificate) :
    certificate.Correct ↔ certificate.DeclarativelyCorrect := by
  constructor
  · intro correct
    exact ⟨certificate.wellFormed_iff_structurallyWellFormed.mp correct.1, by
      intro graph switching
      exact correct.2 graph
        (certificate.mem_switchingGraphs_iff graph |>.mpr switching)⟩
  · intro correct
    exact ⟨certificate.wellFormed_iff_structurallyWellFormed.mpr correct.1, by
      intro graph membership
      exact correct.2 graph
        (certificate.mem_switchingGraphs_iff graph |>.mp membership)⟩

theorem allTrees_sound (graphs : List Graph) (accepted : allTrees graphs = true) :
    ∀ graph ∈ graphs, graph.IsTree := by
  induction graphs with
  | nil => simp
  | cons head tail ih =>
      simp [allTrees] at accepted
      intro graph membership
      simp at membership
      cases membership with
      | inl same =>
          subst graph
          exact head.isTree_sound accepted.1
      | inr memberTail =>
          exact ih accepted.2 graph memberTail

theorem allTrees_computational (graphs : List Graph)
    (accepted : allTrees graphs = true) :
    ∀ graph ∈ graphs, graph.ComputationalTree := by
  induction graphs with
  | nil => simp
  | cons head tail ih =>
      simp [allTrees] at accepted
      intro graph membership
      simp at membership
      cases membership with
      | inl same =>
          subst graph
          exact head.isTree_iff_computational.mp accepted.1
      | inr memberTail =>
          exact ih accepted.2 graph memberTail

theorem allTrees_complete_computational (graphs : List Graph)
    (correct : ∀ graph ∈ graphs, graph.ComputationalTree) :
    allTrees graphs = true := by
  induction graphs with
  | nil => rfl
  | cons head tail ih =>
      simp [allTrees]
      constructor
      · exact head.isTree_iff_computational.mpr (correct head (by simp))
      · exact ih (by
          intro graph membership
          exact correct graph (by simp [membership]))

theorem allTrees_fuel (graphs : List Graph) (accepted : allTrees graphs = true) :
    ∀ graph ∈ graphs, graph.FuelTree := by
  intro graph membership
  have computational := allTrees_computational graphs accepted graph membership
  exact graph.isTree_iff_fuelTree.mp
    (graph.isTree_iff_computational.mpr computational)

theorem allTrees_complete_fuel (graphs : List Graph)
    (correct : ∀ graph ∈ graphs, graph.FuelTree) :
    allTrees graphs = true := by
  apply allTrees_complete_computational
  intro graph membership
  exact graph.isTree_iff_computational.mp
    (graph.isTree_iff_fuelTree.mpr (correct graph membership))

/-- Any accepted executable certificate satisfies the declarative criterion. -/
theorem check_sound (certificate : Certificate) (accepted : certificate.check = true) :
    certificate.Correct := by
  simp [check] at accepted
  exact ⟨accepted.1, allTrees_sound certificate.switchingGraphs accepted.2⟩

theorem check_sound_declarative (certificate : Certificate)
    (accepted : certificate.check = true) :
    certificate.DeclarativelyCorrect :=
  certificate.correct_iff_declarative.mp (certificate.check_sound accepted)

/-- The exact finite-computation contract used for an executable completeness theorem. -/
def ComputationallyCorrect (certificate : Certificate) : Prop :=
  certificate.wellFormed = true ∧
    ∀ graph ∈ certificate.switchingGraphs, graph.ComputationalTree

/-- Independent fuel-indexed correctness semantics. Unlike
`ComputationallyCorrect`, this contract is stated through adjacency paths, but
it still has a checker completeness theorem. -/
def FuelCorrect (certificate : Certificate) : Prop :=
  certificate.wellFormed = true ∧
    ∀ graph ∈ certificate.switchingGraphs, graph.FuelTree

/-- Fuel-indexed correctness over the independent switching-choice relation. -/
def FuelDeclarativelyCorrect (certificate : Certificate) : Prop :=
  certificate.StructurallyWellFormed ∧
    ∀ graph, certificate.SwitchingGraph graph → graph.FuelTree

theorem fuelCorrect_iff_declarative (certificate : Certificate) :
    certificate.FuelCorrect ↔ certificate.FuelDeclarativelyCorrect := by
  constructor
  · intro correct
    exact ⟨certificate.wellFormed_iff_structurallyWellFormed.mp correct.1, by
      intro graph switching
      exact correct.2 graph
        (certificate.mem_switchingGraphs_iff graph |>.mpr switching)⟩
  · intro correct
    exact ⟨certificate.wellFormed_iff_structurallyWellFormed.mpr correct.1, by
      intro graph membership
      exact correct.2 graph
        (certificate.mem_switchingGraphs_iff graph |>.mp membership)⟩

/-- The checker is complete for its exact finite-computation contract. -/
theorem check_complete_computational (certificate : Certificate)
    (correct : certificate.ComputationallyCorrect) :
    certificate.check = true := by
  simp [check]
  exact ⟨correct.1,
    allTrees_complete_computational certificate.switchingGraphs correct.2⟩

theorem check_iff_computational (certificate : Certificate) :
    certificate.check = true ↔ certificate.ComputationallyCorrect := by
  constructor
  · intro accepted
    simp [check] at accepted
    exact ⟨accepted.1,
      allTrees_computational certificate.switchingGraphs accepted.2⟩
  · exact certificate.check_complete_computational

theorem check_iff_fuelCorrect (certificate : Certificate) :
    certificate.check = true ↔ certificate.FuelCorrect := by
  constructor
  · intro accepted
    simp [check] at accepted
    exact ⟨accepted.1,
      allTrees_fuel certificate.switchingGraphs accepted.2⟩
  · intro correct
    simp [check]
    exact ⟨correct.1,
      allTrees_complete_fuel certificate.switchingGraphs correct.2⟩

theorem check_iff_fuelDeclarativelyCorrect (certificate : Certificate) :
    certificate.check = true ↔ certificate.FuelDeclarativelyCorrect := by
  rw [certificate.check_iff_fuelCorrect,
    certificate.fuelCorrect_iff_declarative]

theorem FuelCorrect.toCorrect {certificate : Certificate}
    (correct : certificate.FuelCorrect) : certificate.Correct :=
  ⟨correct.1, by
    intro graph membership
    exact (correct.2 graph membership).toIsTree⟩

end Certificate
end ProofNetIR
