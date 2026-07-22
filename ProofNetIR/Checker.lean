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

def switchingGraphs (certificate : Certificate) : List Graph :=
  (enumerateChoices certificate.parChoices).map fun selected =>
    { vertexCount := certificate.formulas.size,
      edges := certificate.fixedEdges ++ selected }

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
          exact (Graph.isTree_iff head).mp accepted.1
      | inr memberTail =>
          exact ih accepted.2 graph memberTail

theorem allTrees_complete (graphs : List Graph)
    (correct : ∀ graph ∈ graphs, graph.IsTree) : allTrees graphs = true := by
  induction graphs with
  | nil => rfl
  | cons head tail ih =>
      simp [allTrees]
      constructor
      · exact (Graph.isTree_iff head).mpr (correct head (by simp))
      · exact ih (by
          intro graph membership
          exact correct graph (by simp [membership]))

/-- Any accepted executable certificate satisfies the declarative criterion. -/
theorem check_sound (certificate : Certificate) (accepted : certificate.check = true) :
    certificate.Correct := by
  simp [check] at accepted
  exact ⟨accepted.1, allTrees_sound certificate.switchingGraphs accepted.2⟩

/-- On the implemented fragment, the checker is also complete for `Correct`. -/
theorem check_complete (certificate : Certificate) (correct : certificate.Correct) :
    certificate.check = true := by
  simp [check]
  exact ⟨correct.1, allTrees_complete certificate.switchingGraphs correct.2⟩

theorem check_iff (certificate : Certificate) :
    certificate.check = true ↔ certificate.Correct :=
  ⟨certificate.check_sound, certificate.check_complete⟩

end Certificate
end ProofNetIR
