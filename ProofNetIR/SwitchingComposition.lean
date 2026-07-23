import ProofNetIR.GraphComposition
import ProofNetIR.Sequentialization

namespace ProofNetIR

namespace Edge

def shiftPair (offset : Nat) (choice : Edge × Edge) : Edge × Edge :=
  (choice.1.shift offset, choice.2.shift offset)

end Edge

namespace Certificate

namespace ChoiceSelection

/-- Split a switching selection over an appended choice list, preserving the
selected-edge occurrence order. -/
theorem splitAppend {firstChoices restChoices : List (Edge × Edge)}
    {selected : List Edge}
    (selection : ChoiceSelection (firstChoices ++ restChoices) selected) :
    ∃ firstSelected restSelected,
      ChoiceSelection firstChoices firstSelected ∧
      ChoiceSelection restChoices restSelected ∧
      selected = firstSelected ++ restSelected := by
  induction firstChoices generalizing selected with
  | nil => exact ⟨[], selected, .nil, selection, by simp⟩
  | cons choice rest ih =>
      rcases choice with ⟨left, right⟩
      cases selection with
      | left prior =>
          rcases ih prior with
            ⟨prefixSelected, suffixSelected, prefixSelection,
              suffixSelection, selectedEquation⟩
          exact ⟨left :: prefixSelected, suffixSelected,
            .left prefixSelection, suffixSelection, by simp [selectedEquation]⟩
      | right prior =>
          rcases ih prior with
            ⟨prefixSelected, suffixSelected, prefixSelection,
              suffixSelection, selectedEquation⟩
          exact ⟨right :: prefixSelected, suffixSelected,
            .right prefixSelection, suffixSelection, by simp [selectedEquation]⟩

/-- Invert a uniformly shifted switching selection. -/
theorem unshiftExists (offset : Nat) {choices : List (Edge × Edge)}
    {selected : List Edge}
    (selection : ChoiceSelection (choices.map (Edge.shiftPair offset)) selected) :
    ∃ original,
      ChoiceSelection choices original ∧
      selected = original.map (Edge.shift offset) := by
  induction choices generalizing selected with
  | nil =>
      cases selection
      exact ⟨[], .nil, by simp⟩
  | cons choice rest ih =>
      rcases choice with ⟨left, right⟩
      cases selection with
      | left prior =>
          rcases ih prior with ⟨original, originalSelection, equation⟩
          exact ⟨left :: original, .left originalSelection, by
            simp [equation]⟩
      | right prior =>
          rcases ih prior with ⟨original, originalSelection, equation⟩
          exact ⟨right :: original, .right originalSelection, by
            simp [equation]⟩

end ChoiceSelection

@[simp] theorem fixedEdges_appendParOccurrence
    (premise : Certificate) (left right : Formula)
    (leftRoot rightRoot : Vertex) (boundary : List Vertex) :
    (premise.appendParOccurrence left right leftRoot rightRoot boundary).fixedEdges =
      premise.fixedEdges := by
  simp [appendParOccurrence, fixedEdges]

@[simp] theorem parChoices_appendParOccurrence
    (premise : Certificate) (left right : Formula)
    (leftRoot rightRoot : Vertex) (boundary : List Vertex) :
    (premise.appendParOccurrence left right leftRoot rightRoot boundary).parChoices =
      premise.parChoices ++ [
        (Edge.mk leftRoot premise.formulas.size,
          Edge.mk rightRoot premise.formulas.size)] := by
  simp [appendParOccurrence, parChoices]

private def fixedLinkEdges : Link → List Edge
  | .axiom left right => [Edge.mk left right]
  | .tensor left right conclusion =>
      [Edge.mk left conclusion, Edge.mk right conclusion]
  | .par _ _ _ => []

private theorem fixedLinkEdges_shift (link : Link) (offset : Nat) :
    fixedLinkEdges (link.shift offset) =
      (fixedLinkEdges link).map (Edge.shift offset) := by
  cases link <;> simp [fixedLinkEdges, Link.shift, Edge.shift]

private theorem fixedEdges_shiftLinks (links : List Link) (offset : Nat) :
    (links.map (Link.shift offset)).flatMap fixedLinkEdges =
    (links.flatMap fixedLinkEdges).map (Edge.shift offset) := by
  induction links with
  | nil => simp
  | cons link rest ih =>
      simp [fixedLinkEdges_shift, ih, List.map_append]

private theorem fixedEdges_eq_links (certificate : Certificate) :
    certificate.fixedEdges = certificate.links.flatMap fixedLinkEdges := rfl

private def linkParChoice : Link → Option (Edge × Edge)
  | .par left right conclusion =>
      some (Edge.mk left conclusion, Edge.mk right conclusion)
  | _ => none

private theorem linkParChoice_shift (link : Link) (offset : Nat) :
    linkParChoice (link.shift offset) =
      (linkParChoice link).map (Edge.shiftPair offset) := by
  cases link <;>
    simp [linkParChoice, Link.shift, Edge.shift, Edge.shiftPair]

private theorem parChoices_shiftLinks (links : List Link) (offset : Nat) :
    (links.map (Link.shift offset)).filterMap linkParChoice =
    (links.filterMap linkParChoice).map (Edge.shiftPair offset) := by
  induction links with
  | nil => simp
  | cons link rest ih =>
      cases link <;>
        simp [linkParChoice, Link.shift, Edge.shiftPair, Edge.shift, ih]

private theorem parChoices_eq_links (certificate : Certificate) :
    certificate.parChoices = certificate.links.filterMap linkParChoice := rfl

@[simp] theorem fixedEdges_appendTensorOccurrence
    (leftPremise rightPremise : Certificate) (left right : Formula)
    (leftRoot rightRoot : Vertex) (boundary : List Vertex) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot boundary).fixedEdges =
      leftPremise.fixedEdges ++
        rightPremise.fixedEdges.map (Edge.shift leftPremise.formulas.size) ++ [
          Edge.mk leftRoot (leftPremise.formulas.size + rightPremise.formulas.size),
          Edge.mk (rightRoot + leftPremise.formulas.size)
            (leftPremise.formulas.size + rightPremise.formulas.size)] := by
  rw [fixedEdges_eq_links
      (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
        rightRoot boundary),
    fixedEdges_eq_links leftPremise, fixedEdges_eq_links rightPremise]
  simp only [appendTensorOccurrence]
  rw [List.flatMap_append, List.flatMap_append]
  rw [fixedEdges_shiftLinks]
  simp [fixedLinkEdges]

@[simp] theorem parChoices_appendTensorOccurrence
    (leftPremise rightPremise : Certificate) (left right : Formula)
    (leftRoot rightRoot : Vertex) (boundary : List Vertex) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot boundary).parChoices =
      leftPremise.parChoices ++
        rightPremise.parChoices.map
          (Edge.shiftPair leftPremise.formulas.size) := by
  rw [parChoices_eq_links
      (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
        rightRoot boundary),
    parChoices_eq_links leftPremise, parChoices_eq_links rightPremise]
  simp only [appendTensorOccurrence]
  rw [List.filterMap_append, List.filterMap_append]
  rw [parChoices_shiftLinks]
  simp [linkParChoice]

/-- The graph-theoretic half of declarative correctness, isolated from
certificate ownership and formula typing. -/
def SwitchingCorrect (certificate : Certificate) : Prop :=
  ∀ graph, certificate.SwitchingGraph graph → graph.IsTree

/-- Switching correctness is closed under the par construction when both
premise roots are existing vertices. Every new switching simply adjoins the
fresh conclusion as a leaf through one of the two par premises. -/
theorem SwitchingCorrect.appendParOccurrence
    {premise : Certificate} (correct : premise.SwitchingCorrect)
    (left right : Formula) {leftRoot rightRoot : Vertex}
    (leftRootInBounds : leftRoot < premise.formulas.size)
    (rightRootInBounds : rightRoot < premise.formulas.size)
    (boundary : List Vertex) :
    (premise.appendParOccurrence left right leftRoot rightRoot
      boundary).SwitchingCorrect := by
  intro graph switching
  rcases switching with ⟨selected, selection, rfl⟩
  rw [parChoices_appendParOccurrence] at selection
  rcases selection.splitAppend with
    ⟨premiseSelected, finalSelected, premiseSelection,
      finalSelection, selectedEquation⟩
  let premiseGraph := premise.graphForSelection premiseSelected
  have premiseTree : premiseGraph.IsTree :=
    correct premiseGraph ⟨premiseSelected, premiseSelection, rfl⟩
  cases finalSelection with
  | left prior =>
      cases prior
      have added := premiseTree.addLeaf leftRootInBounds
      simpa [graphForSelection, premiseGraph, Graph.addLeaf,
        selectedEquation, List.append_assoc] using added
  | right prior =>
      cases prior
      have added := premiseTree.addLeaf rightRootInBounds
      simpa [graphForSelection, premiseGraph, Graph.addLeaf,
        selectedEquation, List.append_assoc] using added

private theorem perm_tensor_edge_blocks
    [BEq α] [LawfulBEq α]
    (leftFixed rightFixed terminal leftSelected rightSelected : List α) :
    ((leftFixed ++ leftSelected) ++ (rightFixed ++ rightSelected) ++ terminal).Perm
      ((leftFixed ++ rightFixed ++ terminal) ++
        (leftSelected ++ rightSelected)) := by
  rw [List.perm_iff_count]
  intro value
  simp only [List.count_append]
  omega

/-- Switching correctness is closed under the tensor construction when the
selected premise roots are in bounds. A new switching is an edge-order
permutation of two disjoint premise switching trees joined through the fresh
tensor conclusion. -/
theorem SwitchingCorrect.appendTensorOccurrence
    {leftPremise rightPremise : Certificate}
    (leftCorrect : leftPremise.SwitchingCorrect)
    (rightCorrect : rightPremise.SwitchingCorrect)
    (left right : Formula) {leftRoot rightRoot : Vertex}
    (leftRootInBounds : leftRoot < leftPremise.formulas.size)
    (rightRootInBounds : rightRoot < rightPremise.formulas.size)
    (boundary : List Vertex) :
    (leftPremise.appendTensorOccurrence rightPremise left right
      leftRoot rightRoot boundary).SwitchingCorrect := by
  intro graph switching
  rcases switching with ⟨selected, selection, rfl⟩
  rw [parChoices_appendTensorOccurrence] at selection
  rcases selection.splitAppend with
    ⟨leftSelected, shiftedRightSelected, leftSelection,
      shiftedRightSelection, selectedEquation⟩
  rcases shiftedRightSelection.unshiftExists leftPremise.formulas.size with
    ⟨rightSelected, rightSelection, shiftedRightEquation⟩
  let leftGraph := leftPremise.graphForSelection leftSelected
  let rightGraph := rightPremise.graphForSelection rightSelected
  have leftTree : leftGraph.IsTree :=
    leftCorrect leftGraph ⟨leftSelected, leftSelection, rfl⟩
  have rightTree : rightGraph.IsTree :=
    rightCorrect rightGraph ⟨rightSelected, rightSelection, rfl⟩
  have joinedTree := leftTree.tensorJoin rightTree
    leftRootInBounds rightRootInBounds
  apply joinedTree.permuteEdges
  · simp [Graph.tensorJoin, leftGraph, rightGraph, graphForSelection]
  · simpa [Graph.tensorJoin, leftGraph, rightGraph, graphForSelection,
      selectedEquation, shiftedRightEquation, List.map_append,
      List.append_assoc] using
        (perm_tensor_edge_blocks leftPremise.fixedEdges
          (rightPremise.fixedEdges.map
            (Edge.shift leftPremise.formulas.size))
          [Edge.mk leftRoot
              (leftPremise.formulas.size + rightPremise.formulas.size),
            Edge.mk (rightRoot + leftPremise.formulas.size)
              (leftPremise.formulas.size + rightPremise.formulas.size)]
          leftSelected
          (rightSelected.map (Edge.shift leftPremise.formulas.size)))

end Certificate

end ProofNetIR
