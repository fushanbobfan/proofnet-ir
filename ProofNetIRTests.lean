import ProofNetIR

open ProofNetIR

namespace ProofNetIRTests

def p : Formula := .atom "p" true
def pDual : Formula := p.dual
def q : Formula := .atom "q" true
def qDual : Formula := q.dual

example : p.dual.dual = p := by simp

def indexedParallelGraph : Graph where
  vertexCount := 2
  edges := [{ first := 0, second := 1 }, { first := 0, second := 1 }]

def parallelDirectedZero : indexedParallelGraph.DirectedEdge where
  index := 0
  edge := { first := 0, second := 1 }
  lookup := rfl
  forward := true

def parallelDirectedOne : indexedParallelGraph.DirectedEdge where
  index := 1
  edge := { first := 0, second := 1 }
  lookup := rfl
  forward := true

example : parallelDirectedZero.edge = parallelDirectedOne.edge := rfl
example : parallelDirectedZero.index ≠ parallelDirectedOne.index := by decide

example : indexedParallelGraph.EdgeWalk 0 [parallelDirectedZero] 1 := by
  exact .step (.refl 0) parallelDirectedZero rfl rfl

example : indexedParallelGraph.Walk 0 1 := by
  exact (show indexedParallelGraph.EdgeWalk 0 [parallelDirectedZero] 1 from
    .step (.refl 0) parallelDirectedZero rfl rfl).toWalk

example : indexedParallelGraph.EdgeWalk 1 [parallelDirectedZero.reverse] 0 := by
  have forward : indexedParallelGraph.EdgeWalk 0 [parallelDirectedZero] 1 :=
    .step (.refl 0) parallelDirectedZero rfl rfl
  simpa [Graph.EdgeWalk.reverseTraversal] using forward.reverse

def indexedParallelCycle : indexedParallelGraph.EdgeSimpleCycle where
  start := 0
  traversed := [parallelDirectedZero, parallelDirectedOne.reverse]
  nonempty := by simp
  walk := by
    apply Graph.EdgeWalk.step
      (Graph.EdgeWalk.step (.refl 0) parallelDirectedZero rfl rfl)
      parallelDirectedOne.reverse
    · rfl
    · rfl
  edgeIndicesNodup := by decide
  interiorNodup := by decide

example : indexedParallelCycle.traversed.map (·.index) = [0, 1] := rfl
example : indexedParallelCycle.traversed.length ≤
    indexedParallelGraph.edges.length := indexedParallelCycle.length_le_edges

def mixedFormula : Formula := .par (.tensor p q) (.atom "r" true)

example : Derivation [mixedFormula, mixedFormula.dual] :=
  Derivation.identity mixedFormula

example : identityCertificate (.tensor p q) = canonicalCertificate "p" "q" := by
  native_decide

example : (identityCertificate mixedFormula).wellFormed = true := by
  native_decide

example : (identityCertificate mixedFormula).switchingGraphs.length = 4 := by
  native_decide

example : (identityCertificate mixedFormula).check = true := by
  native_decide

example : (identityCertificate mixedFormula).FuelCorrect :=
  (identityCertificate mixedFormula).check_iff_fuelCorrect.mp (by native_decide)

example :
    (reconstructIdentity? (identityCertificate mixedFormula) mixedFormula).isSome =
      true := by
  native_decide

example :
    (reconstructIdentity?
      (Mutation.dropFirstLink.apply (identityCertificate mixedFormula))
      mixedFormula).isSome = false := by
  native_decide

def generatedDepthTwo : List Formula := Formula.enumerate ["p"] 2

example : generatedDepthTwo.length = 210 := by native_decide
example : generatedDepthTwo.all (fun formula =>
    (identityCertificate formula).check) = true := by
  native_decide

def generatedDerivationTrees : List CutFreeDerivation :=
  (List.range 250).map fun seed => CutFreeDerivation.generate seed 2

example : generatedDerivationTrees.all (fun tree => tree.infer?.isSome) = true := by
  native_decide

example : generatedDerivationTrees.all (fun tree =>
    tree.desequentializeChecked?.isSome) = true := by
  native_decide

example : generatedDerivationTrees.all (fun tree => tree.elaborate?.isSome) = true := by
  native_decide

def generatedJsonRoundTrips : Bool :=
  generatedDerivationTrees.all fun tree =>
    match tree.desequentialize? with
    | none => false
    | some certificate =>
        match Certificate.checkedFromString certificate.canonicalString with
        | .error _ => false
        | .ok checked => checked.certificate == certificate.canonicalize

example : generatedJsonRoundTrips = true := by native_decide

def generatedV03JsonRoundTrips : Bool :=
  generatedDerivationTrees.all fun tree =>
    match tree.desequentialize? with
    | none => false
    | some certificate =>
        match Certificate.checkedFromString
            certificate.equivalenceCanonicalString with
        | .error _ => false
        | .ok checked =>
            checked.certificate == certificate.equivalenceCanonicalize

example : generatedV03JsonRoundTrips = true := by native_decide

example : generatedDerivationTrees.all (fun tree =>
    match tree.desequentialize? with
    | some certificate => certificate.check
    | none => false) = true := by
  native_decide

def generatedTerminalParPeelsAccepted : Bool :=
  generatedDerivationTrees.all fun tree =>
    match tree.desequentialize? with
    | none => false
    | some certificate =>
        certificate.terminalPars.all fun candidate =>
          let (left, right, conclusion) := candidate
          (certificate.peelTerminalParChecked?
            left right conclusion).isSome

/-- A broad generated regression for the terminal-par inverse operation. The
general preservation theorem remains separate and is not inferred from this
test. -/
example : generatedTerminalParPeelsAccepted = true := by native_decide

def hasCheckedInverseStep (certificate : Certificate) : Bool :=
  certificate.terminalPars.any (fun candidate =>
    let (left, right, conclusion) := candidate
    (certificate.peelTerminalParChecked? left right conclusion).isSome) ||
  certificate.terminalTensors.any (fun candidate =>
    let (left, right, conclusion) := candidate
    (certificate.splitTerminalTensorChecked? left right conclusion).isSome)

def generatedInverseStepsAvailable : Bool :=
  generatedDerivationTrees.all fun tree =>
    match tree.desequentialize? with
    | none => false
    | some certificate => hasCheckedInverseStep certificate

/-- Every non-axiom generated fixture exposes a checker-accepted inverse par
or splitting-tensor step. This exercises discovery but does not replace the
universal splitting theorem. -/
example : generatedInverseStepsAvailable = true := by native_decide

/-- The canonical net for `⊢ p ⊗ q, p⊥ ⅋ q⊥`. -/
def canonical : Certificate where
  formulas := #[p, pDual, q, qDual, .tensor p q, .par pDual qDual]
  links := [
    .axiom 0 1,
    .axiom 2 3,
    .tensor 0 2 4,
    .par 1 3 5
  ]
  conclusions := [4, 5]

def canonicalParLeftIn : canonical.fullGraph.DirectedEdge where
  index := 4
  edge := { first := 1, second := 5 }
  lookup := rfl
  forward := true

def canonicalParRightIn : canonical.fullGraph.DirectedEdge where
  index := 5
  edge := { first := 3, second := 5 }
  lookup := rfl
  forward := true

theorem canonicalFullLeftSelection :
    Certificate.FullSwitchingSelection canonical.links
    [{ first := 1, second := 5 }]
    [{ first := 0, second := 1 },
     { first := 2, second := 3 },
     { first := 0, second := 4 },
     { first := 2, second := 4 },
     { first := 1, second := 5 }]
    [true, true, true, true, true, false] :=
  .axiom (.axiom (.tensor (.parLeft .nil)))

example : Certificate.ChoiceSelection canonical.parChoices
    [{ first := 1, second := 5 }] :=
  canonicalFullLeftSelection.choiceSelection
example : Certificate.retainByMask canonical.fullEdges
    [true, true, true, true, true, false] =
      [{ first := 0, second := 1 },
       { first := 2, second := 3 },
       { first := 0, second := 4 },
       { first := 2, second := 4 },
       { first := 1, second := 5 }] := by native_decide
example : [true, true, true, true, true, false].length =
    canonical.fullEdges.length := by
  simpa using canonicalFullLeftSelection.mask_length
example : ∃ retained mask,
    Certificate.FullSwitchingSelection canonical.links
      [{ first := 1, second := 5 }] retained mask ∧
      retained.Perm
        (canonical.graphForSelection [{ first := 1, second := 5 }]).edges :=
  canonical.occurrenceSwitching_exists
    canonicalFullLeftSelection.choiceSelection

example : canonical.fullEdgeParTargets =
    [none, none, none, none, some 5, some 5] := by native_decide
example : canonical.fullEdgeAnnotations.map Prod.fst = canonical.fullEdges :=
  canonical.fullEdgeAnnotations_edges
example : canonical.fullEdgeAnnotations.map Prod.snd =
    canonical.fullEdgeParTargets := canonical.fullEdgeAnnotations_parTargets
example : canonical.incidenceColor canonicalParLeftIn =
    .par 5 := by native_decide
example : canonical.incidenceColor canonicalParRightIn =
    .par 5 := by native_decide
example : canonical.incidenceColor canonicalParLeftIn = .par 5 ↔
    canonicalParLeftIn.forward = true ∧
      canonical.fullEdgeParTargets[canonicalParLeftIn.index]? =
        some (some 5) :=
  canonical.incidenceColor_eq_par_iff canonicalParLeftIn 5
example : ∃ leftIncidence rightIncidence : canonical.fullGraph.DirectedEdge,
    leftIncidence.source = 1 ∧ leftIncidence.target = 5 ∧
      rightIncidence.source = 3 ∧ rightIncidence.target = 5 ∧
      canonical.incidenceColor leftIncidence = .par 5 ∧
      canonical.incidenceColor rightIncidence = .par 5 :=
  canonical.par_incidenceColors_exist (by simp [canonical])
example : canonical.incidenceColor canonicalParLeftIn.reverse =
    .unique 4 false := by native_decide
example : canonical.Cusp canonicalParLeftIn canonicalParRightIn.reverse := by
  rfl
example : canonical.Cusp canonicalParRightIn canonicalParLeftIn.reverse :=
  (canonical.cusp_reverse_iff canonicalParLeftIn
    canonicalParRightIn.reverse).mp (by rfl)

example : canonical.wellFormed = true := by native_decide
example : canonical.StructurallyWellFormed :=
  canonical.wellFormed_iff_structurallyWellFormed.mp (by native_decide)
example : canonical.switchingGraphs.length = 2 := by native_decide
example : canonical.check = true := by native_decide
example : canonical.Correct := canonical.check_sound (by native_decide)
example : canonical.check = true ↔ canonical.Correct :=
  canonical.check_iff_correct
example : canonical.DeclarativelyCorrect :=
  canonical.check_sound_declarative (by native_decide)
example : canonical.check = true ↔ canonical.DeclarativelyCorrect :=
  canonical.check_iff_declarativelyCorrect
example : canonical.FuelCorrect :=
  canonical.check_iff_fuelCorrect.mp (by native_decide)
example : canonical.Correct ↔ canonical.FuelCorrect :=
  canonical.correct_iff_fuelCorrect
example : canonical.FuelDeclarativelyCorrect :=
  canonical.check_iff_fuelDeclarativelyCorrect.mp (by native_decide)
example : canonical.DeclarativelyCorrect ↔
    canonical.FuelDeclarativelyCorrect :=
  canonical.declarativelyCorrect_iff_fuelDeclarativelyCorrect

def canonicalRuleTree : CutFreeDerivation :=
  .par 1 1 (.tensor 0 0 (.axiom "p" true) (.axiom "q" true))

def canonicalSequentialization : SequentializationResult canonical where
  tree := canonicalRuleTree
  sequent := [
    .tensor (.atom "p" true) (.atom "q" true),
    .par (.atom "p" false) (.atom "q" false)]
  output := canonical
  inferred := by native_decide
  desequentialized := by native_decide
  outputLabels := by native_decide
  equivalent := .refl canonical

example : Nonempty (Derivation canonicalSequentialization.sequent) :=
  canonicalSequentialization.kernelDerivation
example : canonical.conclusionFormulas? =
    some canonicalSequentialization.sequent :=
  canonicalSequentialization.inputLabels
example : canonicalSequentialization.output.check = true :=
  canonicalSequentialization.outputAccepted (by native_decide)
example : (1, 3, 5) ∈ canonical.terminalPars := by native_decide
example : canonical.TerminalPar 1 3 5 :=
  (canonical.mem_terminalPars_iff 1 3 5).mp (by native_decide)
example : canonical.TerminalTensor 0 2 4 :=
  (canonical.mem_terminalTensors_iff 0 2 4).mp (by native_decide)
example : ¬canonical.SplittingTensor 0 2 4 := by
  intro splitting
  have rejected :=
    (Certificate.TerminalTensor.splitting_iff_reachability_rejected
      (canonical.wellFormed_iff_structurallyWellFormed.mp (by native_decide))
      (canonical.mem_terminalTensors_iff 0 2 4 |>.mp (by native_decide))).mp
      splitting
  have reached :
      ((canonical.fullGraphWithoutVertex 4).closureN
        canonical.formulas.size [0]).contains 2 = true := by native_decide
  rw [reached] at rejected
  cases rejected
example : ∀ graph, canonical.SwitchingGraph graph → graph.Leaf 5 := by
  intro graph switching
  rcases switching with ⟨selected, selection, rfl⟩
  exact Certificate.TerminalPar.graphForSelection_leaf
    (canonical.wellFormed_iff_structurallyWellFormed.mp (by native_decide))
    (canonical.mem_terminalPars_iff 1 3 5 |>.mp (by native_decide))
    selection
example : ∀ graph, canonical.SwitchingGraph graph →
    graph.incidentCount 4 = 2 := by
  intro graph switching
  rcases switching with ⟨selected, selection, rfl⟩
  exact Certificate.TerminalTensor.graphForSelection_incidentCount
    (canonical.wellFormed_iff_structurallyWellFormed.mp (by native_decide))
    (canonical.mem_terminalTensors_iff 0 2 4 |>.mp (by native_decide))
    selection

def canonicalParPremise : Certificate where
  formulas := #[p, pDual, q, qDual, .tensor p q]
  links := [
    .axiom 0 1,
    .axiom 2 3,
    .tensor 0 2 4]
  conclusions := [4, 1, 3]

def canonicalLeftTensorPremise : Certificate where
  formulas := #[p, pDual]
  links := [.axiom 0 1]
  conclusions := [1, 0]

def canonicalRightTensorPremise : Certificate where
  formulas := #[q, qDual]
  links := [.axiom 0 1]
  conclusions := [1, 0]

example : canonicalParPremise.SplittingTensor 0 2 4 := by
  apply (Certificate.TerminalTensor.splitting_iff_reachability_rejected
    (canonicalParPremise.wellFormed_iff_structurallyWellFormed.mp
      (by native_decide))
    (canonicalParPremise.mem_terminalTensors_iff 0 2 4 |>.mp
      (by native_decide))).mpr
  native_decide

example : ∃ left right conclusion,
    canonicalParPremise.TerminalPar left right conclusion ∨
      canonicalParPremise.TerminalTensor left right conclusion := by
  apply Certificate.terminalConnective_exists
    (canonicalParPremise.wellFormed_iff_structurallyWellFormed.mp
      (by native_decide))
  exact ⟨.tensor 0 2 4, by native_decide, rfl⟩

example : ∃ leftCertificate rightCertificate,
    canonicalParPremise.splitTerminalTensorCandidate? 0 2 4 =
      some (leftCertificate, rightCertificate) :=
  Certificate.splitTerminalTensorCandidate?_eq_some_exists
    (canonicalParPremise.wellFormed_iff_structurallyWellFormed.mp
      (by native_decide))
    (by
      apply (Certificate.TerminalTensor.splitting_iff_reachability_rejected
        (canonicalParPremise.wellFormed_iff_structurallyWellFormed.mp
          (by native_decide))
        (canonicalParPremise.mem_terminalTensors_iff 0 2 4 |>.mp
          (by native_decide))).mpr
      native_decide)

example : ∃ leftCertificate rightCertificate,
    canonicalParPremise.splitTerminalTensorCandidate? 0 2 4 =
        some (leftCertificate, rightCertificate) ∧
      leftCertificate.StructurallyWellFormed ∧
      rightCertificate.StructurallyWellFormed :=
  Certificate.splitTerminalTensorCandidate?_structural_exists
    (canonicalParPremise.wellFormed_iff_structurallyWellFormed.mp
      (by native_decide))
    (by
      apply (Certificate.TerminalTensor.splitting_iff_reachability_rejected
        (canonicalParPremise.wellFormed_iff_structurallyWellFormed.mp
          (by native_decide))
        (canonicalParPremise.mem_terminalTensors_iff 0 2 4 |>.mp
          (by native_decide))).mpr
      native_decide)

example : canonicalParPremise.splitTerminalTensorCandidate? 0 2 4 =
    some (canonicalLeftTensorPremise, canonicalRightTensorPremise) := by
  native_decide

example {graph : Graph}
    (switching : canonicalLeftTensorPremise.SwitchingGraph graph) :
    ∃ inputGraph,
      canonicalParPremise.SwitchingGraph inputGraph ∧
      graph = inputGraph.restrictTo
        (canonicalParPremise.tensorLeftVertices 0 4) := by
  apply Certificate.TerminalTensor.restrictTo?_leftSwitchingLift
    (canonicalParPremise.wellFormed_iff_structurallyWellFormed.mp
      (by native_decide))
    (by
      apply (Certificate.TerminalTensor.splitting_iff_reachability_rejected
        (canonicalParPremise.wellFormed_iff_structurallyWellFormed.mp
          (by native_decide))
        (canonicalParPremise.mem_terminalTensors_iff 0 2 4 |>.mp
          (by native_decide))).mpr
      native_decide)
    (by native_decide)
    switching

example {selected : List Edge}
    (selection : Certificate.ChoiceSelection
      canonicalParPremise.parChoices selected)
    (tree : (canonicalParPremise.graphForSelection selected).IsTree) :
    ((canonicalParPremise.graphForSelection selected).restrictTo
      (canonicalParPremise.tensorLeftVertices 0 4)).Connected := by
  exact Certificate.TerminalTensor.graph_restrictTo_left_connected
    (canonicalParPremise.wellFormed_iff_structurallyWellFormed.mp
      (by native_decide))
    (by
      apply (Certificate.TerminalTensor.splitting_iff_reachability_rejected
        (canonicalParPremise.wellFormed_iff_structurallyWellFormed.mp
          (by native_decide))
        (canonicalParPremise.mem_terminalTensors_iff 0 2 4 |>.mp
          (by native_decide))).mpr
      native_decide)
    selection tree

example {selected : List Edge}
    (selection : Certificate.ChoiceSelection
      canonicalParPremise.parChoices selected)
    (tree : (canonicalParPremise.graphForSelection selected).IsTree) :
    ((canonicalParPremise.graphForSelection selected).restrictTo
        (canonicalParPremise.tensorLeftVertices 0 4)).IsTree ∧
      ((canonicalParPremise.graphForSelection selected).restrictTo
        (canonicalParPremise.tensorRightVertices 0 4)).IsTree := by
  exact Certificate.TerminalTensor.graph_restrictTo_trees
    (canonicalParPremise.wellFormed_iff_structurallyWellFormed.mp
      (by native_decide))
    (by
      apply (Certificate.TerminalTensor.splitting_iff_reachability_rejected
        (canonicalParPremise.wellFormed_iff_structurallyWellFormed.mp
          (by native_decide))
        (canonicalParPremise.mem_terminalTensors_iff 0 2 4 |>.mp
          (by native_decide))).mpr
      native_decide)
    selection tree

example : Certificate.TerminalTensorReduction canonicalParPremise
    canonicalLeftTensorPremise canonicalRightTensorPremise 0 2 4 := by
  exact Certificate.splitTerminalTensorCandidate?_reduction
    (canonicalParPremise.wellFormed_iff_structurallyWellFormed.mp
      (by native_decide))
    (by
      apply (Certificate.TerminalTensor.splitting_iff_reachability_rejected
        (canonicalParPremise.wellFormed_iff_structurallyWellFormed.mp
          (by native_decide))
        (canonicalParPremise.mem_terminalTensors_iff 0 2 4 |>.mp
          (by native_decide))).mpr
      native_decide)
    (by native_decide)

example : canonicalLeftTensorPremise.DeclarativelyCorrect ∧
    canonicalRightTensorPremise.DeclarativelyCorrect := by
  have reduction : Certificate.TerminalTensorReduction canonicalParPremise
      canonicalLeftTensorPremise canonicalRightTensorPremise 0 2 4 := by
    exact Certificate.splitTerminalTensorCandidate?_reduction
      (canonicalParPremise.wellFormed_iff_structurallyWellFormed.mp
        (by native_decide))
      (by
        apply (Certificate.TerminalTensor.splitting_iff_reachability_rejected
          (canonicalParPremise.wellFormed_iff_structurallyWellFormed.mp
            (by native_decide))
          (canonicalParPremise.mem_terminalTensors_iff 0 2 4 |>.mp
            (by native_decide))).mpr
        native_decide)
      (by native_decide)
  exact reduction.declarativelyCorrect
    (canonicalParPremise.check_iff_declarativelyCorrect.mp (by native_decide))

example : ∃ premises,
    canonicalParPremise.splitTerminalTensorChecked? 0 2 4 = some premises := by
  exact Certificate.splitTerminalTensorChecked?_eq_some_exists
    (canonicalParPremise.wellFormed_iff_structurallyWellFormed.mp
      (by native_decide))
    (by
      apply (Certificate.TerminalTensor.splitting_iff_reachability_rejected
        (canonicalParPremise.wellFormed_iff_structurallyWellFormed.mp
          (by native_decide))
        (canonicalParPremise.mem_terminalTensors_iff 0 2 4 |>.mp
          (by native_decide))).mpr
      native_decide)
    (by native_decide)

example : canonical.peelTerminalParCandidate? 1 3 5 =
    some canonicalParPremise := by native_decide
example : canonical.peelTerminalPar 1 3 5 = canonicalParPremise := by
  native_decide
example : (canonical.peelTerminalPar 1 3 5).conclusions.Nodup :=
  Certificate.peelTerminalPar_conclusions_nodup
    (canonical.wellFormed_iff_structurallyWellFormed.mp (by native_decide))
    (canonical.mem_terminalPars_iff 1 3 5 |>.mp (by native_decide))
example : ∀ link ∈ (canonical.peelTerminalPar 1 3 5).links,
    (canonical.peelTerminalPar 1 3 5).LinkWellFormed link :=
  Certificate.peelTerminalPar_links_wellFormed
    (canonical.wellFormed_iff_structurallyWellFormed.mp (by native_decide))
    (canonical.mem_terminalPars_iff 1 3 5 |>.mp (by native_decide))
example : canonicalParPremise.StructurallyWellFormed := by
  have preserved := Certificate.peelTerminalPar_structurallyWellFormed
    (canonical.wellFormed_iff_structurallyWellFormed.mp (by native_decide))
    (canonical.mem_terminalPars_iff 1 3 5 |>.mp (by native_decide))
  simpa [show canonical.peelTerminalPar 1 3 5 = canonicalParPremise by
    native_decide] using preserved
example : Certificate.TerminalParReduction canonical canonicalParPremise 5 := by
  simpa [show canonical.peelTerminalPar 1 3 5 = canonicalParPremise by
    native_decide] using Certificate.peelTerminalPar_reduction
      (canonical.wellFormed_iff_structurallyWellFormed.mp (by native_decide))
      (canonical.mem_terminalPars_iff 1 3 5 |>.mp (by native_decide))
example : canonicalParPremise.check = true := by native_decide
example : (canonical.peelTerminalParChecked? 1 3 5).isSome = true := by
  native_decide
example : canonical.peelTerminalParCandidate? 0 2 4 = none := by
  native_decide

def canonicalLeftAxiomPremise : Certificate where
  formulas := #[p, pDual]
  links := [.axiom 0 1]
  conclusions := [1, 0]

def canonicalRightAxiomPremise : Certificate where
  formulas := #[q, qDual]
  links := [.axiom 0 1]
  conclusions := [1, 0]

example : canonical.splitTerminalTensorCandidate? 0 2 4 = none := by
  native_decide
example : canonicalParPremise.splitTerminalTensorCandidate? 0 2 4 =
    some (canonicalLeftAxiomPremise, canonicalRightAxiomPremise) := by
  native_decide
example : canonicalLeftAxiomPremise.check = true := by native_decide
example : canonicalRightAxiomPremise.check = true := by native_decide
example :
    (canonicalParPremise.splitTerminalTensorChecked? 0 2 4).isSome = true := by
  native_decide

example : canonical = canonicalCertificate "p" "q" := by native_decide

def swapCanonicalZeroOne : VertexRenaming canonical.formulas.size :=
  VertexRenaming.swap canonical.formulas.size 0 1 (by decide) (by decide)

def reindexedCanonical : Certificate :=
  canonical.reindex swapCanonicalZeroOne

example : reindexedCanonical ≠ canonical := by native_decide
example : reindexedCanonical.formula? 1 = canonical.formula? 0 := by
  exact canonical.reindex_formula?_forward swapCanonicalZeroOne 0
example : reindexedCanonical.check = true := by native_decide
example : reindexedCanonical.reindex
    (canonical.inverseReindexing swapCanonicalZeroOne) = canonical :=
  canonical.reindex_inverse swapCanonicalZeroOne
example : canonical.ReindexEquivalent reindexedCanonical :=
  ⟨swapCanonicalZeroOne, rfl⟩
example : reindexedCanonical.ReindexEquivalent canonical :=
  (show canonical.ReindexEquivalent reindexedCanonical from
    ⟨swapCanonicalZeroOne, rfl⟩).symm
example : canonical.check = reindexedCanonical.check :=
  (show canonical.ReindexEquivalent reindexedCanonical from
    ⟨swapCanonicalZeroOne, rfl⟩).check_eq
example : canonical.DeclarativelyCorrect ↔
    reindexedCanonical.DeclarativelyCorrect :=
  (show canonical.ReindexEquivalent reindexedCanonical from
    ⟨swapCanonicalZeroOne, rfl⟩).declarativelyCorrect_iff
example : canonical.canonicalString ≠ reindexedCanonical.canonicalString := by
  native_decide
example : canonical.equivalenceCanonicalize.check = true :=
  canonical.equivalenceCanonicalize_check_of_check (by native_decide)
example : canonical.ReindexEquivalent canonical.equivalenceCanonicalize :=
  (show canonical.StructurallyWellFormed from
    canonical.wellFormed_iff_structurallyWellFormed.mp (by native_decide))
    |>.equivalenceCanonicalize_reindexEquivalent
example : canonical.equivalenceCanonicalString =
    reindexedCanonical.equivalenceCanonicalString := by native_decide
example : Certificate.reindexEquivalent? canonical reindexedCanonical = true := by
  native_decide
example : Certificate.reindexEquivalent? canonical reindexedCanonical = true ↔
    canonical.ReindexEquivalent reindexedCanonical :=
  Certificate.reindexEquivalent?_eq_true_iff_of_check
    (by native_decide) (by native_decide)
example : (canonical.reindex swapCanonicalZeroOne).equivalenceCanonicalString =
    canonical.equivalenceCanonicalString :=
  canonical.equivalenceCanonicalString_reindex swapCanonicalZeroOne

example (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).check = certificate.check :=
  certificate.check_reindex r

def scrambledCanonical : Certificate :=
  { canonical with
    links := canonical.links.reverse
    conclusions := canonical.conclusions.reverse }

/-- This differs only in link storage order. It is checker-equivalent but not
related by the deliberately narrower, order-preserving reindexing relation. -/
def linkScrambledCanonical : Certificate :=
  { canonical with links := canonical.links.reverse }

example : canonical.LinkPermutationEquivalent linkScrambledCanonical := by
  refine ⟨rfl, ?_, rfl⟩
  simpa [linkScrambledCanonical] using
    (List.reverse_perm canonical.links).symm
example : linkScrambledCanonical.check = true := by native_decide
example : canonical.check = linkScrambledCanonical.check :=
  (show canonical.LinkPermutationEquivalent linkScrambledCanonical from by
    refine ⟨rfl, ?_, rfl⟩
    simpa [linkScrambledCanonical] using
      (List.reverse_perm canonical.links).symm).check_eq
example : canonical.ProofNetEquivalent linkScrambledCanonical :=
  (show canonical.LinkPermutationEquivalent linkScrambledCanonical from by
    refine ⟨rfl, ?_, rfl⟩
    simpa [linkScrambledCanonical] using
      (List.reverse_perm canonical.links).symm).toProofNetEquivalent
example : ¬ canonical.ReindexEquivalent linkScrambledCanonical := by
  rw [← Certificate.reindexEquivalent?_eq_true_iff_of_check
    (left := canonical) (right := linkScrambledCanonical)
    (by native_decide) (by native_decide)]
  native_decide

example : scrambledCanonical.canonicalize.check = true := by native_decide
example : scrambledCanonical.canonicalString = canonical.canonicalString := by
  native_decide
example : scrambledCanonical.StructurallyWellFormed :=
  scrambledCanonical.wellFormed_iff_structurallyWellFormed.mp (by native_decide)
example : Certificate.reindexEquivalent? canonical scrambledCanonical = false := by
  native_decide

def parsedCanonicalMatches : Bool :=
  match Certificate.fromString canonical.canonicalString with
  | .ok certificate => certificate == canonical
  | .error _ => false

example : parsedCanonicalMatches = true := by native_decide

example :
    (Certificate.checkedFromString canonical.canonicalString).isOk = true := by
  native_decide

def parsedEquivalenceCanonicalMatches : Bool :=
  match Certificate.fromString canonical.equivalenceCanonicalString with
  | .ok certificate => certificate == canonical.equivalenceCanonicalize
  | .error _ => false

example : parsedEquivalenceCanonicalMatches = true := by native_decide

example :
    (Certificate.checkedFromString
      canonical.equivalenceCanonicalString).isOk = true := by
  native_decide

def migratedCanonicalMatches : Bool :=
  match Certificate.migrateV02StringToV03 canonical.canonicalString with
  | .ok output => output == canonical.equivalenceCanonicalString
  | .error _ => false

example : migratedCanonicalMatches = true := by native_decide

def unsupportedCanonicalizationJson : Lean.Json :=
  let normalized := canonical.equivalenceCanonicalize
  Lean.Json.mkObj [
    ("version", "0.3"),
    ("canonical", true),
    ("canonicalization", "unknown"),
    ("formulas", .arr (normalized.formulas.map Certificate.formulaJson)),
    ("links", .arr (normalized.links.toArray.map Certificate.linkJson)),
    ("conclusions", .arr (normalized.conclusions.toArray.map
      (fun value : Vertex => .num (Lean.JsonNumber.fromNat value))))]

def unsupportedCanonicalizationDiagnosticMatches : Bool :=
  match Certificate.fromJson unsupportedCanonicalizationJson with
  | .error error => error == {
      path := "$.canonicalization"
      message := "unsupported canonicalization 'unknown'" }
  | .ok _ => false

example : unsupportedCanonicalizationDiagnosticMatches = true := by
  native_decide

def rejectedCanonicalJson : Lean.Json :=
  Mutation.dropFirstLink.apply canonical |>.canonicalJson

def rejectedCertificateStillParses : Bool :=
  match Certificate.fromJson rejectedCanonicalJson with
  | .ok certificate =>
      certificate == (Mutation.dropFirstLink.apply canonical |>.canonicalize)
  | .error _ => false

example : rejectedCertificateStillParses = true := by native_decide

example : (Certificate.checkedFromJson rejectedCanonicalJson).isOk = false := by
  native_decide

def missingAtomName : Lean.Json := Lean.Json.mkObj [
  ("kind", "atom"), ("positive", true)]

def missingAtomNameDiagnosticMatches : Bool :=
  match Certificate.formulaFromJson missingAtomName with
  | .error error =>
      error == { path := "$.name", message := "property not found: name" }
  | .ok _ => false

example : missingAtomNameDiagnosticMatches = true := by native_decide

def nonCanonicalJson : Lean.Json :=
  Lean.Json.mkObj [
    ("version", "0.2"),
    ("canonical", true),
    ("formulas", .arr (canonical.formulas.map Certificate.formulaJson)),
    ("links", .arr
      (scrambledCanonical.links.toArray.map Certificate.linkJson)),
    ("conclusions", .arr (scrambledCanonical.conclusions.toArray.map
      (fun value : Vertex => .num (Lean.JsonNumber.fromNat value))))]

example : (Certificate.fromJson nonCanonicalJson).isOk = false := by
  native_decide

def malformedExchange : CutFreeDerivation :=
  .exchange [0, 0] (.axiom "p" true)

example : malformedExchange.desequentialize?.isNone = true := by native_decide

example : (reconstructCanonical? canonical "p" "q").isSome = true := by
  native_decide

example :
    Derivation [
      .tensor (.atom "p" true) (.atom "q" true),
      .par (.atom "p" false) (.atom "q" false)
    ] := reconstructCanonical "p" "q"

def wrongAxiom : Certificate :=
  { canonical with links := [
      .axiom 0 3,
      .axiom 2 1,
      .tensor 0 2 4,
      .par 1 3 5
    ] }

example : wrongAxiom.wellFormed = false := by native_decide
example : wrongAxiom.check = false := by native_decide
example : ¬wrongAxiom.FuelCorrect := by
  intro semantic
  have accepted := wrongAxiom.check_iff_fuelCorrect.mpr semantic
  exact (by native_decide : wrongAxiom.check ≠ true) accepted
example : ¬wrongAxiom.FuelDeclarativelyCorrect := by
  intro semantic
  have accepted := wrongAxiom.check_iff_fuelDeclarativelyCorrect.mpr semantic
  exact (by native_decide : wrongAxiom.check ≠ true) accepted
example : (reconstructCanonical? wrongAxiom "p" "q").isSome = false := by
  native_decide

def canonicalThree : Certificate := canonicalThreeCertificate "p" "q" "r"

example : canonicalThree.wellFormed = true := by native_decide
example : canonicalThree.switchingGraphs.length = 4 := by native_decide
example : canonicalThree.check = true := by native_decide
example : canonicalThree.Correct :=
  canonicalThree.check_sound (by native_decide)

example :
    Derivation [
      .tensor
        (.tensor (.atom "p" true) (.atom "q" true))
        (.atom "r" true),
      .par
        (.atom "p" false)
        (.par (.atom "q" false) (.atom "r" false))
    ] := Derivation.canonicalThree "p" "q" "r"

def droppedLink : Certificate := Mutation.dropFirstLink.apply canonical
def duplicatedLink : Certificate := Mutation.duplicateFirstLink.apply canonical
def rewiredAxiom : Certificate :=
  (Mutation.replaceFirstAxiomRight 3).apply canonical

example : droppedLink.check = false := by native_decide
example : duplicatedLink.check = false := by native_decide
example : rewiredAxiom.check = false := by native_decide

def disconnected : Certificate where
  formulas := #[p, pDual, q, qDual]
  links := [.axiom 0 1, .axiom 2 3]
  conclusions := [0, 1, 2, 3]

example : disconnected.wellFormed = true := by native_decide
example : disconnected.check = false := by native_decide

def axiomOnly : Certificate where
  formulas := #[p, pDual]
  links := [.axiom 0 1]
  conclusions := [0, 1]

example : axiomOnly.wellFormed = true := by native_decide
example : axiomOnly.check = true := by native_decide

def duplicateConclusion : Certificate :=
  { axiomOnly with conclusions := [0, 0, 1] }

example : duplicateConclusion.wellFormed = false := by native_decide
example : duplicateConclusion.check = false := by native_decide

def outOfBounds : Certificate :=
  { axiomOnly with links := [.axiom 0 8] }

example : outOfBounds.wellFormed = false := by native_decide

def duplicateAxiom : Certificate :=
  { axiomOnly with links := [.axiom 0 1, .axiom 0 1] }

example : duplicateAxiom.wellFormed = false := by native_decide

def wrongTensorLabel : Certificate :=
  { canonical with formulas := #[p, pDual, q, qDual, .par p q, .par pDual qDual] }

example : wrongTensorLabel.wellFormed = false := by native_decide

def missingConclusion : Certificate :=
  { axiomOnly with conclusions := [] }

example : missingConclusion.wellFormed = false := by native_decide

def cyclicGraph : Graph where
  vertexCount := 3
  edges := [
    { first := 0, second := 1 },
    { first := 1, second := 2 },
    { first := 2, second := 0 }
  ]

example : cyclicGraph.connected = true := by native_decide
example : cyclicGraph.isTree = false := by native_decide
example : ¬cyclicGraph.FuelTree := by
  intro semantic
  have accepted := cyclicGraph.isTree_iff_fuelTree.mpr semantic
  exact (by native_decide : cyclicGraph.isTree ≠ true) accepted

def treeGraph : Graph where
  vertexCount := 4
  edges := [
    { first := 0, second := 1 },
    { first := 1, second := 2 },
    { first := 1, second := 3 }
  ]

example : treeGraph.isTree = true := by native_decide
example : treeGraph.IsTree := treeGraph.isTree_sound (by native_decide)
example : treeGraph.isTree = true ↔ treeGraph.IsTree :=
  treeGraph.isTree_iff_isTree
example : treeGraph.FuelTree :=
  treeGraph.isTree_iff_fuelTree.mp (by native_decide)
example : treeGraph.Walk 0 3 :=
  (treeGraph.isTree_sound (by native_decide)).2.1.2 3 (by decide)
theorem treeGraphLeaf3 : treeGraph.Leaf 3 := by
  simp [Graph.Leaf, Graph.incidentCount, treeGraph, Edge.incident]
example : (treeGraph.deleteVertex 3).IsTree :=
  (treeGraph.isTree_sound (by native_decide)).deleteLeaf treeGraphLeaf3
example : (treeGraph.deleteVertex 3).isTree = true := by native_decide
theorem treeGraphLeaf0 : treeGraph.Leaf 0 := by
  simp [Graph.Leaf, Graph.incidentCount, treeGraph, Edge.incident]
example : (treeGraph.deleteVertex 0).IsTree :=
  (treeGraph.isTree_sound (by native_decide)).deleteLeaf treeGraphLeaf0

theorem treeEdge01 : treeGraph.Adjacent 0 1 :=
  ⟨{ first := 0, second := 1 }, by simp [treeGraph], .inl ⟨rfl, rfl⟩⟩

theorem treeEdge13 : treeGraph.Adjacent 1 3 :=
  ⟨{ first := 1, second := 3 }, by simp [treeGraph], .inl ⟨rfl, rfl⟩⟩

theorem treeWalk03 : treeGraph.Walk 0 3 :=
  .step (.step (.refl 0) treeEdge01) treeEdge13

theorem treeWalkN03 : treeGraph.WalkN 0 2 3 :=
  .step (.step .refl treeEdge01) treeEdge13

example : ∃ steps visited, treeGraph.SimpleWalk 0 steps visited 3 :=
  treeWalk03.toSimple

example : treeGraph.FuelConnected :=
  (treeGraph.isTree_sound (by native_decide)).2.1.toFuelConnected
    (treeGraph.isTree_sound (by native_decide)).1

example : 3 ∈ treeGraph.closureN 2 [0] := by native_decide
example : 3 ∈ treeGraph.closureN 2 [0] :=
  treeGraph.walkN_mem_closureN
    (treeGraph.isTree_sound (by native_decide)).1 treeWalkN03
example :
    3 ∈ treeGraph.closureN 2 [0] ↔ treeGraph.WalkWithin 0 2 3 :=
  treeGraph.mem_closureN_iff_walkWithin
    (treeGraph.isTree_sound (by native_decide)).1 0 3 2 (by decide)
example : ∃ fuel, 3 ∈ treeGraph.closureN fuel [0] := by
  exact treeGraph.walk_mem_some_closureN
    (treeGraph.isTree_sound (by native_decide)).1
    treeWalk03

def singletonGraph : Graph where
  vertexCount := 1
  edges := []

example : singletonGraph.isTree = true := by native_decide

def emptyGraph : Graph where
  vertexCount := 0
  edges := []

example : emptyGraph.isTree = false := by native_decide

def selfLoopGraph : Graph where
  vertexCount := 1
  edges := [{ first := 0, second := 0 }]

example : selfLoopGraph.boundedEdges = false := by native_decide
example : selfLoopGraph.isTree = false := by native_decide

def parallelEdgeGraph : Graph where
  vertexCount := 2
  edges := [
    { first := 0, second := 1 },
    { first := 0, second := 1 }
  ]

example : parallelEdgeGraph.connected = true := by native_decide
example : parallelEdgeGraph.isTree = false := by native_decide

def unboundedGraph : Graph where
  vertexCount := 2
  edges := [{ first := 0, second := 2 }]

example : unboundedGraph.boundedEdges = false := by native_decide
example : unboundedGraph.isTree = false := by native_decide

/-- The unbounded walk semantics can cross an out-of-bounds bridge that the
finite checker intentionally filters. This witnesses why the `Bounded`
hypothesis of `connected_iff_connected` is necessary. -/
def unboundedBridgeGraph : Graph where
  vertexCount := 2
  edges := [
    { first := 0, second := 2 },
    { first := 2, second := 1 }
  ]

theorem unboundedBridgeEdge02 : unboundedBridgeGraph.Adjacent 0 2 :=
  ⟨{ first := 0, second := 2 }, by simp [unboundedBridgeGraph],
    .inl ⟨rfl, rfl⟩⟩

theorem unboundedBridgeEdge21 : unboundedBridgeGraph.Adjacent 2 1 :=
  ⟨{ first := 2, second := 1 }, by simp [unboundedBridgeGraph],
    .inl ⟨rfl, rfl⟩⟩

example : unboundedBridgeGraph.Connected := by
  refine ⟨by decide, ?_⟩
  intro vertex inBounds
  simp [unboundedBridgeGraph] at inBounds
  have cases : vertex = 0 ∨ vertex = 1 := by omega
  rcases cases with rfl | rfl
  · exact .refl 0
  · exact .step (.step (.refl 0) unboundedBridgeEdge02)
      unboundedBridgeEdge21

example : unboundedBridgeGraph.Bounded → False := by
  intro bounded
  have edgeBounds := bounded { first := 0, second := 2 }
    (by simp [unboundedBridgeGraph])
  have impossible : 2 < 2 := by
    simpa [unboundedBridgeGraph] using edgeBounds.2.1
  omega

example : unboundedBridgeGraph.connected = false := by native_decide

def run : IO Unit := do
  if !canonical.check then
    throw <| IO.userError "canonical proof net was unexpectedly rejected"
  let fixture ← IO.FS.readFile "examples/canonical-v0.3.json"
  match Certificate.checkedFromString fixture with
  | .error error =>
      throw <| IO.userError s!"v0.3 fixture rejected: {error.render}"
  | .ok checked =>
      if checked.certificate != canonical.equivalenceCanonicalize then
        throw <| IO.userError "v0.3 fixture differs from Lean serializer output"
  IO.println "ProofNetIR: all certificate and v0.3 fixture checks passed"

end ProofNetIRTests

def main : IO Unit := ProofNetIRTests.run
