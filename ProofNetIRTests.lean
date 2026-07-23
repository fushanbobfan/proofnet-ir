import ProofNetIR

open ProofNetIR

namespace ProofNetIRTests

universe u

def p : Formula := .atom "p" true
def pDual : Formula := p.dual
def q : Formula := .atom "q" true
def qDual : Formula := q.dual

example : p.dual.dual = p := by simp

example (proposition : Prop) : proposition → proposition ∧ proposition :=
  LeanProp.Templates.duplicate_proof proposition

example (left right : Prop) (leftProof : left) (rightProof : right) :
    left ∧ right :=
  LeanProp.Templates.linearPair_proof left right leftProof rightProof

example {α : Type u} (left right : α) (motive : α → Prop) :
    left = right → motive left → motive right :=
  LeanProp.Templates.rewrite_proof left right motive

example {α : Type u} (predicate : α → Prop) (term : α) :
    (∀ value, predicate value) → predicate term :=
  LeanProp.Templates.instantiate_proof predicate term

example {α : Type u} (predicate : α → Prop) (term : α) :
    predicate term → ∃ value, predicate value :=
  LeanProp.Templates.witness_proof predicate term

example (proposition : Prop) : proposition → proposition ∧ proposition :=
  (LeanProp.Schema.Corpus.duplicate "schema-p").sound
    (fun _ => proposition) .nil .nil

example : (LeanProp.Schema.Corpus.generated 100).length = 600 := by
  native_decide

example {left right : List Prop} :
    Nonempty (LeanProp.ContextPermutation left right) ↔ left.Perm right :=
  LeanProp.ContextPermutation.nonempty_iff_listPerm

example {left right : List Prop}
    (permutation : LeanProp.ContextPermutation left right)
    (values : LeanProp.Assumptions right) :
    LeanProp.Assumptions.permute permutation
        (LeanProp.Assumptions.permute permutation.symm values) = values :=
  LeanProp.Assumptions.permute_symm_right permutation values

example {source target linear : List Prop} {goal : Prop}
    (permutation : source.Perm target)
    (derivation : LeanProp.Derivation.{u} source linear goal) :
    Nonempty (LeanProp.Derivation.{u} target linear goal) :=
  LeanProp.Derivation.persistentExchange_nonempty_of_listPerm
    permutation derivation

example {persistent source target : List Prop} {goal : Prop}
    (permutation : source.Perm target)
    (derivation : LeanProp.Derivation.{u} persistent source goal) :
    Nonempty (LeanProp.Derivation.{u} persistent target goal) :=
  LeanProp.Derivation.linearExchange_nonempty_of_listPerm
    permutation derivation

def redundantPersistentIdentity (proposition : Prop) :
    LeanProp.Derivation [proposition] [] proposition :=
  .persistentContract (.persistentWeaken (.persistentAxiom))

example (proposition : Prop) :
    (redundantPersistentIdentity proposition).normalizePersistentStructural =
      LeanProp.Derivation.persistentAxiom := by
  rfl

example (proposition : Prop) :
    (redundantPersistentIdentity proposition).persistentStructuralSize = 2 := by
  rfl

example {persistent linear : List Prop} {goal : Prop}
    (derivation : LeanProp.Derivation.{u} persistent linear goal) :
    derivation.normalizePersistentStructural.PersistentStructurallyReduced :=
  derivation.normalizePersistentStructural_reduced

example {persistent linear : List Prop} {goal : Prop}
    (derivation : LeanProp.Derivation.{u} persistent linear goal) :
    derivation.normalizePersistentStructural.normalizePersistentStructural =
      derivation.normalizePersistentStructural :=
  derivation.normalizePersistentStructural_idempotent

example {persistent linear : List Prop} {goal : Prop}
    (derivation : LeanProp.Derivation.{u} persistent linear goal) :
    derivation.normalizePersistentStructural.persistentStructuralSize ≤
      derivation.persistentStructuralSize :=
  derivation.normalizePersistentStructural_size_le

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
example : ¬indexedParallelGraph.Acyclic := by
  intro acyclic
  exact acyclic indexedParallelCycle
example :
    indexedParallelGraph.isEdgeSimpleCycleTraversal
      indexedParallelCycle.traversed = true := by
  native_decide
example : indexedParallelGraph.hasEdgeSimpleCycle = true := by native_decide
example : indexedParallelGraph.isAcyclic = false := by native_decide

def reversedParallelGraph : Graph where
  vertexCount := 2
  edges := [{ first := 0, second := 1 }, { first := 1, second := 0 }]

def reversedParallelZero : reversedParallelGraph.DirectedEdge where
  index := 0
  edge := { first := 0, second := 1 }
  lookup := rfl
  forward := true

def reversedParallelOne : reversedParallelGraph.DirectedEdge where
  index := 1
  edge := { first := 1, second := 0 }
  lookup := rfl
  forward := true

def reversedParallelCycle : reversedParallelGraph.EdgeSimpleCycle where
  start := 0
  traversed := [reversedParallelZero, reversedParallelOne]
  nonempty := by simp
  walk := by
    exact Graph.EdgeWalk.step
      (Graph.EdgeWalk.step (.refl 0) reversedParallelZero rfl rfl)
      reversedParallelOne rfl rfl
  edgeIndicesNodup := by decide
  interiorNodup := by decide

example : ¬reversedParallelGraph.Acyclic := by
  intro acyclic
  exact acyclic reversedParallelCycle
example : reversedParallelGraph.isAcyclic = false := by native_decide
example : reversedParallelGraph.IsTree ↔
    reversedParallelGraph.Bounded ∧ reversedParallelGraph.Connected ∧
      reversedParallelGraph.Acyclic :=
  reversedParallelGraph.isTree_iff_bounded_connected_acyclic

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

def generatedDerivationVerifications : Bool :=
  generatedDerivationTrees.all fun tree =>
    match tree.desequentialize? with
    | none => false
    | some certificate => certificate.verifiesDerivation tree

example : generatedDerivationVerifications = true := by
  native_decide

def generatedReorderedDerivationVerifications : Bool :=
  generatedDerivationTrees.all fun tree =>
    match tree.desequentialize? with
    | none => false
    | some certificate =>
        ({ certificate with links := certificate.links.reverse } :
          Certificate).verifiesDerivation tree

example : generatedReorderedDerivationVerifications = true := by
  native_decide

def generatedCheckerFreeReconstructions : Bool :=
  generatedDerivationTrees.all fun tree =>
    match tree.desequentialize? with
    | none => false
    | some certificate => certificate.reconstructsDerivation

example : generatedCheckerFreeReconstructions = true := by
  native_decide

def generatedReorderedCheckerFreeReconstructions : Bool :=
  generatedDerivationTrees.all fun tree =>
    match tree.desequentialize? with
    | none => false
    | some certificate =>
        ({ certificate with links := certificate.links.reverse } :
          Certificate).reconstructsDerivation

example : generatedReorderedCheckerFreeReconstructions = true := by
  native_decide

example : generatedDerivationTrees.all (fun tree => tree.elaborate?.isSome) = true := by
  native_decide

example {tree : CutFreeDerivation} {sequent : List Formula}
    (accepted : tree.infer? = some sequent) :
    ∃ result : CutFreeDerivation.ElaboratedCertificate,
      tree.elaborate? = some result :=
  tree.elaborate?_exists_of_infer? accepted

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

def generatedExecutableSequentializations : Bool :=
  generatedDerivationTrees.all fun tree =>
    match tree.desequentialize? with
    | none => false
    | some certificate =>
        match certificate.sequentialize with
        | .error _ => false
        | .ok result =>
            result.tree.infer? == certificate.conclusionFormulas? &&
              result.output.check

/-- The public runtime inverse reconstructs all 250 broad generated trees,
including arbitrary tensor/par focuses and exchanges, and revalidates every
output certificate. -/
example : generatedExecutableSequentializations = true := by native_decide

def rejectedExecutableSequentialization : Bool :=
  match (Mutation.dropFirstLink.apply
      (identityCertificate mixedFormula)).sequentialize with
  | .error error => error.stage == "input"
  | .ok _ => false

example : rejectedExecutableSequentialization = true := by native_decide

example : Certificate.matchingFormulaOrder? [p, p, q] [p, q, p] =
    some [0, 2, 1] := by native_decide

example : Certificate.matchingFormulaOrders [p, p, q] [p, q, p] =
    [[0, 2, 1], [1, 2, 0]] := by native_decide

#check Certificate.matchingFormulaOrdersForCertificates_complete

def repeatedBoundaryTree : CutFreeDerivation :=
  .tensor 0 0 (.axiom "p" true) (.axiom "p" true)

/-- The final two formula labels are identical, but the exchange swaps their
distinct occurrence roots. This is the non-injective projection case for the
formula-to-fragment synchronization theorem. -/
def repeatedLabelExchangeTree : CutFreeDerivation :=
  .exchange [0, 2, 1] repeatedBoundaryTree

example : repeatedLabelExchangeTree.infer? =
    some [.tensor p p, pDual, pDual] := by
  native_decide

example : ∃ fragment : NetFragment,
    repeatedLabelExchangeTree.build? = some fragment :=
  CutFreeDerivation.build?_exists_of_infer?
    (sequent := [.tensor p p, pDual, pDual]) (by native_decide)

example : ∃ certificate : Certificate,
    repeatedLabelExchangeTree.desequentialize? = some certificate ∧
      certificate.conclusionFormulas? =
        some [.tensor p p, pDual, pDual] :=
  CutFreeDerivation.desequentialize?_exists_with_labels_of_infer?
    (by native_decide)

def repeatedBoundarySequentializes : Bool :=
  match repeatedBoundaryTree.desequentialize? with
  | none => false
  | some certificate =>
      match certificate.sequentialize with
      | .error _ => false
      | .ok result =>
          result.tree.infer? == certificate.conclusionFormulas?

/-- Two indistinguishable `p⊥` boundary labels exercise exhaustive occurrence
matching rather than a unique-label shortcut. -/
example : repeatedBoundarySequentializes = true := by native_decide

def repeatedBoundaryIdentityCandidateCount : Nat :=
  match repeatedBoundaryTree.desequentialize? with
  | none => 0
  | some certificate =>
      certificate.proofNetIdentityCandidateCount certificate

/-- One-hop role/label signatures remove all spurious self-alignments in this
repeated-label accepted net while retaining the genuine identity witness. -/
example : repeatedBoundaryIdentityCandidateCount = 1 := by native_decide

#check Certificate.localIdentityCompatible_inverse

def reversedLinkCertificate : Certificate :=
  { canonicalCertificate "reordered-p" "reordered-q" with
    links := (canonicalCertificate "reordered-p" "reordered-q").links.reverse }

example : reversedLinkCertificate.check = true := by native_decide

example : Certificate.proofNetEquivalent?
    (canonicalCertificate "reordered-p" "reordered-q")
      reversedLinkCertificate = true := by native_decide

def checkedCanonicalCertificate : CutFreeDerivation.CheckedCertificate :=
  ⟨canonicalCertificate "reordered-p" "reordered-q", by native_decide⟩

def checkedReversedLinkCertificate : CutFreeDerivation.CheckedCertificate :=
  ⟨reversedLinkCertificate, by native_decide⟩

example : checkedCanonicalCertificate.sameProofNet?
    checkedReversedLinkCertificate = true := by native_decide

example : checkedCanonicalCertificate.certificate.ProofNetEquivalent
    checkedReversedLinkCertificate.certificate :=
  CutFreeDerivation.CheckedCertificate.sameProofNet?_eq_true_iff.mp
    (by native_decide)

example : (canonicalCertificate "reordered-p" "reordered-q").ProofNetEquivalent
    reversedLinkCertificate := by
  apply (Certificate.proofNetEquivalent?_eq_true_iff
    ((canonicalCertificate "reordered-p" "reordered-q").check_sound_declarative
      (by native_decide)).1).mp
  native_decide

def reversedConclusionCertificate : Certificate :=
  { canonicalCertificate "ordered-p" "ordered-q" with
    conclusions := (canonicalCertificate "ordered-p" "ordered-q").conclusions.reverse }

example : reversedConclusionCertificate.check = true := by native_decide

/-- `ProofNetEquivalent` deliberately preserves the ordered conclusion
boundary even though it ignores link-list storage order. -/
example : Certificate.proofNetEquivalent?
    (canonicalCertificate "ordered-p" "ordered-q")
      reversedConclusionCertificate = false := by native_decide

def reversedLinkSequentializes : Bool :=
  match reversedLinkCertificate.sequentialize with
  | .error _ => false
  | .ok result => result.output.check

/-- Link storage order is semantically irrelevant.  This is a regression for
the v0.5 prototype's initially over-strong `ReindexEquivalent` postcondition. -/
example : reversedLinkSequentializes = true := by native_decide

def generatedReversedLinkSequentializations : Bool :=
  generatedDerivationTrees.all fun tree =>
    match tree.desequentialize? with
    | none => false
    | some certificate =>
        let reordered : Certificate :=
          { certificate with links := certificate.links.reverse }
        reordered.check && reordered.sequentialize.isOk

/-- The full generated corpus remains executable after reversing every stored
link list, exercising the v0.4 link-permutation identity contract broadly. -/
example : generatedReversedLinkSequentializations = true := by native_decide

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
example : Certificate.ParPairSparse canonical.links 0
    (fun index =>
      [true, true, true, true, true, false][index]? = some true) :=
  canonicalFullLeftSelection.mask_parPairSparse

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
example : canonicalParLeftIn ∈ canonical.fullGraph.directedEdges :=
  canonicalParLeftIn.mem_directedEdges
example : canonical.Cusp canonicalParLeftIn canonicalParRightIn.reverse := by
  rfl
example : canonical.Cusp canonicalParRightIn canonicalParLeftIn.reverse :=
  (canonical.cusp_reverse_iff canonicalParLeftIn
    canonicalParRightIn.reverse).mp (by rfl)
example : canonical.isCuspFreeTraversal
    [canonicalParLeftIn, canonicalParRightIn.reverse] = false := by
  native_decide
example : canonical.isCuspFreeTraversal
    [canonicalParLeftIn] = true := by
  native_decide
example : canonical.cuspCount
    [canonicalParLeftIn, canonicalParRightIn.reverse] = 1 := by
  native_decide
example : canonical.CuspingEdge canonicalParLeftIn := by
  refine ⟨canonicalParRightIn.reverse, by rfl, ?_⟩
  intro same
  have sameIndex := congrArg Graph.DirectedEdge.index same
  exact (by decide : canonicalParLeftIn.index ≠
    canonicalParRightIn.reverse.index) sameIndex
example (directed : canonical.fullGraph.DirectedEdge) :
    directed.source ≠ directed.target :=
  canonical.fullDirectedEdge_loopless
    (canonical.wellFormed_iff_structurallyWellFormed.mp (by native_decide))
    directed
example : canonical.cuspCount
      ([canonicalParLeftIn] ++ [canonicalParRightIn.reverse]) =
    canonical.cuspCount [canonicalParLeftIn] +
      canonical.cuspCount [canonicalParRightIn.reverse] +
      canonical.cuspBoundaryCount [canonicalParLeftIn]
        [canonicalParRightIn.reverse] :=
  canonical.cuspCount_append _ _
example : canonical.cuspCount
      (Graph.EdgeWalk.reverseTraversal
        [canonicalParLeftIn, canonicalParRightIn.reverse]) =
    canonical.cuspCount
      [canonicalParLeftIn, canonicalParRightIn.reverse] :=
  canonical.cuspCount_reverseTraversal _

example {incoming outgoing : canonical.fullGraph.DirectedEdge}
    (continuation : canonical.CuspFreeContinuation incoming outgoing)
    (vertices : List Vertex)
    (intersects : ∃ vertex,
      vertex ∈ continuation.path.vertices.tail ∧ vertex ∈ vertices) :
    ∃ (last : canonical.fullGraph.DirectedEdge)
      (truncated : canonical.CuspFreeContinuation incoming last),
      last.target ∈ vertices ∧
      ∀ vertex, vertex ∈ truncated.path.vertices.tail →
        vertex ∈ vertices → vertex = last.target :=
  continuation.prefixToFirstIntersection vertices intersects

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
example : canonical.CuspAcyclic :=
  (canonical.check_sound_declarative (by native_decide)).cuspAcyclic
example :
    (canonical.fullGraph.retainEdges
      [true, true, true, true, true, false]).Acyclic :=
  (show canonical.CuspAcyclic from
      (canonical.check_sound_declarative (by native_decide)).cuspAcyclic)
    |>.occurrenceSwitching_acyclic
      (canonical.wellFormed_iff_structurallyWellFormed.mp (by native_decide))
      canonicalFullLeftSelection
example : canonical.CuspAcyclic ↔
    ∀ selected retained mask,
      Certificate.FullSwitchingSelection canonical.links
          selected retained mask →
        (canonical.fullGraph.retainEdges mask).Acyclic :=
  canonical.cuspAcyclic_iff_allOccurrenceSwitchingsAcyclic
    (canonical.wellFormed_iff_structurallyWellFormed.mp (by native_decide))
example : canonical.AllOccurrenceSwitchingsConnected :=
  (canonical.declarativelyCorrect_iff_structural_cuspAcyclic_allConnected.mp
    (canonical.check_sound_declarative (by native_decide))).2.2
example : canonical.DeclarativelyCorrect ↔
    canonical.StructurallyWellFormed ∧
      canonical.CuspAcyclic ∧
      canonical.AllOccurrenceSwitchingsConnected :=
  canonical.declarativelyCorrect_iff_structural_cuspAcyclic_allConnected
example : canonical.check = true ↔
    canonical.StructurallyWellFormed ∧
      canonical.CuspAcyclic ∧
      canonical.AllOccurrenceSwitchingsConnected :=
  canonical.check_iff_structural_cuspAcyclic_allConnected
example : canonical.isCuspAcyclic = true :=
  canonical.isCuspAcyclic_of_check (by native_decide)
example : canonical.isCuspAcyclic = true ↔ canonical.CuspAcyclic :=
  canonical.isCuspAcyclic_eq_true_iff
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

example : canonical.verifiesDerivation canonicalRuleTree = true := by
  native_decide

example :
    ({ canonical with links := canonical.links.reverse } :
      Certificate).verifiesDerivation canonicalRuleTree = true := by
  native_decide

example :
    (Mutation.dropFirstLink.apply canonical).verifiesDerivation
      canonicalRuleTree = false := by
  native_decide

example : canonical.reconstructsDerivation = true := by
  native_decide

example : canonical.reconstructsDerivation = canonical.check :=
  canonical.reconstructsDerivation_eq_check

example : ∃ result : DerivationVerificationResult canonical,
    canonical.reconstructDerivation? = some result :=
  canonical.reconstructDerivation?_complete (by native_decide)

def canonicalBoundedReconstruction :=
  canonical.reconstructDerivationWithinLimits

example : canonicalBoundedReconstruction.isOk = true := by
  native_decide

def zeroReconstructionLimits : ReconstructionLimits where
  maxFormulaOccurrences := 0
  maxLinks := 0
  maxConclusions := 0

def zeroLimitReportsFormulaCount : Bool :=
  match canonical.reconstructDerivationWithinLimits
      zeroReconstructionLimits with
  | .error (.formulaLimitExceeded actual limit) =>
      actual == canonical.formulas.size && limit == 0
  | _ => false

example : zeroLimitReportsFormulaCount = true := by
  native_decide

def malformedBoundedReconstructionRejected : Bool :=
  match (Mutation.dropFirstLink.apply canonical)
      |>.reconstructDerivationWithinLimits with
  | .error .structurallyMalformed => true
  | _ => false

example : malformedBoundedReconstructionRejected = true := by
  native_decide

def conclusionOverLimitCertificate : Certificate :=
  { canonical with conclusions := List.replicate 25 4 }

def conclusionLimitReportedBeforeSearch : Bool :=
  match conclusionOverLimitCertificate.reconstructDerivationWithinLimits with
  | .error (.conclusionLimitExceeded actual limit) =>
      actual == 25 && limit == ReconstructionLimits.qualified.maxConclusions
  | _ => false

example : conclusionLimitReportedBeforeSearch = true := by
  native_decide

example :
    (Mutation.dropFirstLink.apply canonical).reconstructsDerivation = false := by
  native_decide

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
example : (FinitePermutations.allPermutations ([0, 1, 2] : List Nat)).length =
    6 := by native_decide
example : [2, 0, 1] ∈
    FinitePermutations.allPermutations ([0, 1, 2] : List Nat) := by
  exact FinitePermutations.mem_allPermutations_iff.mpr (by decide)
example : canonical.equivalenceCanonicalize ∈
    canonical.proofNetCanonicalFamily := by
  rw [Certificate.mem_proofNetCanonicalFamily_iff]
  exact ⟨canonical.links, .refl _, rfl⟩
example : ∀ candidate,
    candidate ∈ canonical.proofNetCanonicalFamily ↔
      candidate ∈ linkScrambledCanonical.proofNetCanonicalFamily :=
  (show canonical.ProofNetEquivalent linkScrambledCanonical from by
    refine (show canonical.LinkPermutationEquivalent
      linkScrambledCanonical from ?_).toProofNetEquivalent
    refine ⟨rfl, ?_, rfl⟩
    simpa [linkScrambledCanonical] using
      (List.reverse_perm canonical.links).symm)
    |>.proofNetCanonicalFamily_mem_iff
example : canonical.ProofNetEquivalent linkScrambledCanonical ↔
    ∀ candidate,
      candidate ∈ canonical.proofNetCanonicalFamily ↔
        candidate ∈ linkScrambledCanonical.proofNetCanonicalFamily :=
  Certificate.proofNetEquivalent_iff_canonicalFamily_of_check
    (by native_decide) (by native_decide)
example :
    canonical.proofNetCanonicalFingerprint?.isSome = true := by
  native_decide
example :
    ∃ fingerprint,
      canonical.proofNetCanonicalFingerprint? = some fingerprint :=
  canonical.proofNetCanonicalFingerprint?_exists
example :
    canonical.proofNetCanonicalFingerprint? =
      linkScrambledCanonical.proofNetCanonicalFingerprint? :=
  (show canonical.ProofNetEquivalent linkScrambledCanonical from by
    refine (show canonical.LinkPermutationEquivalent
      linkScrambledCanonical from ?_).toProofNetEquivalent
    refine ⟨rfl, ?_, rfl⟩
    simpa [linkScrambledCanonical] using
      (List.reverse_perm canonical.links).symm)
    |>.proofNetCanonicalFingerprint?_eq
example :
    (canonical.reindex
      swapCanonicalZeroOne).proofNetCanonicalFingerprint? =
      canonical.proofNetCanonicalFingerprint? :=
  (show (canonical.reindex swapCanonicalZeroOne).ProofNetEquivalent
      canonical from
    (Certificate.ReindexEquivalent.symm
      ⟨swapCanonicalZeroOne, rfl⟩).toProofNetEquivalent)
    |>.proofNetCanonicalFingerprint?_eq
example :
    canonical.proofNetCanonicalCode?.isSome = true := by
  native_decide
example :
    canonical.ProofNetEquivalent linkScrambledCanonical ↔
      canonical.proofNetCanonicalCode? =
        linkScrambledCanonical.proofNetCanonicalCode? :=
  Certificate.proofNetEquivalent_iff_canonicalCode_of_check
    (by native_decide) (by native_decide)
example :
    canonical.proofNetCanonicalCode? =
      linkScrambledCanonical.proofNetCanonicalCode? :=
  (show canonical.ProofNetEquivalent linkScrambledCanonical from by
    refine (show canonical.LinkPermutationEquivalent
      linkScrambledCanonical from ?_).toProofNetEquivalent
    refine ⟨rfl, ?_, rfl⟩
    simpa [linkScrambledCanonical] using
      (List.reverse_perm canonical.links).symm)
    |>.proofNetCanonicalCode?_eq
example :
    (canonical.reindex swapCanonicalZeroOne).proofNetCanonicalCode? =
      canonical.proofNetCanonicalCode? :=
  (show (canonical.reindex swapCanonicalZeroOne).ProofNetEquivalent
      canonical from
    (Certificate.ReindexEquivalent.symm
      ⟨swapCanonicalZeroOne, rfl⟩).toProofNetEquivalent)
    |>.proofNetCanonicalCode?_eq
example :
    (canonicalCertificate "ordered-p" "ordered-q").proofNetCanonicalCode? ≠
      reversedConclusionCertificate.proofNetCanonicalCode? := by
  native_decide

def generatedCanonicalKey : CanonicalKey :=
  canonical.proofNetCanonicalKey?.get (by native_decide)

example :
    canonical.matchesCanonicalKey generatedCanonicalKey = true := by
  native_decide
example :
    linkScrambledCanonical.matchesCanonicalKey generatedCanonicalKey = true := by
  native_decide
example : canonical.ProofNetEquivalent linkScrambledCanonical :=
  Certificate.proofNetEquivalent_of_matchesCanonicalKey
    (key := generatedCanonicalKey)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
example :
    canonical.ProofNetEquivalent linkScrambledCanonical ↔
      canonical.proofNetCanonicalKey? =
        linkScrambledCanonical.proofNetCanonicalKey? :=
  Certificate.proofNetEquivalent_iff_canonicalKey_of_check
    (by native_decide) (by native_decide)

def overLimitCanonicalKeyCertificate : Certificate :=
  { canonical with links := List.replicate 8 (.axiom 0 1) }

example : CanonicalKey.maxGenerationLinks = 7 := rfl
example :
    overLimitCanonicalKeyCertificate.proofNetCanonicalKeyWithinLimit?.isNone =
      true := by
  native_decide
example :
    overLimitCanonicalKeyCertificate.proofNetCanonicalKeyString?.isNone =
      true := by
  native_decide
example :
    overLimitCanonicalKeyCertificate.matchesCanonicalKey generatedCanonicalKey =
      false := by
  native_decide

def generatedCanonicalKeyRoundTrips : Bool :=
  match CanonicalKey.fromString generatedCanonicalKey.toString with
  | .ok parsed => parsed == generatedCanonicalKey
  | .error _ => false

example : generatedCanonicalKeyRoundTrips = true := by native_decide
example :
    (CanonicalKey.fromString
      "{\"version\":\"wrong\",\"canonicalization\":\"proofnet-equivalent-v1\",\"tokens\":[\"x\"]}").isOk =
        false := by
  native_decide
example :
    (CanonicalKey.fromString
      "{\"version\":\"proofnet-canonical-key-0.1\",\"canonicalization\":\"wrong\",\"tokens\":[\"x\"]}").isOk =
        false := by
  native_decide
example :
    (CanonicalKey.fromString
      "{\"version\":\"proofnet-canonical-key-0.1\",\"canonicalization\":\"proofnet-equivalent-v1\",\"tokens\":[]}").isOk =
        false := by
  native_decide
example :
    (CanonicalKey.fromString
      "{\"version\":\"proofnet-canonical-key-0.1\",\"canonicalization\":\"proofnet-equivalent-v1\",\"tokens\":[1]}").isOk =
        false := by
  native_decide
example :
    (Certificate.migrateV03StringToCanonicalKey
      canonical.equivalenceCanonicalString).isOk = true := by
  native_decide
example :
    (Certificate.migrateV03StringToCanonicalKey
      canonical.canonicalString).isOk = false := by
  native_decide

def migratedCanonicalKeyMatches : Bool :=
  match Certificate.migrateV03StringToCanonicalKey
      canonical.equivalenceCanonicalString with
  | .error _ => false
  | .ok wire =>
      match CanonicalKey.fromString wire with
      | .error _ => false
      | .ok key => canonical.matchesCanonicalKey key

example : migratedCanonicalKeyMatches = true := by native_decide

/-- One thousand cheap, deterministic wire properties vary atom labels while
exercising exact-key equality across reversed link storage and JSON
encode/decode.  This is a wire regression corpus, not a performance claim for
large factorial families. -/
def generatedCanonicalKeyWireProperties : Bool :=
  (List.range 1000).all fun seed =>
    let formula :=
      Formula.tensor
        (.atom s!"wire-p-{seed}" true)
        (.atom s!"wire-q-{seed}" true)
    let certificate := identityCertificate formula
    let reordered : Certificate :=
      { certificate with links := certificate.links.reverse }
    match certificate.proofNetCanonicalKeyWithinLimit?,
        reordered.proofNetCanonicalKeyWithinLimit? with
    | some leftKey, some rightKey =>
        leftKey == rightKey &&
          match CanonicalKey.fromString leftKey.toString with
          | .ok parsed => parsed == leftKey
          | .error _ => false
    | _, _ => false

example : generatedCanonicalKeyWireProperties = true := by native_decide
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

def loopGraph : Graph where
  vertexCount := 1
  edges := [{ first := 0, second := 0 }]

def disconnectedForestGraph : Graph where
  vertexCount := 4
  edges := [
    { first := 0, second := 1 },
    { first := 2, second := 3 }
  ]

/-- Three uniquely colored axiom occurrences form a cusp-free triangle. The
certificate is intentionally not structurally well formed: this fixture tests
the colored-cycle oracle independently of certificate acceptance. -/
def cuspCycleCertificate : Certificate where
  formulas := #[p, q, pDual]
  links := [.axiom 0 1, .axiom 1 2, .axiom 2 0]
  conclusions := [0, 1, 2]

example : cuspCycleCertificate.hasCuspFreeEdgeSimpleCycle = true := by
  native_decide
example : cuspCycleCertificate.isCuspAcyclic = false := by
  native_decide

def cyclicDirected01 : cyclicGraph.DirectedEdge where
  index := 0
  edge := { first := 0, second := 1 }
  lookup := rfl
  forward := true

def cyclicDirected12 : cyclicGraph.DirectedEdge where
  index := 1
  edge := { first := 1, second := 2 }
  lookup := rfl
  forward := true

def cyclicDirected20 : cyclicGraph.DirectedEdge where
  index := 2
  edge := { first := 2, second := 0 }
  lookup := rfl
  forward := true

def cyclicTriangle : cyclicGraph.EdgeSimpleCycle where
  start := 0
  traversed := [cyclicDirected01, cyclicDirected12, cyclicDirected20]
  nonempty := by simp
  walk := by
    apply Graph.EdgeWalk.step
      (Graph.EdgeWalk.step
        (Graph.EdgeWalk.step (.refl 0) cyclicDirected01 rfl rfl)
        cyclicDirected12 rfl rfl)
      cyclicDirected20 rfl rfl
  edgeIndicesNodup := by decide
  interiorNodup := by decide

def swapCyclicZeroOne : VertexRenaming cyclicGraph.vertexCount :=
  VertexRenaming.swap cyclicGraph.vertexCount 0 1 (by decide) (by decide)

def reindexedCyclicTriangle :
    (cyclicGraph.reindex swapCyclicZeroOne).EdgeSimpleCycle :=
  cyclicTriangle.reindex swapCyclicZeroOne

example : reindexedCyclicTriangle.start = 1 := by native_decide
example : reindexedCyclicTriangle.traversed.map (·.index) = [0, 1, 2] := by
  native_decide

def cyclicPath02 : cyclicGraph.EdgeSimplePath where
  start := 0
  finish := 2
  traversed := [cyclicDirected01, cyclicDirected12]
  walk := by
    apply Graph.EdgeWalk.step
      (Graph.EdgeWalk.step (.refl 0) cyclicDirected01 rfl rfl)
      cyclicDirected12 rfl rfl
  verticesNodup := by decide

def cyclicReturn20 : cyclicGraph.EdgeSimplePath where
  start := 2
  finish := 0
  traversed := [cyclicDirected20]
  walk := by
    exact Graph.EdgeWalk.step (.refl 2) cyclicDirected20 rfl rfl
  verticesNodup := by decide

def cyclicTriangleFromPaths : cyclicGraph.EdgeSimpleCycle :=
  Graph.EdgeSimpleCycle.ofTwoPaths cyclicPath02 cyclicReturn20
    (by simp [cyclicPath02]) (by simp [cyclicReturn20]) rfl rfl
    (by native_decide) (by native_decide)

example : cyclicTriangleFromPaths.traversed = cyclicTriangle.traversed := rfl
example : cyclicPath02.reverse.vertices = cyclicPath02.vertices.reverse :=
  cyclicPath02.reverse_vertices
example : cyclicPath02.traversed.map Graph.DirectedEdge.index |>.Nodup :=
  cyclicPath02.edgeIndicesNodup
example : ∃ rotated : cyclicGraph.EdgeSimpleCycle,
    rotated.start = 1 ∧ rotated.traversed =
      [cyclicDirected12, cyclicDirected20, cyclicDirected01] := by
  simpa [cyclicDirected12, Graph.DirectedEdge.source] using
    cyclicTriangle.rotateAt_exists
      (before := [cyclicDirected01]) (first := cyclicDirected12)
      (after := [cyclicDirected20]) rfl
example : ∃ path : cyclicGraph.EdgeSimplePath,
    path.start = 2 ∧ path.finish = 0 ∧
      path.traversed = [cyclicDirected20] ∧
      ∀ vertex, vertex ∈ path.vertices → vertex ∈ cyclicTriangle.vertices := by
  rcases cyclicTriangle.complementPath
      (before := []) (outgoingAtVertex := cyclicDirected01)
      (between := []) (cuspIncoming := cyclicDirected12)
      (cuspOutgoing := cyclicDirected20) (after := []) rfl with
    ⟨path, starts, finishes, steps, _baseInTail, subset, _edgeSubset⟩
  exact ⟨path, by
    simpa [cyclicDirected20, Graph.DirectedEdge.source] using starts,
    by simpa [cyclicDirected01, Graph.DirectedEdge.source] using finishes,
    by simpa using steps, subset⟩

#check Certificate.cyclicCuspCount_append_comm
#check Certificate.CuspFreeContinuation.firstIntersection_cycle_edgeDisjoint
#check Certificate.CuspFreeContinuation.firstIntersection_withCycle_cycle
#check Certificate.CuspFreeContinuation.bungee_firstIntersection_cycle
#check Certificate.CuspFreeContinuation.rotate_spliced_cycle_to_return_vertex
#check Certificate.CuspFreeContinuation.bungee_firstIntersection_sameBaseCycle
#check Certificate.CuspFreeContinuation.bungee_firstIntersection_exactSameBaseCycle
#check Certificate.cuspCount_rotateAt_of_closing_free
#check Certificate.bungee_exactSameBase_closingFree
#check Certificate.bungee_minimal_count_constraints
#check Certificate.bungee_cuspFreeCycle_of_minimal_nonempty
#check Certificate.CuspAcyclic.no_minimal_bungee_firstIntersection_nonempty
#check Certificate.no_minimal_bungee_firstIntersection_atBase
#check Certificate.no_minimal_bungee_firstIntersection_atBase_forward
#check Certificate.no_minimal_bungee_firstIntersection_atBase_anyOrientation
#check Certificate.CuspAcyclic.no_minimal_bungee_firstIntersection
#check Graph.EdgeWalk.head_reverseTraversal
#check Graph.EdgeWalk.getLast_reverseTraversal
#check Graph.EdgeSimpleCycle.middlePath
#check Graph.EdgeSimpleCycle.mem_reverse_vertices_iff
#check Graph.EdgeSimpleCycle.wrapPathAfterCusp
#check Graph.EdgeSimpleCycle.segmentBeforeAfterCuspHit
#check Certificate.CuspFreeContinuation.bungee_afterCusp_exactSameBaseCycle
#check Certificate.bungee_afterCusp_exactSameBase_closingFree
#check Certificate.bungee_afterCusp_minimal_count_constraints
#check Certificate.CuspAcyclic.no_minimal_bungee_afterCusp
#check Certificate.CuspFreeContinuation.rebaseAtReversedPartner
#check Certificate.no_minimal_bungee_atIncoming_base
#check Certificate.CuspAcyclic.no_minimal_bungee_atIncoming
#check Certificate.CuspAcyclic.no_minimal_bungee
#check Certificate.CuspFreeContinuation.toOrderingPathOfMinimalCycle
#check Certificate.CuspAcyclic.ordering_of_not_splitting
#check Certificate.CuspAcyclic.exists_splittingVertex_of_directedEdge
#check Graph.DirectedEdge.eq_of_index_eq_of_forward_eq
#check Graph.SimpleWalk.liftToEdgeSimplePath
#check Certificate.tensor_fullEdgeAnnotations
#check Certificate.fullEdgeAnnotation_some_par_origin
#check Certificate.incidenceColor_eq_unique_of_not_par
#check Certificate.tensor_incidenceColors_exist
#check Certificate.CuspingEdge.incidenceColor_eq_par
#check Certificate.CuspingEdge.par_origin
#check Certificate.CuspAcyclic.exists_splitting_par_of_cuspingEdge
#check Certificate.fullGraphWithoutVertex_simpleWalk_avoids
#check Certificate.SplittingVertex.toSplittingTensor
#check Graph.EdgeSimplePath.directed_endpoints_mem_vertices
#check Graph.EdgeSimplePath.directed_source_ne_finish
#check Graph.EdgeSimplePath.head_source
#check Certificate.SequentializationEdge
#check Certificate.CuspingEdge.sequentializationEdge
#check Certificate.parent_sequentializationEdge_exists
#check Certificate.cusp_eq_reverse_of_outgoing_forward
#check Certificate.SequentializationEdge.parentContinuation
#check Certificate.CuspAcyclic.ordering_to_parent
#check Certificate.SequentializationEdge.target_in_bounds
#check Certificate.CuspAcyclic.ordering_of_sequentializationEdge_not_terminal
#check Certificate.sequentializationEdge_exists_of_connective
#check Certificate.CuspAcyclic.exists_terminal_splitting_target
#check Certificate.DeclarativelyCorrect.terminalPar_or_splittingTensor_exists
#check Certificate.terminalPar_or_splittingTensor_exists_of_check
#check Certificate.peelTerminalPar_formulas_size_lt
#check Certificate.splitTerminalTensorCandidate?_left_formulas_size_lt
#check Certificate.splitTerminalTensorCandidate?_right_formulas_size_lt
#check Certificate.DeclarativelyCorrect.axiomOnly_cardinality
#check Certificate.DeclarativelyCorrect.axiomOnly_conclusions_perm
#check Certificate.DeclarativelyCorrect.axiomOnly_data
#check Certificate.DeclarativelyCorrect.axiomOnly_certificate_cases
#check Certificate.DeclarativelyCorrect.axiomOnly_sequentialization
#check CutFreeDerivation.pick?_append_cons
#check CutFreeDerivation.infer?_parLast
#check CutFreeDerivation.infer?_tensorLast
#check CutFreeDerivation.build?_parLast
#check CutFreeDerivation.build?_tensorLast
#check LogicalSequentializationResult
#check LogicalSequentializationResult.ofSequentialization
#check LogicalSequentializationResult.parRule
#check LogicalSequentializationResult.tensorRule
#check Certificate.StructurallyWellFormed.conclusionFormulas?_eq_getD
#check Certificate.restrictTo?_conclusionFormulas?_eq_some
#check Certificate.TerminalPar.logicalBoundaryData
#check Certificate.SplittingTensor.logicalBoundaryData
#check Certificate.logicalSequentialization_of_check
#check Certificate.logicallySequentializable
#check Certificate.DirectProofNetEquivalent
#check Certificate.ProofNetEquivalent.toDirect
#check Certificate.proofNetEquivalent_iff_direct
#check CutFreeDerivation.CheckedCertificate.sameProofNet?
#check CutFreeDerivation.CheckedCertificate.sameProofNet?_eq_true_iff
#check NetFragment.Balanced
#check CutFreeDerivation.pick?_map
#check CutFreeDerivation.pick?_exists_of_map_eq_some
#check CutFreeDerivation.reorderCandidate?_perm
#check CutFreeDerivation.reorder?_eq_reorderCandidate?
#check CutFreeDerivation.reorderCandidate?_map
#check CutFreeDerivation.reorder?_map_of_eq_some
#check CutFreeDerivation.reorder?_exists_of_map_eq_some
#check CutFreeDerivation.build?_balanced
#check CutFreeDerivation.infer?_of_build?
#check CutFreeDerivation.build?_exists_of_infer?
#check CutFreeDerivation.infer?_eq_some_iff_build?_conclusions
#check NetFragment.FormulaConsistent
#check CutFreeDerivation.build?_formulaConsistent
#check CutFreeDerivation.build?_structurallyWellFormed
#check CutFreeDerivation.build?_switchingCorrect
#check CutFreeDerivation.build?_declarativelyCorrect
#check CutFreeDerivation.build?_check
#check CutFreeDerivation.build?_conclusionFormulas?
#check CutFreeDerivation.desequentialize?_conclusionFormulas?
#check CutFreeDerivation.desequentialize?_declarativelyCorrect
#check CutFreeDerivation.desequentialize?_check
#check CutFreeDerivation.desequentialize?_exists_with_labels_of_infer?
#check CutFreeDerivation.desequentialize?_exists_checked_of_infer?
#check CutFreeDerivation.desequentializeChecked?_exists_of_infer?
#check CutFreeDerivation.elaborate?_exists_of_infer?
#check CutFreeDerivation.build?_exists_of_desequentialize?
#check SequentializationResult.fragment_exists
#check VertexRenaming.extendLast
#check VertexRenaming.insertLastAt
#check CutFreeDerivation.reorder?_idxOf_of_nodup_perm
#check CutFreeDerivation.build?_exchange_of_reorder
#check list_pair_decompose_map_fst_append_two
#check list_pair_decompose_map_fst_append_one
#check list_zip_labelled_of_mapM_eq_some
#check list_zip_eq_map_option_getD_of_mapM_eq_some
#check list_pairs_eq_map_option_getD
#check list_zip_map_fst_snd
#check list_map_pair_self_nodup
#check Certificate.appendParOccurrence
#check Certificate.appendParPlacement
#check Certificate.appendParOccurrence_reindex_formulas
#check Certificate.DirectProofNetEquivalent.appendParOccurrenceExtended
#check Certificate.DirectProofNetEquivalent.appendParOccurrence
#check Certificate.TerminalPar.occurrenceBoundaryReconstruction_at
#check Certificate.TerminalPar.occurrenceBoundaryReconstruction
#check Certificate.TerminalPar.premiseBoundaryData_of_formulaData
#check Link.reindex_insertLastAt_compactVertices
#check Certificate.TerminalPar.producer_filter_eq
#check Certificate.TerminalPar.terminal_not_mem_remaining
#check Certificate.TerminalPar.peelLinks_reindex_append_perm
#check Certificate.LinkWellFormed.par_formulaData
#check Certificate.TerminalPar.peelFormulas_reindex_append_eq
#check Certificate.TerminalPar.rebuild_directProofNetEquivalent
#check Certificate.TerminalPar.sequentializationResult
#check Certificate.appendTensorOccurrence
#check VertexRenaming.blockSum
#check Certificate.appendTensorRenaming
#check Certificate.appendTensorOccurrence_reindex_formulas
#check Certificate.DirectProofNetEquivalent.appendTensorOccurrenceExtended
#check Certificate.LinkWellFormed.tensor_formulaData
#check Certificate.TerminalTensor.tensorPlacement
#check Certificate.TerminalTensor.tensorPlacement_inverse_left
#check Certificate.TerminalTensor.tensorPlacement_inverse_right
#check Certificate.TerminalTensor.tensorPlacement_inverse_conclusion
#check Certificate.TerminalTensor.occurrenceBoundaryReconstruction
#check Certificate.TerminalTensor.restrictLinks_reindex_append_perm
#check Certificate.TerminalTensor.rebuild_directProofNetEquivalent
#check Certificate.SplittingTensor.premiseBoundaryData_of_formulaData
#check Certificate.TerminalTensor.sequentializationResult
#check Certificate.sequentialization_of_check
#check Certificate.generallySequentializable
#check Certificate.sequentialize_complete
#check Certificate.verifyDerivation?
#check Certificate.verifyDerivation?_sound
#check Certificate.verifyDerivation?_complete
#check Certificate.verifiesDerivation_eq_true_iff
#check Certificate.reconstructDerivationWithFuel?
#check Certificate.reconstructDerivation?
#check Certificate.reconstructDerivation?_sound
#check Certificate.reconstructDerivation?_accepted
#check Certificate.reconstructDerivation?_complete
#check Certificate.reconstructsDerivation_eq_true_iff
#check Certificate.reconstructsDerivation_eq_true_iff_check
#check Certificate.reconstructsDerivation_eq_check
#check ReconstructionLimits
#check ReconstructionLimits.qualified
#check ReconstructionError
#check ReconstructionError.message
#check Certificate.reconstructDerivationWithinLimits
#check Certificate.reconstructDerivationWithinLimits_sound
#check Certificate.reconstructDerivationWithinLimits_accepted
#check Certificate.reconstructDerivationWithinLimits_implies_reconstructs

example : CutFreeDerivation.reorder?
    [((.atom "p" true : Formula), 0), (.atom "p" true, 1)] [1, 0] =
      some [((.atom "p" true : Formula), 1), (.atom "p" true, 0)] := by
  native_decide

example : Nonempty (LogicalSequentializationResult canonical) :=
  canonical.logicalSequentialization_of_check (by native_decide)

example : Nonempty (SequentializationResult axiomOnly) := by
  apply (axiomOnly.check_sound_declarative (by native_decide)).axiomOnly_sequentialization
  simp [axiomOnly, Link.isConnective]

example : ∃ result : ExecutableSequentializationResult canonical,
    canonical.sequentialize = .ok result :=
  canonical.sequentialize_complete (by native_decide)

example : cyclicTriangle.reverse.traversed =
    [cyclicDirected20.reverse, cyclicDirected12.reverse,
      cyclicDirected01.reverse] := by
  rfl

example : ∃ path : cyclicGraph.EdgeSimplePath,
    path.start = 0 ∧ path.finish = 1 ∧
      path.traversed = [cyclicDirected01] := by
  simpa [cyclicTriangle, cyclicDirected01, Graph.DirectedEdge.target] using
    cyclicTriangle.prefixPath
    (before := []) (incoming := cyclicDirected01)
    (outgoing := cyclicDirected12) (after := [cyclicDirected20]) rfl

example : ∃ initialPath : cyclicGraph.EdgeSimplePath,
    initialPath.start = 0 ∧ initialPath.finish = 2 ∧
      initialPath.traversed = [cyclicDirected01, cyclicDirected12] := by
  simpa [cyclicTriangle, cyclicDirected12, Graph.DirectedEdge.target] using
    cyclicTriangle.prefixPath
      (before := [cyclicDirected01]) (incoming := cyclicDirected12)
      (outgoing := cyclicDirected20) (after := []) rfl

example : cyclicGraph.connected = true := by native_decide
example : cyclicGraph.isTree = false := by native_decide
example : cyclicGraph.isAcyclic = false := by native_decide
example : cyclicGraph.isTreeViaAcyclic = cyclicGraph.isTree :=
  cyclicGraph.isTreeViaAcyclic_eq_isTree
example : loopGraph.isAcyclic = false := by native_decide
example : disconnectedForestGraph.isAcyclic = true := by native_decide
example : disconnectedForestGraph.isAcyclic = true ↔
    disconnectedForestGraph.Acyclic :=
  disconnectedForestGraph.isAcyclic_eq_true_iff
example : ¬cyclicGraph.Acyclic := by
  intro acyclic
  exact acyclic cyclicTriangle
#check Graph.retainEdgesByMask_lookup_exists_original
#check Graph.DirectedEdge.inflateRetained_exists
#check Graph.EdgeWalk.inflateRetained
#check Graph.EdgeSimpleCycle.inflateRetained
#check Graph.DirectedEdge.ne_reverse
#check Graph.EdgeSimpleCycle.eq_of_index_eq
#check Certificate.FullSwitchingSelection.mask_parPairSparse
#check Certificate.FullSwitchingSelection.kept_parTarget_index_unique
#check Certificate.StructurallyWellFormed.parTarget_producerCount
#check Certificate.FullSwitchingSelection.no_cusp_of_kept
#check Certificate.fullSwitchingSelection_cycle_cuspFree
#check Certificate.CuspAcyclic.occurrenceSwitching_acyclic
#check Certificate.cuspAcyclic_iff_allOccurrenceSwitchingsAcyclic
#check Graph.Bounded.retainEdges
#check Certificate.StructurallyWellFormed.fullGraph_bounded
#check Certificate.AllOccurrenceSwitchingsConnected
#check Certificate.declarativelyCorrect_iff_structural_cuspAcyclic_allConnected
#check Certificate.check_iff_structural_cuspAcyclic_allConnected
#check Certificate.StructurallyWellFormed.par_producer_unique
example : cyclicGraph.IsTree ↔
    cyclicGraph.Bounded ∧ cyclicGraph.Connected ∧ cyclicGraph.Acyclic :=
  cyclicGraph.isTree_iff_bounded_connected_acyclic
example : ¬(cyclicGraph.reindex swapCyclicZeroOne).Acyclic := by
  intro acyclic
  exact acyclic reindexedCyclicTriangle
example : (cyclicGraph.reindex swapCyclicZeroOne).Acyclic ↔
    cyclicGraph.Acyclic :=
  cyclicGraph.acyclic_reindex_iff swapCyclicZeroOne
example : ¬cyclicGraph.IsTree := by
  intro tree
  exact tree.no_edgeSimpleCycle cyclicTriangle
example : ∃ maximal ∈ ([0, 1, 2] : List Nat),
    ∀ candidate ∈ ([0, 1, 2] : List Nat), ¬maximal < candidate := by
  exact Certificate.exists_relation_maximal [0, 1, 2] (by simp) (by simp)
    (fun first second : Nat => first < second)
    Nat.lt_irrefl (by intro first middle last; omega)
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

def swapTreeZeroThree : VertexRenaming treeGraph.vertexCount :=
  VertexRenaming.swap treeGraph.vertexCount 0 3 (by decide) (by decide)

example : treeGraph.isTree = true := by native_decide
example : treeGraph.isAcyclic = true := by native_decide
example : treeGraph.isTreeViaAcyclic = true := by native_decide
example : treeGraph.isTreeViaAcyclic = treeGraph.isTree :=
  treeGraph.isTreeViaAcyclic_eq_isTree
example : treeGraph.isAcyclic = true ↔ treeGraph.Acyclic :=
  treeGraph.isAcyclic_eq_true_iff
example : treeGraph.IsTree := treeGraph.isTree_sound (by native_decide)
example : treeGraph.Acyclic :=
  (treeGraph.isTree_sound (by native_decide)).acyclic
example : treeGraph.IsTree ↔
    treeGraph.Bounded ∧ treeGraph.Connected ∧ treeGraph.Acyclic :=
  treeGraph.isTree_iff_bounded_connected_acyclic
example : treeGraph.edges.length + 1 ≤ treeGraph.vertexCount :=
  ((treeGraph.isTree_sound (by native_decide)).acyclic)
    |>.edges_add_one_le_vertexCount
      (treeGraph.isTree_sound (by native_decide)).1
      (treeGraph.isTree_sound (by native_decide)).2.1
example : (treeGraph.reindex swapTreeZeroThree).Acyclic :=
  ((treeGraph.isTree_sound (by native_decide)).acyclic).reindex
    swapTreeZeroThree
example : ∃ vertex, vertex < treeGraph.vertexCount ∧ vertex ≠ 0 := by
  rcases (treeGraph.isTree_sound (by native_decide)).every_edge_index_is_parent
      (index := 1) (by decide) with
    ⟨vertex, inBounds, nonRoot, parentIndex⟩
  exact ⟨vertex, inBounds, nonRoot⟩
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

/-! v0.8 intrinsic-canonicalization regression boundary. -/

example :
    canonical.intrinsicCanonicalize =
      linkScrambledCanonical.intrinsicCanonicalize := by
  native_decide

example :
    canonical.intrinsicCanonicalize =
      reindexedCanonical.intrinsicCanonicalize := by
  native_decide

example :
    canonical.intrinsicCanonicalize =
      linkScrambledCanonical.intrinsicCanonicalize :=
  (show canonical.ProofNetEquivalent linkScrambledCanonical from by
    refine (show canonical.LinkPermutationEquivalent
      linkScrambledCanonical from ?_).toProofNetEquivalent
    refine ⟨rfl, ?_, rfl⟩
    simpa [linkScrambledCanonical] using
      (List.reverse_perm canonical.links).symm)
    |>.intrinsicCanonicalize_eq

example :
    canonical.intrinsicCanonicalize ≠
      reversedConclusionCertificate.intrinsicCanonicalize := by
  native_decide

example :
    canonical.intrinsicOrderedLinks.Perm canonical.links := by
  native_decide

def rightNestedFormula : Nat → Formula
  | 0 => .atom "intrinsic-base" true
  | depth + 1 =>
      .tensor (rightNestedFormula depth)
        (.atom s!"intrinsic-right-{depth}" true)

def intrinsicLargeCertificate : Certificate :=
  identityCertificate (rightNestedFormula 8)

example :
    CanonicalKey.maxGenerationLinks <
      intrinsicLargeCertificate.links.length := by
  native_decide

example : intrinsicLargeCertificate.check = true := by
  native_decide

example :
    intrinsicLargeCertificate.proofNetCanonicalKeyWithinLimit?.isNone =
      true := by
  native_decide

example :
    intrinsicLargeCertificate.intrinsicCanonicalKeyString?.isSome =
      true := by
  native_decide

def generatedIntrinsicCanonicalKey : IntrinsicCanonicalKey :=
  canonical.intrinsicCanonicalKey

example :
    canonical.matchesIntrinsicCanonicalKey generatedIntrinsicCanonicalKey =
      true := by
  native_decide

example :
    linkScrambledCanonical.matchesIntrinsicCanonicalKey
      generatedIntrinsicCanonicalKey = true := by
  native_decide

example : canonical.ProofNetEquivalent linkScrambledCanonical :=
  Certificate.proofNetEquivalent_of_matchesIntrinsicCanonicalKey
    (key := generatedIntrinsicCanonicalKey)
    (by native_decide) (by native_decide)

def generatedIntrinsicCanonicalKeyRoundTrips : Bool :=
  match IntrinsicCanonicalKey.fromString
      generatedIntrinsicCanonicalKey.toString with
  | .ok parsed => parsed == generatedIntrinsicCanonicalKey
  | .error _ => false

example : generatedIntrinsicCanonicalKeyRoundTrips = true := by
  native_decide

example :
    (IntrinsicCanonicalKey.fromString
      "{\"version\":\"proofnet-canonical-key-0.1\",\"canonicalization\":\"proofnet-equivalent-v1\",\"tokens\":[\"x\"]}").isOk =
        false := by
  native_decide

example :
    (CanonicalKey.fromString generatedIntrinsicCanonicalKey.toString).isOk =
      false := by
  native_decide

example :
    (Certificate.migrateV03StringToIntrinsicCanonicalKey
      canonical.equivalenceCanonicalString).isOk = true := by
  native_decide

def migratedIntrinsicCanonicalKeyMatches : Bool :=
  match Certificate.migrateV03StringToIntrinsicCanonicalKey
      canonical.equivalenceCanonicalString with
  | .error _ => false
  | .ok wire =>
      match IntrinsicCanonicalKey.fromString wire with
      | .error _ => false
      | .ok key => canonical.matchesIntrinsicCanonicalKey key

example : migratedIntrinsicCanonicalKeyMatches = true := by
  native_decide

/-- One thousand deterministic differential cases compare the new intrinsic
key with the v0.7 factorial oracle on the oracle's supported small domain.
Both positive link permutations and negative ordered-boundary changes must
agree, and every new wire value must round-trip. -/
def intrinsicCanonicalDifferentialProperties : Bool :=
  (List.range 1000).all fun seed =>
    let formula :=
      Formula.tensor
        (.atom s!"intrinsic-p-{seed}" true)
        (.atom s!"intrinsic-q-{seed}" true)
    let certificate := identityCertificate formula
    let reordered : Certificate :=
      { certificate with links := certificate.links.reverse }
    let boundaryChanged : Certificate :=
      { certificate with conclusions := certificate.conclusions.reverse }
    let leftOld := certificate.proofNetCanonicalKeyWithinLimit?
    let reorderedOld := reordered.proofNetCanonicalKeyWithinLimit?
    let boundaryOld := boundaryChanged.proofNetCanonicalKeyWithinLimit?
    let leftNew := certificate.intrinsicCanonicalKey
    let reorderedNew := reordered.intrinsicCanonicalKey
    let boundaryNew := boundaryChanged.intrinsicCanonicalKey
    (leftOld == reorderedOld) &&
      (leftNew == reorderedNew) &&
      (leftOld != boundaryOld) &&
      (leftNew != boundaryNew) &&
      match IntrinsicCanonicalKey.fromString leftNew.toString with
      | .ok parsed =>
          parsed == leftNew &&
            certificate.matchesIntrinsicCanonicalKey parsed
      | .error _ => false

example : intrinsicCanonicalDifferentialProperties = true := by
  native_decide

/-- A broader generated-net corpus exercises the intrinsic path independently
of the small factorial oracle domain. Every derivation-generated accepted net
and its reversed link storage must emit one round-tripping key that safely
matches both inputs. -/
def intrinsicCanonicalGeneratedProperties : Bool :=
  (List.range 1000).all fun seed =>
    let tree := CutFreeDerivation.generate (10_000 + seed) 2
    match tree.desequentialize? with
    | none => false
    | some certificate =>
        let reordered : Certificate :=
          { certificate with links := certificate.links.reverse }
        certificate.check &&
          (certificate.intrinsicCanonicalKey ==
            reordered.intrinsicCanonicalKey) &&
          match certificate.intrinsicCanonicalKeyString? with
          | none => false
          | some wire =>
              match IntrinsicCanonicalKey.fromString wire with
              | .error _ => false
              | .ok key =>
                  certificate.matchesIntrinsicCanonicalKey key &&
                    reordered.matchesIntrinsicCanonicalKey key

example : intrinsicCanonicalGeneratedProperties = true := by
  native_decide

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
