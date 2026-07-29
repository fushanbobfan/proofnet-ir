import ProofNetIR
import ProofNetIR.SequentialFigure7History

example {certificate : ProofNetIR.Certificate}
    {state next : ProofNetIR.UnificationMarking certificate}
    (step : ProofNetIR.UnificationStep certificate state next) :
    state.tokenCount ≤ next.tokenCount :=
  step.tokenCount_mono

example {certificate : ProofNetIR.Certificate}
    {state next : ProofNetIR.UnificationMarking certificate}
    (step : ProofNetIR.UnificationStep certificate state next) :
    (∃ left right,
      ProofNetIR.Link.axiom left right ∈ certificate.links) ∨
    (∃ left right conclusion,
      ProofNetIR.Link.par left right conclusion ∈ certificate.links) ∨
    (∃ left right conclusion,
      ProofNetIR.Link.tensor left right conclusion ∈ certificate.links) :=
  step.link_exists

example (certificate : ProofNetIR.Certificate)
    (state : ProofNetIR.UnificationState)
    (abstractable :
      state.Abstractable certificate) :
    (state.toMarking certificate abstractable).tokenCount =
      state.parents.size :=
  state.toMarking_tokenCount certificate abstractable

example (certificate : ProofNetIR.Certificate)
    (state : ProofNetIR.UnificationState)
    (abstractable :
      state.Abstractable certificate)
    (first second : Nat) :
    (state.toMarking certificate abstractable).sameThread first second ↔
      state.representative first = state.representative second :=
  state.toMarking_sameThread certificate abstractable first second

example {certificate : ProofNetIR.Certificate}
    {state : ProofNetIR.UnificationState}
    (consistent :
      state.ComponentsFormulaConsistent certificate)
    {token : Nat} {component : ProofNetIR.UnificationComponent}
    (yielded : state.componentAt? token = some component) :
    component.FormulaConsistent certificate :=
  consistent.componentAt yielded

example {certificate : ProofNetIR.Certificate}
    (state : ProofNetIR.UnificationMarking certificate)
    (fresh : Nat) :
    Equivalence (state.FreshExtension fresh) :=
  state.freshExtension_equivalence fresh

example {certificate : ProofNetIR.Certificate}
    (state : ProofNetIR.UnificationMarking certificate)
    (leftToken rightToken : Nat) :
    Equivalence (state.MergeExtension leftToken rightToken) :=
  state.mergeExtension_equivalence leftToken rightToken

example {certificate : ProofNetIR.Certificate}
    (state : ProofNetIR.UnificationMarking certificate)
    (leftToken rightToken : Nat) :
    state.MergeExtension leftToken rightToken =
      state.MergeExtension rightToken leftToken :=
  state.mergeExtension_comm leftToken rightToken

example {certificate : ProofNetIR.Certificate}
    {state next : ProofNetIR.UnificationMarking certificate}
    (transition :
      ProofNetIR.UnificationStep certificate state next) :
    ProofNetIR.UnificationExecution certificate state next :=
  ProofNetIR.UnificationExecution.single transition

example {certificate : ProofNetIR.Certificate}
    {state : ProofNetIR.UnificationState}
    (abstractable : state.Abstractable certificate)
    (identity : state.IdentityParents)
    {left right : Nat}
    (membership :
      ProofNetIR.Link.axiom left right ∈ certificate.links)
    (leftBound : left < certificate.formulas.size)
    (rightBound : right < certificate.formulas.size)
    (leftUnmarked : state.assignedToken? left = none)
    (rightUnmarked : state.assignedToken? right = none) :
    ProofNetIR.UnificationStep certificate
      (state.toMarking certificate abstractable)
      ((state.startMarking left right).toMarking certificate
        (abstractable.startMarking identity leftBound rightBound)) :=
  state.startMarking_startStep abstractable identity membership
    leftBound rightBound leftUnmarked rightUnmarked

example {state : ProofNetIR.UnificationState}
    (ordered : state.OrderedParents)
    {token : Nat} (bound : token < state.parents.size) :
    state.representative (state.representative token) =
      state.representative token :=
  ordered.representative_idempotent bound

example {certificate : ProofNetIR.Certificate}
    {state : ProofNetIR.UnificationState}
    (abstractable : state.Abstractable certificate)
    (ordered : state.OrderedParents)
    {conclusion representative retired : Nat}
    (conclusionBound : conclusion < certificate.formulas.size)
    (representativeBound : representative < state.parents.size)
    (representativeLe : representative ≤ retired) :
    (state.mergeConclusion conclusion representative retired)
      |>.Abstractable certificate :=
  abstractable.mergeConclusion ordered conclusionBound
    representativeBound representativeLe

example {state : ProofNetIR.UnificationState}
    {left right conclusion leftToken rightToken : Nat}
    (equation :
      state.unifyTokens? left right conclusion =
        some (leftToken, rightToken)) :
    state.marks[conclusion]? = some none ∧
      state.tokenAt? left = some leftToken ∧
      state.tokenAt? right = some rightToken ∧
      leftToken ≠ rightToken :=
  state.unifyTokens?_success equation

example (certificate : ProofNetIR.Certificate)
    (state : ProofNetIR.UnificationState)
    (abstractable : state.Abstractable certificate)
    {vertex token : Nat}
    (yielded : state.tokenAt? vertex = some token) :
    token < state.parents.size :=
  abstractable.tokenAt?_bound yielded

example (certificate : ProofNetIR.Certificate)
    (state : ProofNetIR.UnificationState)
    (abstractable : state.Abstractable certificate)
    {vertex token : Nat}
    (yielded : state.tokenAt? vertex = some token) :
    state.representative token = token :=
  abstractable.tokenAt?_root yielded

example {state : ProofNetIR.UnificationState}
    {vertex token : Nat}
    (yielded : state.tokenAt? vertex = some token) :
    ∃ rawToken,
      state.assignedToken? vertex = some rawToken ∧
        state.representative rawToken = token :=
  state.tokenAt?_some_witness yielded

example {certificate : ProofNetIR.Certificate}
    {state : ProofNetIR.UnificationState}
    (abstractable : state.Abstractable certificate)
    (ordered : state.OrderedParents)
    {left right conclusion leftToken rightToken : Nat}
    (membership :
      ProofNetIR.Link.tensor left right conclusion ∈ certificate.links)
    (equation :
      state.unifyTokens? left right conclusion =
        some (leftToken, rightToken)) :
    ∃ nextAbstractable :
        (state.mergeConclusion conclusion
          (min leftToken rightToken) (max leftToken rightToken))
          |>.Abstractable certificate,
      ProofNetIR.UnificationStep certificate
        (state.toMarking certificate abstractable)
        ((state.mergeConclusion conclusion
          (min leftToken rightToken) (max leftToken rightToken)).toMarking
            certificate nextAbstractable) :=
  state.unifyTokens?_refines abstractable ordered membership equation

example (certificate : ProofNetIR.Certificate)
    (state : ProofNetIR.UnificationState)
    (abstractable : state.Abstractable certificate)
    {conclusion token : Nat}
    (conclusionBound : conclusion < certificate.formulas.size)
    (tokenBound : token < state.parents.size) :
    (state.markConclusion conclusion token).Abstractable certificate :=
  abstractable.markConclusion conclusionBound tokenBound

example {certificate : ProofNetIR.Certificate}
    {first second : ProofNetIR.UnificationState}
    (equivalent : first.ObservationEquivalent second)
    (abstractable : first.Abstractable certificate) :
    second.Abstractable certificate :=
  equivalent.abstractable abstractable

example {first second : ProofNetIR.UnificationState}
    (equivalent : first.ObservationEquivalent second)
    (identity : first.IdentityParents) :
    second.IdentityParents :=
  equivalent.identityParents identity

example {certificate : ProofNetIR.Certificate}
    {state : ProofNetIR.UnificationState}
    (abstractable : state.Abstractable certificate)
    {left right conclusion leftToken rightToken outputToken : Nat}
    (membership :
      ProofNetIR.Link.par left right conclusion ∈ certificate.links)
    (conclusionBound : conclusion < certificate.formulas.size)
    (conclusionUnmarked : state.assignedToken? conclusion = none)
    (leftMarked : state.assignedToken? left = some leftToken)
    (rightMarked : state.assignedToken? right = some rightToken)
    (premisesSynchronized : state.SameThread leftToken rightToken)
    (outputTokenAllocated : outputToken < state.parents.size)
    (outputTokenSynchronized :
      state.SameThread outputToken leftToken) :
    ProofNetIR.UnificationStep certificate
      (state.toMarking certificate abstractable)
      ((state.markConclusion conclusion outputToken).toMarking certificate
        (abstractable.markConclusion conclusionBound
          outputTokenAllocated)) :=
  state.markConclusion_forwardStep abstractable membership conclusionBound
    conclusionUnmarked leftMarked rightMarked premisesSynchronized
    outputTokenAllocated outputTokenSynchronized

example {certificate : ProofNetIR.Certificate}
    {state : ProofNetIR.UnificationState}
    (abstractable : state.Abstractable certificate)
    {left right conclusion outputToken : Nat}
    (membership :
      ProofNetIR.Link.par left right conclusion ∈ certificate.links)
    (equation :
      state.forwardToken? left right conclusion = some outputToken) :
    ∃ nextAbstractable :
        (state.markConclusion conclusion outputToken)
          |>.Abstractable certificate,
      ProofNetIR.UnificationStep certificate
        (state.toMarking certificate abstractable)
        ((state.markConclusion conclusion outputToken).toMarking
          certificate nextAbstractable) :=
  state.forwardToken?_refines abstractable membership equation

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

example :
    ¬Graph.EdgeWalk.NoImmediateReverse
      [parallelDirectedZero, parallelDirectedZero.reverse] := by
  simp [Graph.EdgeWalk.NoImmediateReverse]

example :
    Graph.EdgeWalk.NoImmediateReverse
      [parallelDirectedZero, parallelDirectedOne.reverse] := by
  simp [Graph.EdgeWalk.NoImmediateReverse, parallelDirectedZero,
    parallelDirectedOne, Graph.DirectedEdge.reverse]

example : indexedParallelGraph.EdgeWalk 0 [] 0 := by
  have outAndBack :
      indexedParallelGraph.EdgeWalk 0
        [parallelDirectedZero, parallelDirectedZero.reverse] 0 := by
    simpa [parallelDirectedZero, Graph.DirectedEdge.source] using
      Graph.EdgeWalk.step
        (Graph.EdgeWalk.step (.refl 0) parallelDirectedZero rfl rfl)
        parallelDirectedZero.reverse rfl rfl
  simpa using
    (Graph.EdgeWalk.cancelImmediateReverse
      (before := []) (after := []) outAndBack)

example :
    Graph.EdgeWalk.ImmediateReverseNormalization
      [parallelDirectedZero, parallelDirectedZero.reverse] [] :=
  .step (.cancel [] [] parallelDirectedZero) (.refl [])

example :
    Graph.EdgeWalk.CyclicImmediateReverseNormalization
      [parallelDirectedZero, parallelDirectedZero.reverse] [] :=
  .finish (.step (.cancel [] [] parallelDirectedZero) (.refl []))

example
    (normalization :
      Graph.EdgeWalk.CyclicImmediateReverseNormalization
        [parallelDirectedZero, parallelDirectedZero.reverse] []) :
    parallelDirectedZero.reverse ∈
      [parallelDirectedZero, parallelDirectedZero.reverse] := by
  apply normalization.reverse_mem_of_normalizes_to_nil rfl
  simp

example
    (normalization :
      Graph.EdgeWalk.CyclicImmediateReverseNormalization
        [parallelDirectedZero, parallelDirectedZero.reverse] []) :
    Graph.EdgeWalk.CyclicImmediateReverseSite
      [parallelDirectedZero, parallelDirectedZero.reverse] := by
  exact normalization.site_of_nonempty_normalizes_to_nil (by simp) rfl

example :
    ∃ reduced,
      Graph.EdgeWalk.ImmediateReverseNormalization
          [parallelDirectedZero, parallelDirectedZero.reverse] reduced ∧
        indexedParallelGraph.EdgeWalk 0 reduced 0 ∧
          Graph.EdgeWalk.NoImmediateReverse reduced := by
  have outAndBack :
      indexedParallelGraph.EdgeWalk 0
        [parallelDirectedZero, parallelDirectedZero.reverse] 0 := by
    simpa [parallelDirectedZero, Graph.DirectedEdge.source] using
      Graph.EdgeWalk.step
        (Graph.EdgeWalk.step (.refl 0) parallelDirectedZero rfl rfl)
        parallelDirectedZero.reverse rfl rfl
  exact Graph.EdgeWalk.normalizeImmediateReversals _ outAndBack

example :
    ∃ normalizedBase reduced,
      indexedParallelGraph.EdgeWalk normalizedBase reduced normalizedBase ∧
        Graph.EdgeWalk.CyclicImmediateReverseNormalization
          [parallelDirectedZero, parallelDirectedZero.reverse] reduced ∧
          (reduced = [] ∨
            Graph.EdgeWalk.CyclicNoImmediateReverse reduced) := by
  have outAndBack :
      indexedParallelGraph.EdgeWalk 0
        [parallelDirectedZero, parallelDirectedZero.reverse] 0 := by
    simpa [parallelDirectedZero, Graph.DirectedEdge.source] using
      Graph.EdgeWalk.step
        (Graph.EdgeWalk.step (.refl 0) parallelDirectedZero rfl rfl)
        parallelDirectedZero.reverse rfl rfl
  exact
    Graph.EdgeWalk.normalizeCyclicImmediateReversalsTraced _ outAndBack

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

/-- Empty token state used to exercise the bounded sequential `NEXTAXIOM`
slice independently of the later `σ`/ready/waiting scheduler. -/
def canonicalSequentialEmpty : UnificationState where
  marks := Array.replicate canonical.formulas.size none
  parents := #[]
  components := #[]
  startedAxioms := 0
  firedConnectives := 0

/-- No canonical occurrence has a token in the empty sequential state. -/
theorem canonicalSequentialEmpty_assignedToken?_eq_none
    (vertex : Vertex) :
    canonicalSequentialEmpty.assignedToken? vertex = none := by
  by_cases vertexBound : vertex < canonical.formulas.size
  · simp [canonicalSequentialEmpty, UnificationState.assignedToken?,
      vertexBound]
  · have outOfBounds : canonical.formulas.size ≤ vertex :=
      Nat.le_of_not_gt vertexBound
    simp [canonicalSequentialEmpty, UnificationState.assignedToken?,
      outOfBounds]

/-- The empty state used by the initial/local `NEXTAXIOM` totality theorem has
the exact executable carrier required by the independent marking semantics. -/
theorem canonicalSequentialEmpty_abstractable :
    canonicalSequentialEmpty.Abstractable canonical := by
  refine {
    markArraySize := by
      simp [canonicalSequentialEmpty]
    markedVertexBound := ?_
    markedTokenBound := ?_
    representativeBound := ?_
    representativeIdempotent := ?_ }
  · intro vertex token assigned
    rw [canonicalSequentialEmpty_assignedToken?_eq_none vertex] at assigned
    simp at assigned
  · intro vertex token assigned
    rw [canonicalSequentialEmpty_assignedToken?_eq_none vertex] at assigned
    simp at assigned
  · intro token tokenBound
    simp [canonicalSequentialEmpty] at tokenBound
  · intro token tokenBound
    simp [canonicalSequentialEmpty] at tokenBound

def canonicalSourceIndex : SequentialUnification.SourceIndex :=
  SequentialUnification.sourceIndex canonical

/-- The structural source table contains one and only one source at every
canonical occurrence, including both atomic endpoints and compound
conclusions. -/
def canonicalSourceBucketsSingleton : Bool :=
  (List.range canonical.formulas.size).all fun vertex =>
    match canonicalSourceIndex[vertex]? with
    | some [_source] => true
    | _ => false

example : canonicalSourceBucketsSingleton = true := by
  native_decide

example (vertex : Vertex) (vertexBound : vertex < canonical.formulas.size) :
    ∃ source,
      canonicalSourceIndex[vertex]? = some [source] := by
  have structural : canonical.StructurallyWellFormed := by
    exact canonical.wellFormed_iff_structurallyWellFormed.mp
      (by native_decide)
  exact
    SequentialUnification.StructurallyWellFormed.sourceIndex_lookup_eq_singleton
      structural vertexBound

/-- With the entire initial carrier untagged and unassigned, every in-bounds
canonical occurrence has a kernel-proved successful rank-budget search.  This
is the initial/local theorem, not a Figure-7 `new`-state result. -/
example (vertex : Vertex) (vertexBound : vertex < canonical.formulas.size) :
    ∃ result,
      SequentialUnification.nextAxiomWithFuel? canonical
          canonicalSequentialEmpty canonicalSourceIndex
          (SequentialUnification.sourceIndex_sound canonical)
          (canonical.formulaComplexityAt vertex + 1)
          (Array.replicate canonical.formulas.size false) vertex =
        some result := by
  apply
    SequentialUnification.nextAxiomWithFuel?_exists_of_structural_carrierClear
      (canonical.wellFormed_iff_structurallyWellFormed.mp
        (by native_decide))
      canonicalSequentialEmpty_abstractable vertexBound
  intro candidate candidateBound
  constructor
  · simp [candidateBound]
  · exact canonicalSequentialEmpty_assignedToken?_eq_none candidate

/-- Executable coverage of the rank-budget initial theorem at all six
canonical occurrences, including both compound starts. -/
def canonicalRankBudgetNextAxiomsAll : Bool :=
  (List.range canonical.formulas.size).all fun vertex =>
    (SequentialUnification.nextAxiomWithFuel? canonical
      canonicalSequentialEmpty canonicalSourceIndex
      (SequentialUnification.sourceIndex_sound canonical)
      (canonical.formulaComplexityAt vertex + 1)
      (Array.replicate canonical.formulas.size false) vertex).isSome

example : canonicalRankBudgetNextAxiomsAll = true := by
  native_decide

/-- A depth-two source-left route used to lock the strict fuel boundary of
the rank-scoped `NEXTAXIOM` totality theorem. -/
def nestedRankBudgetR : Formula := .atom "r" true

def nestedRankBudgetRDual : Formula := nestedRankBudgetR.dual

def nestedRankBudget : Certificate where
  formulas := #[
    p, pDual, q, qDual, nestedRankBudgetR, nestedRankBudgetRDual,
    .tensor p q, .tensor (.tensor p q) nestedRankBudgetR
  ]
  links := [
    .axiom 0 1,
    .axiom 2 3,
    .axiom 4 5,
    .tensor 0 2 6,
    .tensor 6 4 7
  ]
  conclusions := [7, 1, 3, 5]

def nestedRankBudgetEmpty : UnificationState where
  marks := Array.replicate nestedRankBudget.formulas.size none
  parents := #[]
  components := #[]
  startedAxioms := 0
  firedConnectives := 0

theorem nestedRankBudgetEmpty_assignedToken?_eq_none
    (vertex : Vertex) :
    nestedRankBudgetEmpty.assignedToken? vertex = none := by
  by_cases vertexBound : vertex < nestedRankBudget.formulas.size
  · simp [nestedRankBudgetEmpty, UnificationState.assignedToken?,
      vertexBound]
  · have outOfBounds : nestedRankBudget.formulas.size ≤ vertex :=
      Nat.le_of_not_gt vertexBound
    simp [nestedRankBudgetEmpty, UnificationState.assignedToken?,
      outOfBounds]

theorem nestedRankBudgetEmpty_abstractable :
    nestedRankBudgetEmpty.Abstractable nestedRankBudget := by
  refine {
    markArraySize := by
      simp [nestedRankBudgetEmpty]
    markedVertexBound := ?_
    markedTokenBound := ?_
    representativeBound := ?_
    representativeIdempotent := ?_ }
  · intro vertex token assigned
    rw [nestedRankBudgetEmpty_assignedToken?_eq_none vertex] at assigned
    simp at assigned
  · intro vertex token assigned
    rw [nestedRankBudgetEmpty_assignedToken?_eq_none vertex] at assigned
    simp at assigned
  · intro token tokenBound
    simp [nestedRankBudgetEmpty] at tokenBound
  · intro token tokenBound
    simp [nestedRankBudgetEmpty] at tokenBound

def nestedRankBudgetSourceIndex : SequentialUnification.SourceIndex :=
  SequentialUnification.sourceIndex nestedRankBudget

example : nestedRankBudget.wellFormed = true := by
  native_decide

theorem nestedRankBudget_startComplexity :
    nestedRankBudget.formulaComplexityAt 7 = 2 := by
  native_decide

/-- Fuel equal to the starting rank is one recursive step too short. -/
example :
    SequentialUnification.nextAxiomWithFuel? nestedRankBudget
      nestedRankBudgetEmpty nestedRankBudgetSourceIndex
      (SequentialUnification.sourceIndex_sound nestedRankBudget)
      2 (Array.replicate nestedRankBudget.formulas.size false) 7 = none := by
  native_decide

/-- The exact `rank + 1` budget succeeds by the general structural theorem,
not only by reduction of this fixture. -/
example :
    ∃ result,
      SequentialUnification.nextAxiomWithFuel? nestedRankBudget
        nestedRankBudgetEmpty nestedRankBudgetSourceIndex
        (SequentialUnification.sourceIndex_sound nestedRankBudget)
        3 (Array.replicate nestedRankBudget.formulas.size false) 7 =
          some result := by
  have success :
      ∃ result,
        SequentialUnification.nextAxiomWithFuel? nestedRankBudget
          nestedRankBudgetEmpty nestedRankBudgetSourceIndex
          (SequentialUnification.sourceIndex_sound nestedRankBudget)
          (nestedRankBudget.formulaComplexityAt 7 + 1)
          (Array.replicate nestedRankBudget.formulas.size false) 7 =
            some result := by
    apply
      SequentialUnification.nextAxiomWithFuel?_exists_of_structural_carrierClear
        (nestedRankBudget.wellFormed_iff_structurallyWellFormed.mp
          (by native_decide))
        nestedRankBudgetEmpty_abstractable (by native_decide)
    intro candidate candidateBound
    constructor
    · simp [candidateBound]
    · exact nestedRankBudgetEmpty_assignedToken?_eq_none candidate
  rw [nestedRankBudget_startComplexity] at success
  simpa using success

example :
    (SequentialUnification.nextAxiomWithFuel? nestedRankBudget
      nestedRankBudgetEmpty nestedRankBudgetSourceIndex
      (SequentialUnification.sourceIndex_sound nestedRankBudget)
      3 (Array.replicate nestedRankBudget.formulas.size false) 7).isSome =
        true := by
  native_decide

def canonicalNextAxiom :=
  SequentialUnification.nextAxiom? canonical canonicalSequentialEmpty
    canonicalSourceIndex
    (SequentialUnification.sourceIndex_sound canonical)
    (Array.replicate canonical.formulas.size false) 4

/-- Starting from the par conclusion reaches stored-right axiom endpoint `1`.
This regression prevents future Figure-7 code from confusing the submitted
`left/right` order with the direction in which `NEXTAXIOM` found the axiom. -/
def canonicalStoredRightNextAxiom :=
  SequentialUnification.nextAxiom? canonical canonicalSequentialEmpty
    canonicalSourceIndex
    (SequentialUnification.sourceIndex_sound canonical)
    (Array.replicate canonical.formulas.size false) 5

example :
    (match canonicalStoredRightNextAxiom with
    | none => false
    | some result =>
        result.linkIndex == 0 &&
          result.left == 0 &&
          result.right == 1 &&
          result.trace == [5, 1]) = true := by
  native_decide

/-- Every successful stored-right regression result carries an oriented route;
the route's `traceLast` identifies the reached endpoint independently of the
submitted axiom orientation. -/
example {result}
    (equation : canonicalStoredRightNextAxiom = some result) :
    ∃ reached partner,
      SequentialUnification.NextAxiomRoute 5 result reached partner := by
  exact SequentialUnification.nextAxiom?_route (by
    simpa [canonicalStoredRightNextAxiom] using equation)

example :
    (match canonicalNextAxiom with
    | none => false
    | some result =>
        result.linkIndex == 0 &&
          result.left == 0 &&
          result.right == 1 &&
          result.trace == [4, 0] &&
          result.tags[4]? == some true &&
          result.tags[0]? == some true &&
          result.tags[1]? == some true) = true := by
  native_decide

example :
    (match canonicalNextAxiom with
    | none => false
    | some result =>
        (SequentialUnification.nextAxiom? canonical
          canonicalSequentialEmpty canonicalSourceIndex
          (SequentialUnification.sourceIndex_sound canonical)
          result.tags 4).isNone) = true := by
  native_decide

/-- Thread the first search's output tags into a disjoint second axiom start.
This is the executable counterpart of
`nextAxiomWithFuel?_threaded_touched_disjoint`; restarting from the original
tag array is intentionally outside that theorem's claim. -/
example :
    (match canonicalNextAxiom with
    | none => false
    | some first =>
        match SequentialUnification.nextAxiom? canonical
            canonicalSequentialEmpty canonicalSourceIndex
            (SequentialUnification.sourceIndex_sound canonical)
            first.tags 2 with
        | none => false
        | some second =>
            second.linkIndex == 1 &&
              second.trace == [2] &&
              second.tags[2]? == some true &&
              second.tags[3]? == some true &&
              second.tags[4]? == some true &&
              second.tags[0]? == some true &&
              second.tags[1]? == some true) = true := by
  native_decide

example :
    SequentialUnification.nextAxiom? canonical canonicalSequentialEmpty
      canonicalSourceIndex
      (SequentialUnification.sourceIndex_sound canonical)
      ((Array.replicate canonical.formulas.size false).setIfInBounds 4 true)
      4 = none := by
  native_decide

example :
    SequentialUnification.nextAxiomWithFuel? canonical
      canonicalSequentialEmpty canonicalSourceIndex
      (SequentialUnification.sourceIndex_sound canonical)
      0 (Array.replicate canonical.formulas.size false) 4 = none := by
  native_decide

example :
    SequentialUnification.nextAxiom? canonical canonicalSequentialEmpty
      canonicalSourceIndex
      (SequentialUnification.sourceIndex_sound canonical)
      (Array.replicate canonical.formulas.size false)
      canonical.formulas.size = none := by
  native_decide

example :
    SequentialUnification.nextAxiom? canonical
      { canonicalSequentialEmpty with
        marks :=
          canonicalSequentialEmpty.marks.setIfInBounds 4 (some 0) }
      canonicalSourceIndex
      (SequentialUnification.sourceIndex_sound canonical)
      (Array.replicate canonical.formulas.size false) 4 = none := by
  native_decide

/-- Deliberately malformed: vertex `4` has no submitted source link. -/
def canonicalMissingSource : Certificate where
  formulas := canonical.formulas
  links := [
    .axiom 0 1,
    .axiom 2 3,
    .par 1 3 5
  ]
  conclusions := canonical.conclusions

example :
    SequentialUnification.nextAxiom? canonicalMissingSource
      canonicalSequentialEmpty
      (SequentialUnification.sourceIndex canonicalMissingSource)
      (SequentialUnification.sourceIndex_sound canonicalMissingSource)
      (Array.replicate canonicalMissingSource.formulas.size false)
      4 = none := by
  native_decide

/-- Deliberately malformed: vertex `4` has two submitted source links.
`NEXTAXIOM` must reject the non-unique source bucket rather than choose one. -/
def canonicalDuplicateSource : Certificate where
  formulas := canonical.formulas
  links := .tensor 0 2 4 :: canonical.links
  conclusions := canonical.conclusions

example :
    SequentialUnification.nextAxiom? canonicalDuplicateSource
      canonicalSequentialEmpty
      (SequentialUnification.sourceIndex canonicalDuplicateSource)
      (SequentialUnification.sourceIndex_sound canonicalDuplicateSource)
      (Array.replicate canonicalDuplicateSource.formulas.size false)
      4 = none := by
  native_decide

example :
    (match SequentialUnification.dynamicStartWithFuel? canonical
        canonicalSequentialEmpty canonicalSourceIndex
        (SequentialUnification.sourceIndex_sound canonical)
        canonical.formulas.size
        (Array.replicate canonical.formulas.size false) 4 with
    | none => false
    | some result =>
        result.after.parents == #[0] &&
          result.after.startedAxioms == 1 &&
          result.after.assignedToken? 0 == some 0 &&
          result.after.assignedToken? 1 == some 0) = true := by
  native_decide

namespace SequentialSchedulerStateTests

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialFigure7

/-- A representative raw-age interval stack: `[0,2,5]` partitions ages below
`7` into intervals beginning at exactly those boundaries. -/
theorem validSigmaSeven : SigmaAgePartition 7 [0, 2, 5] := by
  exact {
    empty_iff := by simp
    head_zero := by simp
    strictIncreasing := by decide
    boundary_lt := by
      intro boundary membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl | rfl | rfl <;> decide }

example : sigmaBoundary? [0, 2, 5] 0 = some 0 := by native_decide
example : sigmaBoundary? [0, 2, 5] 1 = some 0 := by native_decide
example : sigmaBoundary? [0, 2, 5] 2 = some 2 := by native_decide
example : sigmaBoundary? [0, 2, 5] 4 = some 2 := by native_decide
example : sigmaBoundary? [0, 2, 5] 5 = some 5 := by native_decide
example : sigmaBoundary? [0, 2, 5] 6 = some 5 := by native_decide

/-- Duplicate interval boundaries violate strict increase. -/
example : ¬ SigmaAgePartition 7 [0, 2, 2] := by
  intro partition
  have impossible : (2 : Nat) < 2 :=
    List.rel_of_pairwise_cons partition.strictIncreasing.tail (by simp)
  exact (Nat.lt_irrefl 2 impossible)

/-- A nonempty raw-age partition must begin at boundary zero. -/
example : ¬ SigmaAgePartition 7 [1, 2] := by
  intro partition
  have headZero := partition.head_zero (by decide)
  have impossible : (1 : Nat) = 0 := Option.some.inj headZero
  omega

/-- Every boundary must be strictly below the raw-age horizon. -/
example : ¬ SigmaAgePartition 7 [0, 2, 7] := by
  intro partition
  have boundaryBound := partition.boundary_lt 7 (by simp)
  exact (Nat.lt_irrefl 7 boundaryBound)

def waitingDistinction : Array WaitingCell :=
  #[.undefined, .initialized []]

/-- Out-of-bounds, `⊥`, and initialized `∅` are three executable lookup
outcomes, not three spellings of the same state. -/
example :
    waitingDistinction[2]? = none ∧
    waitingDistinction[0]? = some .undefined ∧
    waitingDistinction[1]? = some (.initialized []) := by
  native_decide

example : WaitingCell.undefined ≠ WaitingCell.initialized [] :=
  WaitingCell.undefined_ne_initialized_empty

/-- Truly empty fixed-carrier scheduler storage. -/
def delayedInitial : SequentialStackState :=
  SequentialStackState.empty canonical.formulas.size

/-- The exact production empty core and delayed empty stack agree before the
first reservation. -/
example :
    RealizesSigma delayedInitial canonical.initialUnificationState := by
  exact initial_realizesSigma canonical

/-- Expected delayed `init` output.  The `(1,0)` endpoint order locks the
stored-right `NEXTAXIOM` fixture semantics. -/
def delayedAfterInit : SequentialStackState where
  marks := Array.replicate canonical.formulas.size none
  nextAge := 1
  sigma := [0]
  ready := [[1, 0]]
  waiting := Array.replicate canonical.formulas.size .undefined

example :
    initEnqueue? delayedInitial 1 0 = some delayedAfterInit := by
  native_decide

/-- Strict delayed initialization rejects a premarked carrier. -/
example :
    initEnqueue?
      { delayedInitial with
        marks := delayedInitial.marks.setIfInBounds 1 (some 0) }
      1 0 = none := by
  native_decide

/-- Strict delayed initialization also rejects a waiting table that is not
entirely paper-level `undefined`. -/
example :
    initEnqueue?
      { delayedInitial with
        waiting :=
          delayedInitial.waiting.setIfInBounds 0 (.initialized []) }
      1 0 = none := by
  native_decide

theorem delayedAfterInit_wellShaped :
    delayedAfterInit.WellShaped canonical.formulas.size := by
  exact initEnqueue?_wellShaped
    (reached := 1) (partner := 0)
    (SequentialStackState.empty_wellShaped canonical.formulas.size)
    (by native_decide)

/-- The reserved raw age has an actual in-bounds waiting cell; its content is
the separately checked paper-level `undefined`, not array `none`. -/
example :
    ∃ cell, delayedAfterInit.waiting[0]? = some cell := by
  exact delayedAfterInit_wellShaped.waiting_lookup_exists (by decide)

example :
    delayedAfterInit.waiting[0]? = some .undefined ∧
    delayedAfterInit.marks[1]? = some none ∧
    delayedAfterInit.marks[0]? = some none := by
  native_decide

example :
    delayedAfterInit.marks[1]? = some none ∧
      delayedAfterInit.marks[0]? = some none := by
  exact initEnqueue?_endpoint_unmarked
    (state := delayedInitial) (after := delayedAfterInit)
    (reached := 1) (partner := 0) (by native_decide)

/-- Re-run the stored-right search against the exact public production empty
core used by the scheduler bridge. -/
def canonicalStoredRightBridgeNextAxiom :=
  SequentialUnification.nextAxiom? canonical
    canonical.initialUnificationState canonicalSourceIndex
    (SequentialUnification.sourceIndex_sound canonical)
    (Array.replicate canonical.formulas.size false) 5

/-- The exact bridge search result carries a kernel-checked oriented route. -/
example {result}
    (equation :
      canonicalStoredRightBridgeNextAxiom = some result) :
    ∃ reached partner,
      SequentialUnification.NextAxiomRoute
        5 result reached partner := by
  exact SequentialUnification.nextAxiom?_route (by
    simpa [canonicalStoredRightBridgeNextAxiom] using equation)

/-- One and the same successful result controls both sides of the bridge:
the production component keeps submitted frontier `[0,1]`, while the delayed
ready bucket keeps search orientation `[1,0]`. -/
example :
    (match canonicalStoredRightBridgeNextAxiom with
    | none => false
    | some result =>
        result.orientedEndpoints? == some (1, 0) &&
        match
            initEnqueue? delayedInitial 1 0,
            canonical.reserveAxiomAt?
              canonical.initialUnificationState result.linkIndex with
        | some stackAfter, some coreAfter =>
            stackAfter.ready == [[1, 0]] &&
            coreAfter.parents == #[0] &&
            coreAfter.startedAxioms == 1 &&
            coreAfter.firedConnectives == 0 &&
            coreAfter.marks == canonical.initialUnificationState.marks &&
            match coreAfter.components[0]? with
            | some (some component) =>
                component.frontier == [0, 1]
            | _ => false
        | _, _ => false) = true := by
  native_decide

/-- The route-bound theorem uses that same result's `linkIndex` for the
submitted-orientation reservation and its reached/partner pair for delayed
enqueueing. -/
example
    {result :
      SequentialUnification.NextAxiomResult canonical
        canonical.initialUnificationState canonical.formulas.size
        (Array.replicate canonical.formulas.size false)}
    {stackAfter : SequentialStackState}
    {coreAfter : UnificationState}
    (route :
      SequentialUnification.NextAxiomRoute 5 result 1 0)
    (stackEquation :
      initEnqueue? delayedInitial 1 0 = some stackAfter)
    (coreEquation :
      canonical.reserveAxiomAt?
          canonical.initialUnificationState result.linkIndex =
        some coreAfter) :
    result.orientedEndpoints? = some (1, 0) ∧
      RealizesSigma stackAfter coreAfter := by
  exact init_reserve_route_exact route stackEquation coreEquation

/-- The stronger route-bound corollary exposes both endpoint orders for every
successful first bridge step, not just for the executable canonical fixture. -/
example
    {result :
      SequentialUnification.NextAxiomResult canonical
        canonical.initialUnificationState canonical.formulas.size
        (Array.replicate canonical.formulas.size false)}
    {stackAfter : SequentialStackState}
    {coreAfter : UnificationState}
    (route :
      SequentialUnification.NextAxiomRoute 5 result 1 0)
    (stackEquation :
      initEnqueue? delayedInitial 1 0 = some stackAfter)
    (coreEquation :
      canonical.reserveAxiomAt?
          canonical.initialUnificationState result.linkIndex =
        some coreAfter) :
    result.orientedEndpoints? = some (1, 0) ∧
      stackAfter.ready = [[1, 0]] ∧
      ∃ component,
        coreAfter.components = #[some component] ∧
        component.frontier = [result.left, result.right] ∧
        RealizesSigma stackAfter coreAfter := by
  exact init_reserve_route_fields route stackEquation coreEquation

/-- A reservation index must designate an axiom link. -/
example :
    canonical.reserveAxiomAt?
        canonical.initialUnificationState 2 = none := by
  native_decide

/-- An out-of-bounds reservation index fails closed. -/
example :
    canonical.reserveAxiomAt?
        canonical.initialUnificationState 99 = none := by
  native_decide

/-- Local axiom well-formedness is checked rather than inferred from the
low-level component constructor. -/
def malformedReservationCertificate : Certificate where
  formulas := #[p, pDual, q]
  links := [.axiom 0 2]
  conclusions := [0, 2]

example :
    malformedReservationCertificate.reserveAxiomAt?
        malformedReservationCertificate.initialUnificationState 0 =
      none := by
  native_decide

/-- Reservation is delayed but still requires both submitted endpoints to be
currently unmarked. -/
def canonicalMarkedReservationState : UnificationState :=
  { canonical.initialUnificationState with
    marks :=
      canonical.initialUnificationState.marks.setIfInBounds
        0 (some 0) }

example :
    canonical.reserveAxiomAt? canonicalMarkedReservationState 0 =
      none := by
  native_decide

/-- The component and parent carriers must be aligned before a reservation. -/
def canonicalMisalignedReservationState : UnificationState :=
  { canonical.initialUnificationState with
    components := #[none] }

example :
    canonical.reserveAxiomAt? canonicalMisalignedReservationState 0 =
      none := by
  native_decide

/-- Literal output of the `new` line as printed in Figure 7.  This fixture is
kept as an auditable negative control: it initializes fresh `W(1)` and therefore
does not satisfy the operational waiting-domain invariant. -/
def delayedAfterLiteralNew : SequentialStackState where
  marks := Array.replicate canonical.formulas.size none
  nextAge := 2
  sigma := [0, 1]
  ready := [[1, 0], [3, 2]]
  waiting :=
    (Array.replicate canonical.formulas.size .undefined).setIfInBounds
      1 (.initialized [])

example :
    newEnqueue? delayedAfterInit 3 2 = some delayedAfterLiteralNew := by
  native_decide

/-- The literal transcription still fails closed on an already marked
endpoint.  Production scheduling does not call this display-level helper. -/
example :
    newEnqueue?
      { delayedAfterInit with
        marks := delayedAfterInit.marks.setIfInBounds 3 (some 0) }
      3 2 = none := by
  native_decide

/-- The literal transcription also rejects a fresh cell that was already
initialized. -/
example :
    newEnqueue?
      { delayedAfterInit with
        waiting :=
          delayedAfterInit.waiting.setIfInBounds 1 (.initialized []) }
      3 2 = none := by
  native_decide

theorem delayedAfterLiteralNew_wellShaped :
    delayedAfterLiteralNew.WellShaped canonical.formulas.size := by
  exact newEnqueue?_wellShaped delayedAfterInit_wellShaped
    (reached := 3) (partner := 2)
    (by native_decide)

example :
    delayedAfterLiteralNew.marks = delayedAfterInit.marks ∧
    delayedAfterLiteralNew.sigma = delayedAfterInit.sigma ++ [1] ∧
    delayedAfterLiteralNew.ready = delayedAfterInit.ready ++ [[3, 2]] ∧
    delayedAfterLiteralNew.waiting[0]? = some .undefined ∧
    delayedAfterLiteralNew.waiting[1]? = some (.initialized []) := by
  native_decide

example :
    delayedAfterLiteralNew.marks[3]? = some none ∧
      delayedAfterLiteralNew.marks[2]? = some none := by
  exact newEnqueue?_endpoint_unmarked
    (state := delayedAfterInit) (after := delayedAfterLiteralNew)
    (reached := 3) (partner := 2) (by native_decide)

/-- Operational `new` initializes the old active boundary `W(0)` and leaves the
fresh top `W(1)` undefined. -/
def delayedAfterOperationalNew : SequentialStackState where
  marks := Array.replicate canonical.formulas.size none
  nextAge := 2
  sigma := [0, 1]
  ready := [[1, 0], [3, 2]]
  waiting :=
    (Array.replicate canonical.formulas.size .undefined).setIfInBounds
      0 (.initialized [])

example :
    operationalNewEnqueue? delayedAfterInit 3 2 =
      some delayedAfterOperationalNew := by
  native_decide

theorem delayedAfterInit_operationalWaitingDomain :
    delayedAfterInit.OperationalWaitingDomain := by
  exact initEnqueue?_operationalWaitingDomain
    (state := delayedInitial) (after := delayedAfterInit)
    (reached := 1) (partner := 0) (by native_decide)

theorem delayedAfterOperationalNew_wellShaped :
    delayedAfterOperationalNew.WellShaped canonical.formulas.size := by
  exact operationalNewEnqueue?_wellShaped delayedAfterInit_wellShaped
    (reached := 3) (partner := 2) (by native_decide)

theorem delayedAfterOperationalNew_operationalWaitingDomain :
    delayedAfterOperationalNew.OperationalWaitingDomain := by
  exact operationalNewEnqueue?_operationalWaitingDomain
    delayedAfterInit_operationalWaitingDomain
    delayedAfterInit_wellShaped
    (reached := 3) (partner := 2) (by native_decide)

/-- The source-literal and operational outputs are deliberately distinct. -/
example :
    delayedAfterLiteralNew ≠ delayedAfterOperationalNew := by
  native_decide

/-- The source-literal fresh-cell write violates the production domain:
inactive boundary zero remains undefined. -/
example :
    ¬ delayedAfterLiteralNew.OperationalWaitingDomain := by
  intro domain
  have initialized :
      delayedAfterLiteralNew.WaitingInitializedAt 0 :=
    (domain.initialized_iff_inactive (age := 0) (by native_decide)).mpr
      (by native_decide)
  rcases initialized with ⟨payload, equation⟩
  have lookup :
      delayedAfterLiteralNew.waiting[0]? = some .undefined := by
    native_decide
  rw [lookup] at equation
  cases equation

example :
    delayedAfterOperationalNew.marks = delayedAfterInit.marks ∧
    delayedAfterOperationalNew.sigma = delayedAfterInit.sigma ++ [1] ∧
    delayedAfterOperationalNew.ready = delayedAfterInit.ready ++ [[3, 2]] ∧
    delayedAfterOperationalNew.waiting[0]? = some (.initialized []) ∧
    delayedAfterOperationalNew.waiting[1]? = some .undefined := by
  native_decide

example :
    delayedAfterOperationalNew.marks[3]? = some none ∧
      delayedAfterOperationalNew.marks[2]? = some none := by
  exact operationalNewEnqueue?_endpoint_unmarked
    (state := delayedAfterInit) (after := delayedAfterOperationalNew)
    (reached := 3) (partner := 2) (by native_decide)

/-- The domain theorem, rather than a fixture computation, recovers the
undefined fresh top from the new active `sigma` boundary. -/
example :
    delayedAfterOperationalNew.waiting[1]? = some .undefined := by
  exact
    delayedAfterOperationalNew_operationalWaitingDomain.active_undefined
      delayedAfterOperationalNew_wellShaped (by native_decide)

/-- Operational `new` cannot reuse an old active boundary whose waiting cell
has already been initialized. -/
example :
    operationalNewEnqueue?
      { delayedAfterInit with
        waiting :=
          delayedAfterInit.waiting.setIfInBounds 0 (.initialized []) }
      3 2 = none := by
  native_decide

/-- Operational `new` also rejects a fresh top that is not unused. -/
example :
    operationalNewEnqueue?
      { delayedAfterInit with
        waiting :=
          delayedAfterInit.waiting.setIfInBounds 1 (.initialized []) }
      3 2 = none := by
  native_decide

/-- A later reservation must also reject an endpoint already stored by an
inactive waiting payload.  Checking only `ready.flatten` would accept this
state and later reintroduce vertex 5 when `W(0)` is drained. -/
def delayedWithWaitingEndpoint : SequentialStackState :=
  { delayedAfterOperationalNew with
    waiting :=
      delayedAfterOperationalNew.waiting.setIfInBounds
        0 (.initialized [5]) }

example :
    delayedWithWaitingEndpoint.waitingVertices = [5] ∧
      5 ∉ delayedWithWaitingEndpoint.ready.flatten ∧
      5 ∈ delayedWithWaitingEndpoint.queuedVertices := by
  native_decide

/-- Every condition from the former ready-only guard still holds; the sole
newly exposed conflict is membership in the waiting payload.  This prevents
the negative regression from passing because of an unrelated side guard. -/
example :
    0 < delayedWithWaitingEndpoint.nextAge ∧
      delayedWithWaitingEndpoint.sigma.getLast? = some 1 ∧
      1 < delayedWithWaitingEndpoint.nextAge ∧
      5 < delayedWithWaitingEndpoint.marks.size ∧
      4 < delayedWithWaitingEndpoint.marks.size ∧
      5 ≠ 4 ∧
      5 ∉ delayedWithWaitingEndpoint.ready.flatten ∧
      4 ∉ delayedWithWaitingEndpoint.ready.flatten ∧
      delayedWithWaitingEndpoint.marks[5]? = some none ∧
      delayedWithWaitingEndpoint.marks[4]? = some none ∧
      delayedWithWaitingEndpoint.waiting[1]? = some .undefined ∧
      delayedWithWaitingEndpoint.waiting[
        delayedWithWaitingEndpoint.nextAge]? = some .undefined := by
  native_decide

example :
    operationalNewEnqueue? delayedWithWaitingEndpoint 5 4 = none := by
  native_decide

/-- A second primitive-only operational reservation initializes the previous
top and again leaves the newly allocated top undefined. -/
def delayedAfterSecondOperationalNew : SequentialStackState where
  marks := Array.replicate canonical.formulas.size none
  nextAge := 3
  sigma := [0, 1, 2]
  ready := [[1, 0], [3, 2], [5, 4]]
  waiting :=
    ((Array.replicate canonical.formulas.size .undefined).setIfInBounds
      0 (.initialized [])).setIfInBounds 1 (.initialized [])

example :
    operationalNewEnqueue? delayedAfterOperationalNew 5 4 =
      some delayedAfterSecondOperationalNew := by
  native_decide

example :
    delayedAfterSecondOperationalNew.waiting[0]? =
        some (.initialized []) ∧
      delayedAfterSecondOperationalNew.waiting[1]? =
        some (.initialized []) ∧
      delayedAfterSecondOperationalNew.waiting[2]? = some .undefined := by
  native_decide

/-- Executable first reservation, including exact route recovery, submitted
component creation, and complete tag threading. -/
def canonicalInitialReservation : Option ReservationState :=
  initializeReservation? canonical 5

/-- The second call consumes the first call's state without resetting tags. -/
def canonicalTwoReservations : Option ReservationState := do
  let first ← canonicalInitialReservation
  reserveNewAxiom? canonical first 3

example :
    (match canonicalInitialReservation with
    | none => false
    | some first =>
        first.stack == delayedAfterInit &&
        first.core.parents == #[0] &&
        first.core.startedAxioms == 1 &&
        first.tags[0]? == some true &&
        first.tags[1]? == some true &&
        first.tags[5]? == some true &&
        match first.core.components[0]? with
        | some (some component) =>
            component.frontier == [0, 1]
        | _ => false) = true := by
  native_decide

/-- The later production call reserves the other submitted axiom, appends the
search-oriented `[3,2]` bucket, initializes the old active waiting boundary,
and leaves the fresh top undefined. -/
example :
    (match canonicalTwoReservations with
    | none => false
    | some after =>
        after.stack == delayedAfterOperationalNew &&
        after.core.parents == #[0, 1] &&
        after.core.startedAxioms == 2 &&
        after.core.firedConnectives == 0 &&
        after.tags[0]? == some true &&
        after.tags[1]? == some true &&
        after.tags[2]? == some true &&
        after.tags[3]? == some true &&
        after.tags[5]? == some true &&
        match after.core.components[0]?, after.core.components[1]? with
        | some (some first), some (some second) =>
            first.frontier == [0, 1] &&
            second.frontier == [2, 3]
        | _, _ => false) = true := by
  native_decide

/-- Complete tag threading makes a replay search from the old start fail. -/
example :
    (match canonicalInitialReservation with
    | none => false
    | some first =>
        (reserveNewAxiom? canonical first 5).isNone) = true := by
  native_decide

/-- Resetting tags is outside the wrapper invariant.  The low-level search can
then rediscover an already reserved axiom, demonstrating why tag provenance is
semantically material independently of the stack transition. -/
example :
    (match canonicalInitialReservation with
    | none => false
    | some first =>
        (SequentialUnification.nextAxiom? canonical first.core
          (SequentialUnification.sourceIndex canonical)
          (SequentialUnification.sourceIndex_sound canonical)
          (Array.replicate canonical.formulas.size false) 5).isSome) = true := by
  native_decide

/-- Even under that deliberately invalid tag reset, the operational wrapper
fails closed because it also forbids re-enqueueing endpoints already present in
the ready stack. -/
example :
    (match canonicalInitialReservation with
    | none => false
    | some first =>
        (reserveNewAxiom? canonical
          { first with
            tags := Array.replicate canonical.formulas.size false }
          5).isNone) = true := by
  native_decide

theorem canonicalInitialReservation_invariant {after : ReservationState}
    (equation :
      canonicalInitialReservation = some after) :
    ReservationInvariant canonical after := by
  rcases initializeReservation?_some_iff.mp (by
      simpa [canonicalInitialReservation] using equation) with
    ⟨step⟩
  exact step.reservationInvariant

/-! Exact executable Figure-7 `concl` and `nop` base rules. -/

/-- The one-axiom proof net makes both axiom endpoints explicit conclusions.
Its first delayed reservation therefore feeds `concl`, not a connective rule. -/
def axiomOnly : Certificate where
  formulas := #[p, pDual]
  links := [.axiom 0 1]
  conclusions := [0, 1]

def axiomOnlyInitial : Option ReservationState :=
  initializeReservation? axiomOnly 0

theorem axiomOnlyInitial_invariant {before : ReservationState}
    (equation : axiomOnlyInitial = some before) :
    ReservationInvariant axiomOnly before := by
  rcases initializeReservation?_some_iff.mp (by
      simpa [axiomOnlyInitial] using equation) with
    ⟨initialStep⟩
  exact initialStep.reservationInvariant

/-- The explicit conclusion query requires both boundary membership and an
exactly empty consumer bucket. -/
example :
    (axiomOnly.conclusionBelow? 0).isSome = true := by
  native_decide

def axiomOnlyConclTransition : Option ReservationState :=
  match equation : axiomOnlyInitial with
  | none => none
  | some before =>
      SequentialFigure7.concl? axiomOnly before
        (axiomOnlyInitial_invariant equation)

/-- `concl` performs only the common pop/raw-mark prefix. -/
example :
    (match axiomOnlyConclTransition with
    | none => false
    | some after =>
        after.stack.marks[0]? == some (some 0) &&
        after.stack.marks[1]? == some none &&
        after.stack.ready == [[1]] &&
        after.stack.sigma == [0] &&
        after.stack.waiting[0]? == some .undefined &&
        after.core.marks == after.stack.marks &&
        after.core.parents == #[0] &&
        after.core.startedAxioms == 1 &&
        after.core.firedConnectives == 0) = true := by
  native_decide

/-- The concrete `concl` prefix changes only the selected raw mark and ready
top: age allocation, sigma boundaries, waiting storage, production metadata,
and search tags are all retained exactly. -/
example :
    (match equation : axiomOnlyInitial with
    | none => false
    | some before =>
        match SequentialFigure7.concl? axiomOnly before
            (axiomOnlyInitial_invariant equation) with
        | none => false
        | some after =>
            after.stack.nextAge == before.stack.nextAge &&
            after.stack.sigma == before.stack.sigma &&
            after.stack.waiting == before.stack.waiting &&
            after.core.parents == before.core.parents &&
            after.core.components == before.core.components &&
            after.core.startedAxioms == before.core.startedAxioms &&
            after.core.firedConnectives == before.core.firedConnectives &&
            after.tags == before.tags) = true := by
  native_decide

example {before after : ReservationState}
    (initialEquation : axiomOnlyInitial = some before)
    (conclEquation :
      SequentialFigure7.concl? axiomOnly before
          (axiomOnlyInitial_invariant initialEquation) =
        some after) :
    ReservationInvariant axiomOnly after :=
  SequentialFigure7.concl?_reservationInvariant
    (axiomOnlyInitial_invariant initialEquation) conclEquation

/-- The executable conclusion step exposes the independent Boolean-free rule
relation, and structural validity makes that relation complete. -/
example {before after : ReservationState}
    (initialEquation : axiomOnlyInitial = some before)
    (conclEquation :
      SequentialFigure7.concl? axiomOnly before
          (axiomOnlyInitial_invariant initialEquation) =
        some after) :
    SequentialFigure7.ConclRule axiomOnly before after :=
  SequentialFigure7.concl?_sound
    (axiomOnlyInitial_invariant initialEquation) conclEquation

example {before after : ReservationState}
    (initialEquation : axiomOnlyInitial = some before)
    (rule : SequentialFigure7.ConclRule axiomOnly before after) :
    SequentialFigure7.concl? axiomOnly before
        (axiomOnlyInitial_invariant initialEquation) =
      some after :=
  SequentialFigure7.concl?_complete_of_structural
    (axiomOnly.wellFormed_iff_structurallyWellFormed.mp
      (by native_decide))
    (axiomOnlyInitial_invariant initialEquation) rule

example {before first second : ReservationState}
    (left : SequentialFigure7.ConclRule axiomOnly before first)
    (right : SequentialFigure7.ConclRule axiomOnly before second) :
    first = second :=
  left.output_unique right

/-- A deliberately malformed explicit boundary has two distinct consumer
slots.  The singleton query and an empty bucket can both appear as `none` at
the `Option` level, so `concl` uses the exact bucket equation and rejects this
case. -/
def ambiguousBoundary : Certificate where
  formulas := #[p, pDual, q, qDual, .tensor p q, .par pDual qDual]
  links := [
    .axiom 0 1,
    .axiom 2 3,
    .tensor 0 2 4,
    .par 1 3 5,
    .par 4 0 5,
    .tensor 4 1 5
  ]
  conclusions := [4, 5]

example :
    ambiguousBoundary.consumerIndex.uniqueConsumer? 4 = none ∧
      ambiguousBoundary.consumerIndex.bucket 4 ≠ [] ∧
      (ambiguousBoundary.connectiveBelow? 4).isNone = true ∧
      (ambiguousBoundary.conclusionBelow? 4).isNone = true := by
  native_decide

/-- `ConclRule` deliberately states only the paper-level boundary predicate.
It can therefore be inhabited on malformed input; the executable-completeness
theorem cannot be applied because structural well-formedness is false. -/
def malformedConclBefore : ReservationState where
  stack := {
    marks := Array.replicate ambiguousBoundary.formulas.size none
    nextAge := 1
    sigma := [0]
    ready := [[4]]
    waiting :=
      Array.replicate ambiguousBoundary.formulas.size .undefined }
  core := {
    marks := Array.replicate ambiguousBoundary.formulas.size none
    parents := #[]
    components := #[]
    startedAxioms := 0
    firedConnectives := 0 }
  tags := Array.replicate ambiguousBoundary.formulas.size false

def malformedConclAfter : ReservationState where
  stack := {
    malformedConclBefore.stack with
    marks :=
      malformedConclBefore.stack.marks.setIfInBounds 4 (some 0)
    ready := [[]] }
  core := {
    malformedConclBefore.core with
    marks :=
      malformedConclBefore.core.marks.setIfInBounds 4 (some 0) }
  tags := malformedConclBefore.tags

example :
    SequentialFigure7.ConclRule ambiguousBoundary
      malformedConclBefore malformedConclAfter := by
  refine ⟨4, 0, ?_, by simp [ambiguousBoundary]⟩
  exact ⟨[], [], [], by native_decide, by native_decide,
    by native_decide, by native_decide, rfl, rfl, rfl⟩

example :
    ¬ Certificate.StructurallyWellFormed ambiguousBoundary := by
  intro structural
  have accepted : ambiguousBoundary.wellFormed = true :=
    ambiguousBoundary.wellFormed_iff_structurallyWellFormed.mpr
      structural
  have rejected : ambiguousBoundary.wellFormed = false := by
    native_decide
  rw [rejected] at accepted
  cases accepted

/-- Declared boundaries that are out of range or have no source incidence are
also rejected rather than being accepted solely because their consumer bucket
is empty. -/
def outOfRangeBoundary : Certificate where
  formulas := #[p, pDual]
  links := [.axiom 0 1]
  conclusions := [2]

def unproducedBoundary : Certificate where
  formulas := #[p]
  links := []
  conclusions := [0]

example :
    (outOfRangeBoundary.conclusionBelow? 2).isNone = true ∧
      (unproducedBoundary.conclusionBelow? 0).isNone = true := by
  native_decide

/-- The canonical first reservation exposes selected premise `1` below the
submitted par at slot `3`; its mate `3` remains raw unmarked, so the exact
Figure-7 rule is `nop`. -/
example :
    (match canonical.connectiveBelow? 1 with
    | none => false
    | some consumer =>
        consumer.kind == .par &&
        consumer.linkIndex == 3 &&
        consumer.storedLeft == 1 &&
        consumer.storedRight == 3 &&
        consumer.conclusion == 5 &&
        consumer.premise == 1 &&
        consumer.mate == 3) = true := by
  native_decide

def canonicalNopTransition : Option ReservationState :=
  match equation : canonicalInitialReservation with
  | none => none
  | some before =>
      SequentialFigure7.nop? canonical before
        (canonicalInitialReservation_invariant equation)

example :
    (match canonicalNopTransition with
    | none => false
    | some after =>
        after.stack.marks[1]? == some (some 0) &&
        after.stack.marks[0]? == some none &&
        after.stack.ready == [[0]] &&
        after.stack.sigma == [0] &&
        after.stack.waiting[0]? == some .undefined &&
        after.core.marks == after.stack.marks &&
        after.core.parents == #[0] &&
        after.core.startedAxioms == 1 &&
        after.core.firedConnectives == 0) = true := by
  native_decide

/-- The concrete `nop` prefix likewise preserves every non-prefix field,
including the complete tag array. -/
example :
    (match equation : canonicalInitialReservation with
    | none => false
    | some before =>
        match SequentialFigure7.nop? canonical before
            (canonicalInitialReservation_invariant equation) with
        | none => false
        | some after =>
            after.stack.nextAge == before.stack.nextAge &&
            after.stack.sigma == before.stack.sigma &&
            after.stack.waiting == before.stack.waiting &&
            after.core.parents == before.core.parents &&
            after.core.components == before.core.components &&
            after.core.startedAxioms == before.core.startedAxioms &&
            after.core.firedConnectives == before.core.firedConnectives &&
            after.tags == before.tags) = true := by
  native_decide

example {before after : ReservationState}
    (initialEquation : canonicalInitialReservation = some before)
    (nopEquation :
      SequentialFigure7.nop? canonical before
          (canonicalInitialReservation_invariant initialEquation) =
        some after) :
    ReservationInvariant canonical after :=
  SequentialFigure7.nop?_reservationInvariant
    (canonicalInitialReservation_invariant initialEquation) nopEquation

/-- The canonical stored-left par step satisfies the independent pre-state
rule and the structural completeness direction reconstructs the exact same
executable output. -/
example {before after : ReservationState}
    (initialEquation : canonicalInitialReservation = some before)
    (nopEquation :
      SequentialFigure7.nop? canonical before
          (canonicalInitialReservation_invariant initialEquation) =
        some after) :
    SequentialFigure7.NopRule canonical before after :=
  SequentialFigure7.nop?_sound
    (canonicalInitialReservation_invariant initialEquation) nopEquation

example {before after : ReservationState}
    (initialEquation : canonicalInitialReservation = some before)
    (rule : SequentialFigure7.NopRule canonical before after) :
    SequentialFigure7.nop? canonical before
        (canonicalInitialReservation_invariant initialEquation) =
      some after :=
  SequentialFigure7.nop?_complete_of_structural
    (canonical.wellFormed_iff_structurallyWellFormed.mp
      (by native_decide))
    (canonicalInitialReservation_invariant initialEquation) rule

/-- The same executable `nop` handles a selected stored-right premise rather
than silently assuming the submitted left/right orientation. -/
def canonicalStoredRightInitial : Option ReservationState :=
  initializeReservation? canonical 3

theorem canonicalStoredRightInitial_invariant
    {before : ReservationState}
    (equation : canonicalStoredRightInitial = some before) :
    ReservationInvariant canonical before := by
  rcases initializeReservation?_some_iff.mp (by
      simpa [canonicalStoredRightInitial] using equation) with
    ⟨initialStep⟩
  exact initialStep.reservationInvariant

example :
    (match equation : canonicalStoredRightInitial with
    | none => false
    | some before =>
        match SequentialFigure7.nop? canonical before
            (canonicalStoredRightInitial_invariant equation) with
        | none => false
        | some after =>
            after.stack.marks[3]? == some (some 0) &&
              after.stack.marks[2]? == some none &&
              after.stack.ready == [[2]]) = true := by
  native_decide

/-- Stored-right orientation is covered by the same independent
executable/declarative equivalence rather than a left-premise convention. -/
example {before after : ReservationState}
    (initialEquation :
      canonicalStoredRightInitial = some before) :
    SequentialFigure7.nop? canonical before
          (canonicalStoredRightInitial_invariant initialEquation) =
        some after ↔
      SequentialFigure7.NopRule canonical before after :=
  SequentialFigure7.nop?_some_iff_rule_of_structural
    (canonical.wellFormed_iff_structurallyWellFormed.mp
      (by native_decide))
    (canonicalStoredRightInitial_invariant initialEquation)

example {before first second : ReservationState}
    (left : SequentialFigure7.NopRule canonical before first)
    (right : SequentialFigure7.NopRule canonical before second) :
    first = second :=
  left.output_unique right

/-- A minimal relation-level negative fixture: the selected stored-left par
premise is raw, but its mate is already marked.  Thus no `NopRule` output is
possible, independently of the executable checker. -/
def nopMateMarkedCertificate : Certificate where
  formulas := #[p, pDual, .par p pDual]
  links := [.par 0 1 2]
  conclusions := [2]

def nopMateMarkedBefore : ReservationState where
  stack := {
    marks := #[none, some 0, none]
    nextAge := 1
    sigma := [0]
    ready := [[0]]
    waiting := Array.replicate 3 .undefined }
  core := {
    marks := #[none, some 0, none]
    parents := #[]
    components := #[]
    startedAxioms := 0
    firedConnectives := 0 }
  tags := Array.replicate 3 false

example :
    ¬ ∃ after,
      SequentialFigure7.NopRule
        nopMateMarkedCertificate nopMateMarkedBefore after := by
  rintro ⟨after, vertex, rawAge, linkIndex, storedLeft,
    storedRight, conclusion, side, prefixRule, linkEquation,
    premiseEquation, mateUnmarked⟩
  rcases prefixRule with
    ⟨readyPrefix, readyTail, sigmaPrefix, readyEquation,
      sigmaEquation, stackUnmarked, coreUnmarked, _⟩
  have linkBound : linkIndex <
      nopMateMarkedCertificate.links.length :=
    (List.getElem?_eq_some_iff.mp linkEquation).1
  have linkIndexZero : linkIndex = 0 := by
    simpa [nopMateMarkedCertificate] using linkBound
  subst linkIndex
  simp [nopMateMarkedCertificate] at linkEquation
  rcases linkEquation with
    ⟨rfl, rfl, rfl, rfl⟩
  cases side <;>
    simp [TensorPremiseSide.premise] at premiseEquation <;>
    subst vertex <;>
    simp [TensorPremiseSide.mate, nopMateMarkedBefore]
      at coreUnmarked mateUnmarked

/-! Exact executable Figure-7 `wait`. -/

/-- Mark canonical premise `1` at raw age `0`, then reserve the second axiom
so the new active bucket is `[3,2]`.  The selected stored-right premise `3`
therefore has raw age `1`, while its mate `1` retains raw age `0`. -/
def canonicalWaitBefore : Option ReservationState :=
  match initialEquation : canonicalInitialReservation with
  | none => none
  | some initial =>
      match _nopEquation :
          SequentialFigure7.nop? canonical initial
            (canonicalInitialReservation_invariant initialEquation) with
      | none => none
      | some afterNop =>
          reserveNewAxiom? canonical afterNop 3

theorem canonicalWaitBefore_invariant {before : ReservationState}
    (equation : canonicalWaitBefore = some before) :
    ReservationInvariant canonical before := by
  unfold canonicalWaitBefore at equation
  split at equation
  next initialFailure =>
    simp at equation
  next initial initialEquation =>
    split at equation
    next nopFailure =>
      simp at equation
    next afterNop nopEquation =>
      have afterNopInvariant :
          ReservationInvariant canonical afterNop :=
        SequentialFigure7.nop?_reservationInvariant
          (canonicalInitialReservation_invariant initialEquation)
          nopEquation
      rcases reserveNewAxiom?_some_iff.mp equation with
        ⟨newStep⟩
      exact newStep.reservationInvariant afterNopInvariant

example :
    (match canonicalWaitBefore with
    | none => false
    | some before =>
        before.stack.ready == [[0], [3, 2]] &&
        before.stack.sigma == [0, 1] &&
        before.stack.marks[1]? == some (some 0) &&
        before.stack.marks[3]? == some none &&
        before.stack.waiting[0]? == some (.initialized []) &&
        before.stack.waiting[1]? == some .undefined) = true := by
  native_decide

def canonicalWaitTransition : Option ReservationState :=
  match equation : canonicalWaitBefore with
  | none => none
  | some before =>
      SequentialFigure7.wait? canonical before
        (canonicalWaitBefore_invariant equation)

/-- Canonical `wait` uses the mate's raw age `0`, resolves destination boundary
`0`, and prepends conclusion `5` to the initialized empty bucket. -/
example :
    (match canonicalWaitTransition with
    | none => false
    | some after =>
        after.stack.marks[3]? == some (some 1) &&
        after.stack.marks[1]? == some (some 0) &&
        after.stack.ready == [[0], [2]] &&
        after.stack.sigma == [0, 1] &&
        after.stack.waiting[0]? == some (.initialized [5]) &&
        after.stack.waiting[1]? == some .undefined &&
        after.core.marks == after.stack.marks &&
        after.core.parents == #[0, 1] &&
        after.core.startedAxioms == 2 &&
        after.core.firedConnectives == 0) = true := by
  native_decide

example {before after : ReservationState}
    (beforeEquation : canonicalWaitBefore = some before)
    (waitEquation :
      SequentialFigure7.wait? canonical before
          (canonicalWaitBefore_invariant beforeEquation) =
        some after) :
    ReservationInvariant canonical after :=
  SequentialFigure7.wait?_reservationInvariant
    (canonicalWaitBefore_invariant beforeEquation) waitEquation

example {before after : ReservationState}
    (beforeEquation : canonicalWaitBefore = some before)
    (waitEquation :
      SequentialFigure7.wait? canonical before
          (canonicalWaitBefore_invariant beforeEquation) =
        some after) :
    SequentialFigure7.WaitRule canonical before after :=
  SequentialFigure7.wait?_sound
    (canonicalWaitBefore_invariant beforeEquation) waitEquation

example {before after : ReservationState}
    (beforeEquation : canonicalWaitBefore = some before)
    (rule : SequentialFigure7.WaitRule canonical before after) :
    SequentialFigure7.wait? canonical before
        (canonicalWaitBefore_invariant beforeEquation) =
      some after :=
  SequentialFigure7.wait?_complete_of_structural
    (canonical.wellFormed_iff_structurallyWellFormed.mp
      (by native_decide))
    (canonicalWaitBefore_invariant beforeEquation) rule

/-- Boundary lookup is not raw-age indexing: raw mate age `1` belongs to the
interval whose boundary is `0`, so only bucket `0` receives the payload. -/
def separatedBoundaryState : ReservationState where
  stack := {
    marks := Array.replicate 6 none
    nextAge := 3
    sigma := [0, 2]
    ready := [[], []]
    waiting := #[
      .initialized [],
      .undefined,
      .undefined,
      .undefined,
      .undefined,
      .undefined] }
  core := {
    marks := Array.replicate 6 none
    parents := #[0, 1, 2]
    components := #[none, none, none]
    startedAxioms := 3
    firedConnectives := 0 }
  tags := Array.replicate 6 false

example :
    sigmaBoundary? separatedBoundaryState.stack.sigma 1 = some 0 := by
  native_decide

example :
    (match enqueueWaitingAtRawAge? separatedBoundaryState 1 5 with
    | none => false
    | some after =>
        after.stack.waiting[0]? == some (.initialized [5]) &&
        after.stack.waiting[1]? == some .undefined) = true := by
  native_decide

/-- Undefined and out-of-bounds destination cells fail closed, while an
initialized empty cell is a successful writable bucket. -/
example :
    ((SequentialStackState.empty 1).prependWaiting? 0 5).isNone =
        true ∧
      ((SequentialStackState.empty 0).prependWaiting? 0 5).isNone =
        true ∧
      ({ (SequentialStackState.empty 1) with
          waiting := #[.initialized []] } :
        SequentialStackState).prependWaiting? 0 5 =
          some {
            (SequentialStackState.empty 1) with
            waiting := #[.initialized [5]] } := by
  native_decide

/-- An unmarked mate does not satisfy `wait`; this is a reachable,
invariant-carrying canonical stored-right state. -/
example :
    (match equation : canonicalStoredRightInitial with
    | none => false
    | some before =>
        (SequentialFigure7.wait? canonical before
          (canonicalStoredRightInitial_invariant equation)).isNone) =
      true := by
  native_decide

/-- Equality of raw ages fails the strict paper guard.  The invariant argument
is quantified because this test isolates the executable age comparison. -/
def waitEqualAgeBefore : ReservationState where
  stack := {
    marks := #[none, some 1, none, none, none, none]
    nextAge := 2
    sigma := [0, 1]
    ready := [[0], [3, 2]]
    waiting := #[
      .initialized [],
      .undefined,
      .undefined,
      .undefined,
      .undefined,
      .undefined] }
  core := {
    marks := #[none, some 1, none, none, none, none]
    parents := #[0, 1]
    components := #[none, none]
    startedAxioms := 2
    firedConnectives := 0 }
  tags := Array.replicate 6 false

example
    (invariant : ReservationInvariant canonical waitEqualAgeBefore) :
    (SequentialFigure7.wait? canonical waitEqualAgeBefore invariant).isNone =
      true := by
  unfold SequentialFigure7.wait?
  native_decide

example {before after : ReservationState}
    (initialEquation :
      canonicalInitialReservation = some before)
    (laterEquation :
      reserveNewAxiom? canonical before 3 = some after) :
    ReservationInvariant canonical after := by
  rcases initializeReservation?_some_iff.mp (by
      simpa [canonicalInitialReservation] using initialEquation) with
    ⟨initialStep⟩
  rcases reserveNewAxiom?_some_iff.mp laterEquation with
    ⟨laterStep⟩
  exact laterStep.reservationInvariant
    initialStep.reservationInvariant

/-- Starting from the tensor conclusion discovers `[0,1]`; the deterministic
Figure-7 `new` step then marks `0`, follows the opposite tensor premise `2`,
and reserves the exact second axiom in search orientation `[2,3]`. -/
def canonicalFigure7NewInitial : Option ReservationState :=
  initializeReservation? canonical 4

theorem canonicalFigure7NewInitial_invariant {before : ReservationState}
    (equation : canonicalFigure7NewInitial = some before) :
    ReservationInvariant canonical before := by
  rcases initializeReservation?_some_iff.mp (by
      simpa [canonicalFigure7NewInitial] using equation) with
    ⟨initialStep⟩
  exact initialStep.reservationInvariant

/-- Tensor-selected states are not silently accepted by the `nop` rule. -/
example :
    (match canonical.connectiveBelow? 0 with
    | none => false
    | some consumer =>
        consumer.kind == .tensor &&
        consumer.linkIndex == 2 &&
        consumer.premise == 0 &&
        consumer.mate == 2 &&
        consumer.conclusion == 4) = true := by
  native_decide

example :
    (match equation : canonicalFigure7NewInitial with
    | none => false
    | some before =>
        (SequentialFigure7.nop?
          canonical before
          (canonicalFigure7NewInitial_invariant equation)).isNone) = true := by
  native_decide

/-- A nonboundary connective premise cannot run `concl`. -/
example :
    (match equation : canonicalFigure7NewInitial with
    | none => false
    | some before =>
        (SequentialFigure7.concl?
          canonical before
          (canonicalFigure7NewInitial_invariant equation)).isNone) = true := by
  native_decide

def canonicalFigure7NewTransition : Option ReservationState :=
  match equation : canonicalFigure7NewInitial with
  | none => none
  | some before =>
      SequentialFigure7.new? canonical before
        (canonicalFigure7NewInitial_invariant equation)

example :
    (match canonicalFigure7NewTransition with
    | none => false
    | some after =>
        after.stack.marks[0]? == some (some 0) &&
        after.stack.marks[1]? == some none &&
        after.stack.sigma == [0, 1] &&
        after.stack.ready == [[1], [2, 3]] &&
        after.stack.waiting[0]? == some (.initialized []) &&
        after.stack.waiting[1]? == some .undefined &&
        after.core.marks == after.stack.marks &&
        after.core.parents == #[0, 1] &&
        after.core.startedAxioms == 2 &&
        after.core.firedConnectives == 0 &&
        match after.core.components[0]?, after.core.components[1]? with
        | some (some first), some (some second) =>
            first.frontier == [0, 1] &&
            second.frontier == [2, 3]
        | _, _ => false) = true := by
  native_decide

/-- The exact success witness proves invariant preservation through the
mark-before-search transition, not merely through its reservation suffix. -/
example {before after : ReservationState}
    (initialEquation :
      canonicalFigure7NewInitial = some before)
    (newEquation :
      SequentialFigure7.new? canonical before
          (canonicalFigure7NewInitial_invariant initialEquation) =
        some after) :
    ReservationInvariant canonical after := by
  exact SequentialFigure7.new?_reservationInvariant
    (canonicalFigure7NewInitial_invariant initialEquation) newEquation

/-- A concrete successful init/new pair builds a proof-relevant two-event
history.  The history carries exact tag provenance, globally distinct
submitted axiom slots, and counters aligned with both scheduler and production
state.  This is a successful-run property, not a progress theorem. -/
example {before after : ReservationState}
    (initialEquation :
      canonicalFigure7NewInitial = some before)
    (newEquation :
      SequentialFigure7.new? canonical before
          (canonicalFigure7NewInitial_invariant initialEquation) =
        some after) :
    ∃ history : SequentialFigure7.InitNewHistory canonical after,
      history.length = 2 ∧
      history.linkIndices.Nodup ∧
      history.length = after.stack.nextAge ∧
      history.length = after.core.startedAxioms ∧
      (∀ {vertex : Vertex},
        after.tags[vertex]? = some true ↔ history.Touched vertex) := by
  rcases initializeReservation?_some_iff.mp (by
      simpa [canonicalFigure7NewInitial] using initialEquation) with
    ⟨initialStep⟩
  rcases
      (SequentialFigure7.new?_some_iff
        (canonicalFigure7NewInitial_invariant initialEquation)).mp
        newEquation with
    ⟨newStep⟩
  let history : SequentialFigure7.InitNewHistory canonical after :=
    .later (.init initialStep) newStep
  refine ⟨history, rfl, history.linkIndices_nodup,
    history.length_eq_nextAge, history.length_eq_startedAxioms, ?_⟩
  intro vertex
  exact history.tagged_iff_touched

/-- Exact tag origin follows from a successful NEXTAXIOM execution equation,
including the equations retained inside proof-relevant scheduler histories. -/
example {certificate : Certificate} {state : UnificationState}
    {index : SequentialUnification.SourceIndex}
    {fuel : Nat} {inputTags : Array Bool}
    {indexSound :
      SequentialUnification.SourceIndex.Sound certificate index}
    {start : Vertex}
    (result :
      SequentialUnification.NextAxiomResult
        certificate state fuel inputTags)
    (equation :
      SequentialUnification.nextAxiomWithFuel?
          certificate state index indexSound fuel inputTags start =
        some result)
    {vertex : Vertex} :
    result.tags[vertex]? = some true ↔
      inputTags[vertex]? = some true ∨ result.Touched vertex :=
  SequentialUnification.nextAxiomWithFuel?_tagged_iff_input_or_touched
    equation

/-- The composed Figure-7 step exports the operational waiting-domain fact,
not only carrier alignment. -/
example {before after : ReservationState}
    (initialEquation :
      canonicalFigure7NewInitial = some before)
    (newEquation :
      SequentialFigure7.new? canonical before
          (canonicalFigure7NewInitial_invariant initialEquation) =
        some after) :
    after.stack.OperationalWaitingDomain := by
  exact
    (SequentialFigure7.new?_reservationInvariant
      (canonicalFigure7NewInitial_invariant initialEquation)
      newEquation).stack_operationalWaitingDomain

/-- A stored par below the selected ready occurrence is not silently treated
as Figure-7 `new`. -/
example :
    (match equation : canonicalInitialReservation with
    | none => false
    | some before =>
        (SequentialFigure7.new?
          canonical before
          (canonicalInitialReservation_invariant equation)).isNone) = true := by
  native_decide

/-- The generic replay theorem does not depend on the canonical indices. -/
example {middle after : ReservationState}
    {firstStart secondStart : Vertex}
    (first :
      InitialReservationStep canonical middle firstStart)
    (second :
      NewReservationStep canonical middle after secondStart) :
    first.result.linkIndex ≠ second.result.linkIndex :=
  first.linkIndex_ne_next second

/-- A deliberately arbitrary ordered parent forest does not by itself imply
interval realization: raw age `2` lies in the σ interval beginning at `1`,
while the manually chosen parent pointer sends it to representative `0`.
This fixture is not claimed to be reachable through the production union
transition. -/
def arbitraryMergedStack : SequentialStackState where
  marks := Array.replicate 3 none
  nextAge := 3
  sigma := [0, 1]
  ready := [[], []]
  waiting := Array.replicate 3 .undefined

def arbitraryMergedCore : UnificationState where
  marks := Array.replicate 3 none
  parents := #[0, 1, 0]
  components := #[none, none, none]
  startedAxioms := 3
  firedConnectives := 0

theorem arbitraryMergedStack_wellShaped :
    arbitraryMergedStack.WellShaped 3 := by
  unfold arbitraryMergedStack
  exact {
    marks_size := by native_decide
    waiting_size := by native_decide
    assigned_age_bound := by
      intro vertex age assigned
      simp [Array.getElem?_replicate] at assigned
    sigma_partition := {
      empty_iff := by native_decide
      head_zero := by
        intro positive
        native_decide
      strictIncreasing := by decide
      boundary_lt := by
        intro boundary membership
        simp only [List.mem_cons, List.not_mem_nil, or_false]
          at membership
        rcases membership with rfl | rfl <;> decide }
    ready_aligned := by native_decide
    ready_nodup := by
      intro bucket membership
      simp at membership
      subst bucket
      simp
    ready_in_bounds := by
      intro bucket membership vertex vertexMembership
      simp at membership
      subst bucket
      simp at vertexMembership
    nextAge_le_waiting := by native_decide }

theorem arbitraryMergedCore_orderedParents :
    arbitraryMergedCore.OrderedParents := by
  intro token parent lookup
  have tokenBound : token < 3 := by
    have actual :=
      (Array.getElem?_eq_some_iff.mp lookup).1
    simpa [arbitraryMergedCore] using actual
  have cases : token = 0 ∨ token = 1 ∨ token = 2 := by
    omega
  rcases cases with rfl | rfl | rfl <;>
    simp [arbitraryMergedCore] at lookup <;>
    omega

example :
    arbitraryMergedCore.marks = arbitraryMergedStack.marks ∧
    arbitraryMergedCore.parents.size = arbitraryMergedStack.nextAge ∧
    sigmaBoundary? arbitraryMergedStack.sigma 2 = some 1 ∧
    arbitraryMergedCore.representative 2 = 0 := by
  native_decide

example :
    ¬ RealizesSigma arbitraryMergedStack arbitraryMergedCore := by
  intro realizes
  have mismatch :=
    realizes.representative_eq_boundary (age := 2) (by decide)
  have boundary :
      sigmaBoundary? arbitraryMergedStack.sigma 2 = some 1 := by
    native_decide
  have representative :
      arbitraryMergedCore.representative 2 = 0 := by
    native_decide
  rw [boundary, representative] at mismatch
  contradiction

/-! Delayed Figure-7 production-core and two-level stack primitives.

These tests intentionally stop before an executable `forward`/`unify` rule:
the core constructors leave their conclusions raw-unmarked, and the stack
updates are exercised independently. -/

def canonicalQueueCoreBefore : UnificationState where
  marks := #[some 0, some 0, some 1, some 1, none, none]
  parents := #[0, 1]
  components := #[
    some {
      tree := .axiom "p" true
      frontier := [0, 1] },
    some {
      tree := .axiom "q" true
      frontier := [2, 3] }]
  startedAxioms := 2
  firedConnectives := 0

def canonicalQueuedTensor : Option UnificationState :=
  Certificate.queueTensor? canonicalQueueCoreBefore 0 2 4

/-- Local tensor queuing merges the two live components, retires the larger
representative, increments only its own counter, and does not mark `4`. -/
example :
    (match canonicalQueuedTensor with
    | none => false
    | some after =>
        after.marks == canonicalQueueCoreBefore.marks &&
        after.marks[4]? == some none &&
        after.parents == #[0, 0] &&
        after.firedConnectives == 1 &&
        match after.components[0]?, after.components[1]? with
        | some (some component), some none =>
            component.frontier == [4, 1, 3]
        | _, _ => false) = true := by
  native_decide

def canonicalQueuedPar : Option UnificationState := do
  let afterTensor ← canonicalQueuedTensor
  Certificate.queuePar? afterTensor 1 3 5

/-- Once tensor queuing has merged the representatives, local par queuing
builds the par component and exposes `5`, still without assigning its raw
age. -/
example :
    (match canonicalQueuedPar with
    | none => false
    | some after =>
        after.marks == canonicalQueueCoreBefore.marks &&
        after.marks[4]? == some none &&
        after.marks[5]? == some none &&
        after.parents == #[0, 0] &&
        after.firedConnectives == 2 &&
        match after.components[0]?, after.components[1]? with
        | some (some component), some none =>
            component.frontier == [4, 5]
        | _, _ => false) = true := by
  native_decide

/-- Reversing the representative order does not reverse the submitted tensor
premises: the larger token is still retired into the smaller token, while the
derivation tree keeps the stored left/right component order. -/
def reverseQueueCoreBefore : UnificationState where
  marks := #[some 1, some 1, some 0, some 0, none]
  parents := #[0, 1]
  components := #[
    some {
      tree := .axiom "q" true
      frontier := [2, 3] },
    some {
      tree := .axiom "p" true
      frontier := [0, 1] }]
  startedAxioms := 2
  firedConnectives := 0

example :
    (match Certificate.queueTensor? reverseQueueCoreBefore 0 2 4 with
    | none => false
    | some after =>
        after.parents == #[0, 0] &&
        after.marks[4]? == some none &&
        after.firedConnectives == 1 &&
        match after.components[0]?, after.components[1]? with
        | some (some component), some none =>
            component.tree ==
              (.tensor 0 0 (.axiom "p" true) (.axiom "q" true)) &&
            component.frontier == [4, 1, 3]
        | _, _ => false) = true := by
  native_decide

/-- The par sub-primitive fails before the tensor representatives have been
merged, and the tensor sub-primitive fails if its conclusion is already
marked. -/
example :
    (Certificate.queuePar?
      canonicalQueueCoreBefore 1 3 5).isNone = true ∧
    (Certificate.queueTensor?
      { canonicalQueueCoreBefore with
        marks :=
          canonicalQueueCoreBefore.marks.setIfInBounds 4 (some 0) }
      0 2 4).isNone = true := by
  native_decide

example {after : UnificationState}
    (equation :
      Certificate.queueTensor?
          canonicalQueueCoreBefore 0 2 4 =
        some after) :
    after.marks[4]? = some none :=
  Certificate.queueTensor?_conclusion_unmarked equation

example {middle after : UnificationState}
    (_tensorEquation :
      Certificate.queueTensor?
          canonicalQueueCoreBefore 0 2 4 =
        some middle)
    (parEquation :
      Certificate.queuePar? middle 1 3 5 = some after) :
    after.marks[5]? = some none :=
  Certificate.queuePar?_conclusion_unmarked parEquation

def stackPrimitiveBefore : SequentialStackState where
  marks := Array.replicate 6 none
  nextAge := 2
  sigma := [0, 1]
  ready := [[1], [2, 3]]
  waiting := #[
    .initialized [5],
    .undefined,
    .undefined,
    .undefined,
    .undefined,
    .undefined]

def stackPrependedReady : Option SequentialStackState :=
  stackPrimitiveBefore.prependReadyTop? 4

/-- Ready-top prepend changes only the active bucket and fixes project list
order without scanning other ready or waiting payloads. -/
example :
    (match stackPrependedReady with
    | none => false
    | some after =>
        after.ready == [[1], [4, 2, 3]] &&
        after.sigma == stackPrimitiveBefore.sigma &&
        after.waiting == stackPrimitiveBefore.waiting &&
        after.marks == stackPrimitiveBefore.marks) = true := by
  native_decide

def stackMergedReadyWaiting : Option SequentialStackState :=
  stackPrimitiveBefore.mergeTopReadyWaiting? 0 4

/-- The deterministic refinement of the paper's set-valued merge is
`4 :: ([5] ++ [1] ++ [2,3])`; the previous boundary becomes active and its
waiting cell is therefore reset to `undefined`. -/
example :
    (match stackMergedReadyWaiting with
    | none => false
    | some after =>
        after.sigma == [0] &&
        after.ready == [[4, 5, 1, 2, 3]] &&
        after.waiting[0]? == some .undefined &&
        after.nextAge == 2 &&
        after.marks == stackPrimitiveBefore.marks) = true := by
  native_decide

/-- An initialized empty waiting set is a valid merge input and remains
operationally distinct from an undefined cell. -/
def initializedEmptyMergeBefore : SequentialStackState where
  marks := Array.replicate 6 none
  nextAge := 2
  sigma := [0, 1]
  ready := [[1], [2, 3]]
  waiting := #[.initialized [], .undefined, .undefined,
    .undefined, .undefined, .undefined]

example :
    (match initializedEmptyMergeBefore.mergeTopReadyWaiting? 0 4 with
    | none => false
    | some after =>
        after.sigma == [0] &&
        after.ready == [[4, 1, 2, 3]] &&
        after.waiting[0]? == some .undefined) = true := by
  native_decide

/-- Ready-top prepend accepts an existing empty active bucket; only a missing
bucket fails. -/
def emptyActiveReadyBefore : SequentialStackState :=
  { initializedEmptyMergeBefore with
    ready := [[]]
    sigma := [0] }

example :
    emptyActiveReadyBefore.prependReadyTop? 4 =
      some { emptyActiveReadyBefore with ready := [[4]] } := by
  native_decide

/-- Two levels and an initialized exact previous boundary are all required;
out-of-bounds/undefined/wrong-boundary cases fail closed. -/
example :
    (SequentialStackState.empty 6
      |>.prependReadyTop? 4).isNone = true ∧
    ({ stackPrimitiveBefore with
        sigma := [0]
        ready := [[2, 3]] }
      |>.mergeTopReadyWaiting? 0 4).isNone = true ∧
    ({ stackPrimitiveBefore with
        waiting :=
          stackPrimitiveBefore.waiting.setIfInBounds
            0 .undefined }
      |>.mergeTopReadyWaiting? 0 4).isNone = true ∧
    (stackPrimitiveBefore.mergeTopReadyWaiting? 1 4).isNone =
      true := by
  native_decide

example {after : SequentialStackState}
    (equation :
      stackPrimitiveBefore.mergeTopReadyWaiting? 0 4 =
        some after) :
    ∃ sigmaPrefix activeBoundary readyPrefix previousReady
        activeReady payload,
      stackPrimitiveBefore.sigma =
        sigmaPrefix ++ [0, activeBoundary] ∧
      stackPrimitiveBefore.ready =
        readyPrefix ++ [previousReady, activeReady] ∧
      stackPrimitiveBefore.waiting[0]? =
        some (.initialized payload) ∧
      after.ready =
        readyPrefix ++
          [4 :: (payload ++ previousReady ++ activeReady)] :=
  by
    rcases
        SequentialStackState.mergeTopReadyWaiting?_exact
          equation with
      ⟨sigmaPrefix, activeBoundary, readyPrefix,
        previousReady, activeReady, payload,
        sigmaEquation, readyEquation, waitingEquation,
        sigmaAfter, readyAfter, waitingAfter, waitingLookup,
        marksAfter, nextAgeAfter⟩
    exact ⟨sigmaPrefix, activeBoundary, readyPrefix,
      previousReady, activeReady, payload,
      sigmaEquation, readyEquation, waitingEquation,
      readyAfter⟩

end SequentialSchedulerStateTests

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
example : canonical.ReferenceSwitchingConnected :=
  canonical.referenceSwitchingConnected_of_check (by native_decide)
example : canonical.AllOccurrenceSwitchingsConnected ↔
    canonical.ReferenceSwitchingConnected :=
  canonical.allOccurrenceSwitchingsConnected_iff_referenceSwitchingConnected
    (canonical.wellFormed_iff_structurallyWellFormed.mp (by native_decide))
    ((canonical.check_sound_declarative (by native_decide)).cuspAcyclic)
example : canonical.DeclarativelyCorrect ↔
    canonical.StructurallyWellFormed ∧
      canonical.CuspAcyclic ∧
      canonical.ReferenceSwitchingConnected :=
  canonical.declarativelyCorrect_iff_structural_cuspAcyclic_referenceConnected
example : canonical.check = true ↔
    canonical.StructurallyWellFormed ∧
      canonical.CuspAcyclic ∧
      canonical.ReferenceSwitchingConnected :=
  canonical.check_iff_structural_cuspAcyclic_referenceConnected
example : canonical.compactCheck = true := by native_decide
example : canonical.compactCheck = canonical.check :=
  canonical.compactCheck_eq_check
example : canonical.compactCheck = true ↔
    canonical.DeclarativelyCorrect :=
  canonical.compactCheck_eq_true_iff_declarativelyCorrect
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

example : canonical.unificationFastCheck = true := by
  native_decide

example : canonical.unificationReconstruct.isOk = true := by
  native_decide

example : canonical.unificationReconstructWithStats.isOk = true := by
  native_decide

example : canonical.unificationWorklistFastCheck = true := by
  native_decide

example : canonical.unificationWorklistReconstructWithStats.isOk = true := by
  native_decide

example : canonical.unificationWorklistCheck = canonical.check :=
  canonical.unificationWorklistCheck_eq_check

example : canonical.unificationDerivationCandidateWithStats.isOk = true := by
  native_decide

example :
    (match canonical.unificationDerivationCandidateWithStats with
    | .error _ => false
    | .ok result =>
        decide (result.stats.linkVisits ≤
          canonical.links.length * canonical.links.length)) = true := by
  native_decide

example :
    (match (Mutation.dropFirstLink.apply canonical).unificationReconstruct with
    | .error error => error.code == .malformedInput
    | .ok _ => false) = true := by
  native_decide

example :
    ({ canonical with links := canonical.links.reverse } :
      Certificate).unificationFastCheck = true := by
  native_decide

example :
    ({ canonical with conclusions := canonical.conclusions.reverse } :
      Certificate).unificationFastCheck = true := by
  native_decide

example :
    (Mutation.dropFirstLink.apply canonical).unificationFastCheck = false := by
  native_decide

example : canonical.unificationCheck = true := by
  native_decide

example : canonical.unificationCheck = canonical.check :=
  canonical.unificationCheck_eq_check

example : canonical.unificationCheck = true ↔ canonical.check = true :=
  canonical.unificationCheck_eq_true_iff_check

example : canonical.unificationCheck = true ↔
    canonical.DeclarativelyCorrect :=
  canonical.unificationCheck_eq_true_iff_declarativelyCorrect

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
example : droppedLink.compactCheck = false := by native_decide
example : duplicatedLink.compactCheck = false := by native_decide
example : rewiredAxiom.compactCheck = false := by native_decide

def disconnected : Certificate where
  formulas := #[p, pDual, q, qDual]
  links := [.axiom 0 1, .axiom 2 3]
  conclusions := [0, 1, 2, 3]

example : disconnected.wellFormed = true := by native_decide
example : disconnected.check = false := by native_decide
example : disconnected.compactCheck = false := by native_decide
example : disconnected.unificationFastCheck = false := by native_decide
example : disconnected.unificationWorklistFastCheck = false := by native_decide
example :
    (match disconnected.unificationReconstruct with
    | .error error => error.code == .nonUniqueThread
    | .ok _ => false) = true := by
  native_decide
example : disconnected.unificationCheck = false := by native_decide
example : disconnected.unificationWorklistCheck = false := by native_decide

def axiomOnly : Certificate where
  formulas := #[p, pDual]
  links := [.axiom 0 1]
  conclusions := [0, 1]

example : axiomOnly.wellFormed = true := by native_decide
example : axiomOnly.check = true := by native_decide
example : axiomOnly.unificationFastCheck = true := by native_decide
example : axiomOnly.unificationWorklistFastCheck = true := by native_decide

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
#check Graph.EdgeSimplePath.uniqueIntersection_of_traversal_split
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
#check Graph.DirectedEdge.inflateRetained_exists_exact
#check Graph.EdgeWalk.inflateRetained
#check Graph.EdgeWalk.inflateRetainedExact
#check Graph.EdgeWalk.NoImmediateReverse
#check Graph.EdgeWalk.NoImmediateReverse.of_map_nodup
#check Graph.EdgeWalk.NoImmediateReverse.of_constant_forward
#check Graph.EdgeWalk.NoImmediateReverse.append
#check Graph.EdgeWalk.NoImmediateReverse.suffix
#check Graph.EdgeWalk.NoImmediateReverse.reduced_or_cancel
#check Graph.EdgeWalk.NoImmediateReverse.not_cancel
#check Graph.EdgeWalk.NoImmediateReverse.junction_reverse_of_append_cancel
#check Graph.EdgeWalk.NoImmediateReverse.junction_reverse_of_flatten_cancel
#check Graph.EdgeWalk.cancelImmediateReverse
#check Graph.EdgeWalk.ImmediateReverseReduction
#check Graph.EdgeWalk.ImmediateReverseReduction.length_lt
#check Graph.EdgeWalk.ImmediateReverseReduction.preservesWalk
#check Graph.EdgeWalk.ImmediateReverseReduction.membership_subset
#check Graph.EdgeWalk.ImmediateReverseReduction.survives_or_reverse_mem
#check Graph.EdgeWalk.ImmediateReverseNormalization
#check Graph.EdgeWalk.ImmediateReverseNormalization.preservesWalk
#check Graph.EdgeWalk.ImmediateReverseNormalization.membership_subset
#check Graph.EdgeWalk.ImmediateReverseNormalization.length_le
#check Graph.EdgeWalk.ImmediateReverseNormalization.survives_or_reverse_mem
#check Graph.EdgeWalk.ImmediateReverseNormalization.reverse_mem_of_normalizes_to_nil
#check Graph.EdgeWalk.ImmediateReverseNormalization.eq_of_noImmediateReverse
#check Graph.EdgeWalk.normalizeImmediateReversals
#check Graph.EdgeWalk.rotateFirstClosed
#check Graph.EdgeWalk.CyclicNoImmediateReverse
#check Graph.EdgeWalk.CyclicImmediateReverseSite
#check Graph.EdgeWalk.CyclicSegmentJunctionReverse
#check Graph.EdgeWalk.cyclicNoImmediateReverse_or_site
#check Graph.EdgeWalk.CyclicImmediateReverseSite.segmentJunction_of_flatten
#check Graph.EdgeWalk.CyclicImmediateReverseNormalization
#check Graph.EdgeWalk.CyclicImmediateReverseNormalization.membership_subset
#check Graph.EdgeWalk.CyclicImmediateReverseNormalization.survives_or_reverse_mem
#check Graph.EdgeWalk.CyclicImmediateReverseNormalization.reverse_mem_of_normalizes_to_nil
#check Graph.EdgeWalk.CyclicImmediateReverseNormalization.eq_of_cyclicNoImmediateReverse
#check Graph.EdgeWalk.CyclicImmediateReverseNormalization.site_of_nonempty_normalizes_to_nil
#check Graph.EdgeWalk.CyclicReverseShellNormalization
#check Graph.EdgeWalk.CyclicReverseShellNormalization.context
#check Graph.EdgeWalk.CyclicReverseShellNormalization.length_eq
#check Graph.EdgeWalk.CyclicImmediateReverseNormalization.reverseShells_of_noImmediateReverse
#check Graph.EdgeWalk.normalizeCyclicImmediateReversalsTraced
#check Graph.EdgeWalk.normalizeCyclicImmediateReversals
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
#check Graph.Acyclic.edges_nodup
#check Graph.connected_of_bounded_acyclic_edgeCount
#check Certificate.StructurallyWellFormed.fullGraph_bounded
#check UnificationMarking.marked_to_unmarked_referenceEdge_exact_connective_origin
#check UnificationMarking.marked_to_unmarked_referenceEdge_connective_origin
#check Certificate.FullSwitchingSelection.retained_length_eq
#check Certificate.AllOccurrenceSwitchingsConnected
#check Certificate.ReferenceSwitchingConnected
#check Certificate.referenceFullSwitchingSelection
#check Certificate.declarativelyCorrect_iff_structural_cuspAcyclic_allConnected
#check Certificate.check_iff_structural_cuspAcyclic_allConnected
#check Certificate.allOccurrenceSwitchingsConnected_of_reference
#check Certificate.allOccurrenceSwitchingsConnected_iff_referenceSwitchingConnected
#check Certificate.declarativelyCorrect_iff_structural_cuspAcyclic_referenceConnected
#check Certificate.check_iff_structural_cuspAcyclic_referenceConnected
#check Certificate.compactCheck
#check Certificate.compactCheck_eq_true_iff_check
#check Certificate.compactCheck_eq_check
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
