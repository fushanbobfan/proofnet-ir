import ProofNetIR.ReconstructionChecker

namespace ProofNetIR

/-- Proof-irrelevant state for the abstract Guerrini Figure-5 rules.

Unlike the executable union-find state, `sameThread` is an arbitrary
equivalence relation on the fixed carrier `Nat`. `tokenCount` allocates the
initial segment below it; natural numbers at or above the count are already
present in the carrier but cannot occur in a stored mark. This fixed-carrier
encoding lets successive states share one relation type. The two bound fields
make every stored mark refer to a submitted formula occurrence and an
allocated token. -/
structure UnificationMarking (certificate : Certificate) where
  tokenCount : Nat
  mark : Vertex → Option Nat
  sameThread : Nat → Nat → Prop
  sameThreadEquivalence : Equivalence sameThread
  markedVertexBound :
    ∀ {vertex token}, mark vertex = some token →
      vertex < certificate.formulas.size
  markedTokenBound :
    ∀ {vertex token}, mark vertex = some token →
      token < tokenCount

namespace UnificationMarking

/-- Two proof-irrelevant markings are equal when their observable token count,
raw marks, and thread relation are equal. Bound and equivalence witnesses are
proof-irrelevant. -/
@[ext]
theorem ext {first second : UnificationMarking certificate}
    (tokenCount : first.tokenCount = second.tokenCount)
    (mark : first.mark = second.mark)
    (sameThread : first.sameThread = second.sameThread) :
    first = second := by
  cases first
  cases second
  simp_all

/-- Mark one formula occurrence, leaving every other occurrence unchanged. -/
def setMark (mark : Vertex → Option Nat) (vertex token : Nat) :
    Vertex → Option Nat :=
  fun candidate => if candidate = vertex then some token else mark candidate

/-- In the fixed `Nat` carrier, allocating a fresh token preserves the global
thread relation. Freshness is a separate side condition: before allocation,
the newly exposed number must be unrelated to every allocated token. -/
def FreshExtension (state : UnificationMarking certificate)
    (_fresh : Nat) (left right : Nat) : Prop :=
  state.sameThread left right

/-- The carrier element about to be allocated is isolated from every token
that is already allocated. -/
def IsFreshToken (state : UnificationMarking certificate)
    (fresh : Nat) : Prop :=
  ∀ {old}, old < state.tokenCount →
    ¬state.sameThread old fresh

/-- Fresh-token allocation preserves an equivalence relation on the fixed
carrier. This theorem is a regression guard against accidentally defining the
extension only on the allocated initial segment. -/
theorem freshExtension_equivalence
    (state : UnificationMarking certificate) (fresh : Nat) :
    Equivalence (state.FreshExtension fresh) :=
  state.sameThreadEquivalence

/-- Merge the two old equivalence classes containing `leftToken` and
`rightToken`. This formula is the exact one-step equivalence closure because
`state.sameThread` is already an equivalence relation. -/
def MergeExtension (state : UnificationMarking certificate)
    (leftToken rightToken left right : Nat) : Prop :=
  state.sameThread left right ∨
    ((state.sameThread left leftToken ∨
        state.sameThread left rightToken) ∧
      (state.sameThread right leftToken ∨
        state.sameThread right rightToken))

/-- Merging two equivalence classes again yields an equivalence relation. -/
theorem mergeExtension_equivalence
    (state : UnificationMarking certificate)
    (leftToken rightToken : Nat) :
    Equivalence (state.MergeExtension leftToken rightToken) := by
  rcases state.sameThreadEquivalence with
    ⟨reflexive, symmetric, transitive⟩
  have transportLeft {first second : Nat}
      (related : state.sameThread first second) :
      (state.sameThread second leftToken ∨
          state.sameThread second rightToken) →
        (state.sameThread first leftToken ∨
          state.sameThread first rightToken) := by
    intro membership
    rcases membership with membership | membership
    · exact Or.inl (transitive related membership)
    · exact Or.inr (transitive related membership)
  have transportRight {first second : Nat}
      (related : state.sameThread first second) :
      (state.sameThread first leftToken ∨
          state.sameThread first rightToken) →
        (state.sameThread second leftToken ∨
          state.sameThread second rightToken) := by
    exact transportLeft (symmetric related)
  refine ⟨?_, ?_, ?_⟩
  · intro token
    exact Or.inl (reflexive token)
  · intro first second related
    rcases related with old | ⟨firstMerged, secondMerged⟩
    · exact Or.inl (symmetric old)
    · exact Or.inr ⟨secondMerged, firstMerged⟩
  · intro first second third firstSecond secondThird
    rcases firstSecond with
      oldFirstSecond | ⟨firstMerged, secondMerged⟩
    · rcases secondThird with
        oldSecondThird | ⟨secondMerged', thirdMerged⟩
      · exact Or.inl (transitive oldFirstSecond oldSecondThird)
      · exact Or.inr
          ⟨transportLeft oldFirstSecond secondMerged', thirdMerged⟩
    · rcases secondThird with
        oldSecondThird | ⟨secondMerged', thirdMerged⟩
      · exact Or.inr
          ⟨firstMerged, transportRight oldSecondThird secondMerged⟩
      · exact Or.inr ⟨firstMerged, thirdMerged⟩

/-- The merged relation depends only on the two selected equivalence classes,
not on which members name those classes. -/
theorem mergeExtension_congr
    (state : UnificationMarking certificate)
    {leftToken leftToken' rightToken rightToken' : Nat}
    (leftRelated :
      state.sameThread leftToken leftToken')
    (rightRelated :
      state.sameThread rightToken rightToken') :
    state.MergeExtension leftToken rightToken =
      state.MergeExtension leftToken' rightToken' := by
  rcases state.sameThreadEquivalence with
    ⟨reflexive, symmetric, transitive⟩
  funext first second
  apply propext
  have leftIff (token : Nat) :
      state.sameThread token leftToken ↔
        state.sameThread token leftToken' :=
    ⟨fun related => transitive related leftRelated,
      fun related => transitive related (symmetric leftRelated)⟩
  have rightIff (token : Nat) :
      state.sameThread token rightToken ↔
        state.sameThread token rightToken' :=
    ⟨fun related => transitive related rightRelated,
      fun related => transitive related (symmetric rightRelated)⟩
  simp only [MergeExtension, leftIff, rightIff]

/-- The two equivalence classes selected for a merge are unordered. -/
theorem mergeExtension_comm
    (state : UnificationMarking certificate)
    (leftToken rightToken : Nat) :
    state.MergeExtension leftToken rightToken =
      state.MergeExtension rightToken leftToken := by
  funext first second
  apply propext
  simp only [MergeExtension]
  constructor
  · intro merged
    rcases merged with old | ⟨firstMerged, secondMerged⟩
    · exact Or.inl old
    · exact Or.inr
        ⟨firstMerged.elim Or.inr Or.inl,
          secondMerged.elim Or.inr Or.inl⟩
  · intro merged
    rcases merged with old | ⟨firstMerged, secondMerged⟩
    · exact Or.inl old
    · exact Or.inr
        ⟨firstMerged.elim Or.inr Or.inl,
          secondMerged.elim Or.inr Or.inl⟩

/-- The deterministic all-left switching edges whose two endpoint
occurrences have already been marked.  Filtering both endpoints makes every
unmarked occurrence isolated in this proof-only graph. -/
def activeReferenceEdges
    (state : UnificationMarking certificate) : List Edge :=
  (Certificate.linkLeftRetainedEdges certificate.links).filter fun edge =>
    (state.mark edge.first).isSome &&
      (state.mark edge.second).isSome

/-- Proof-only subgraph recording the part of the all-left switching already
spanned by a unification marking. -/
def activeReferenceGraph
    (state : UnificationMarking certificate) : Graph where
  vertexCount := certificate.formulas.size
  edges := state.activeReferenceEdges

/-- Mark-domain extension ignores token names and records only that no
previously marked occurrence becomes unmarked. -/
def MarkDomainExtends
    (first second : UnificationMarking certificate) : Prop :=
  ∀ vertex,
    (first.mark vertex).isSome = true →
      (second.mark vertex).isSome = true

/-- Every pair of marked occurrences in one semantic token class is connected
inside the already active all-left switching subgraph. -/
def ThreadConnected
    (state : UnificationMarking certificate) : Prop :=
  ∀ {first second firstToken secondToken : Nat},
    state.mark first = some firstToken →
      state.mark second = some secondToken →
        state.sameThread firstToken secondToken →
          state.activeReferenceGraph.Walk first second

/-- The retained reference edges contributed by one link do not cross
semantic token classes.  For a par, the deterministic reference switching
retains its left edge; axioms and tensors retain all of their fixed edges. -/
def ReferenceLinkThreaded
    (state : UnificationMarking certificate) : Link → Prop
  | .axiom left right =>
      ∀ {leftToken rightToken},
        state.mark left = some leftToken →
          state.mark right = some rightToken →
            state.sameThread leftToken rightToken
  | .par left _right conclusion =>
      ∀ {leftToken conclusionToken},
        state.mark left = some leftToken →
          state.mark conclusion = some conclusionToken →
            state.sameThread leftToken conclusionToken
  | .tensor left right conclusion =>
      (∀ {leftToken conclusionToken},
          state.mark left = some leftToken →
            state.mark conclusion = some conclusionToken →
              state.sameThread leftToken conclusionToken) ∧
        ∀ {rightToken conclusionToken},
          state.mark right = some rightToken →
            state.mark conclusion = some conclusionToken →
              state.sameThread rightToken conclusionToken

/-- Every submitted link respects the semantic token partition along the
edges retained by the deterministic all-left reference switching. -/
def ReferenceLinksThreaded
    (state : UnificationMarking certificate) : Prop :=
  ∀ link, link ∈ certificate.links →
    state.ReferenceLinkThreaded link

/-- A marked connective conclusion can only arise after both of that
connective's premises have been marked.  This causal closure prevents a later
step from activating an already-fired consumer edge behind the operational
frontier. -/
def MarkingCausallyClosed
    (state : UnificationMarking certificate) : Prop :=
  ∀ link, link ∈ certificate.links →
    match link with
    | .axiom _ _ => True
    | .par left right conclusion
    | .tensor left right conclusion =>
        (state.mark conclusion).isSome = true →
          (state.mark left).isSome = true ∧
            (state.mark right).isSome = true

/-- The operational coherence bundle needed to preserve exact active
thread/component correspondence through independent unification steps. -/
def CausallyThreaded
    (state : UnificationMarking certificate) : Prop :=
  state.MarkingCausallyClosed ∧ state.ReferenceLinksThreaded

/-- Exact correspondence between semantic token classes and connected
components of the active all-left reference graph.  The two directions are
kept separately reusable because operational proofs establish them by
different invariants. -/
def ThreadComponentsExact
    (state : UnificationMarking certificate) : Prop :=
  state.ThreadConnected ∧ state.ReferenceLinksThreaded

/-- Active switching edges are literal retained edges of the complete
all-left reference switching. -/
theorem activeReferenceEdges_subset
    (state : UnificationMarking certificate) :
    ∀ edge ∈ state.activeReferenceEdges,
      edge ∈ Certificate.linkLeftRetainedEdges certificate.links := by
  intro edge membership
  exact (List.mem_filter.mp membership).1

/-- The deterministic occurrence-level reference graph contains exactly the
left-retained edge values, in occurrence order. -/
theorem referenceSwitchingGraph_edges_eq_leftRetained
    (certificate : Certificate) :
      certificate.referenceSwitchingGraph.edges =
        Certificate.linkLeftRetainedEdges certificate.links := by
  change Graph.retainEdgesByMask certificate.fullEdges
      certificate.referenceSwitchingMask =
    Certificate.linkLeftRetainedEdges certificate.links
  simpa [Certificate.retainByMask] using
    certificate.referenceFullSwitchingSelection
      |>.retained_eq_retainByMask.symm

/-- Every active semantic edge is an edge value of the deterministic all-left
occurrence switching. -/
theorem activeReferenceEdges_subset_referenceSwitchingGraph
    (state : UnificationMarking certificate) :
    ∀ edge ∈ state.activeReferenceEdges,
      edge ∈ certificate.referenceSwitchingGraph.edges := by
  intro edge membership
  rw [referenceSwitchingGraph_edges_eq_leftRetained]
  exact state.activeReferenceEdges_subset edge membership

/-- Link-local threading controls every retained edge value, before the
endpoint-mark filter defining the active graph is applied. -/
private theorem retainedEdge_threaded
    {links : List Link}
    (state : UnificationMarking certificate)
    (threaded :
      ∀ link, link ∈ links → state.ReferenceLinkThreaded link)
    {edge : Edge} {firstToken secondToken : Nat}
    (retained :
      edge ∈ Certificate.linkLeftRetainedEdges links)
    (firstMarked : state.mark edge.first = some firstToken)
    (secondMarked : state.mark edge.second = some secondToken) :
    state.sameThread firstToken secondToken := by
  induction links with
  | nil =>
      simp [Certificate.linkLeftRetainedEdges] at retained
  | cons head tail induction =>
      have tailThreaded :
          ∀ link, link ∈ tail →
            state.ReferenceLinkThreaded link := by
        intro link membership
        exact threaded link (by simp [membership])
      cases head with
      | «axiom» left right =>
          simp only [Certificate.linkLeftRetainedEdges,
            List.mem_cons] at retained
          rcases retained with edgeEquation | tailMembership
          · subst edge
            exact
              threaded (.axiom left right) (by simp)
                firstMarked secondMarked
          · exact induction tailThreaded tailMembership
      | «par» left right conclusion =>
          simp only [Certificate.linkLeftRetainedEdges,
            List.mem_cons] at retained
          rcases retained with edgeEquation | tailMembership
          · subst edge
            exact
              threaded (.par left right conclusion) (by simp)
                firstMarked secondMarked
          · exact induction tailThreaded tailMembership
      | tensor left right conclusion =>
          simp only [Certificate.linkLeftRetainedEdges,
            List.mem_cons] at retained
          rcases retained with leftEquation | retained
          · subst edge
            exact
              (threaded (.tensor left right conclusion)
                (by simp)).1 firstMarked secondMarked
          · rcases retained with rightEquation | tailMembership
            · subst edge
              exact
                (threaded (.tensor left right conclusion)
                  (by simp)).2 firstMarked secondMarked
            · exact induction tailThreaded tailMembership

/-- Every active reference edge has marked endpoints in one semantic token
class. -/
theorem ReferenceLinksThreaded.activeEdge_threaded
    (state : UnificationMarking certificate)
    (threaded : state.ReferenceLinksThreaded)
    {edge : Edge} {firstToken secondToken : Nat}
    (active : edge ∈ state.activeReferenceEdges)
    (firstMarked : state.mark edge.first = some firstToken)
    (secondMarked : state.mark edge.second = some secondToken) :
    state.sameThread firstToken secondToken := by
  exact retainedEdge_threaded state threaded
    (List.mem_filter.mp active).1 firstMarked secondMarked

/-- A true `isSome` observation exposes the marked token. -/
private theorem token_exists_of_isSome
    {value : Option Nat} (present : value.isSome = true) :
    ∃ token, value = some token := by
  cases value with
  | none =>
      simp at present
  | some token =>
      exact ⟨token, rfl⟩

/-- If every active retained edge stays inside one semantic class, then every
active graph walk also stays inside one semantic class. -/
theorem ReferenceLinksThreaded.walk_sameThread
    (state : UnificationMarking certificate)
    (threaded : state.ReferenceLinksThreaded)
    {first second firstToken secondToken : Nat}
    (walk : state.activeReferenceGraph.Walk first second)
    (firstMarked : state.mark first = some firstToken)
    (secondMarked : state.mark second = some secondToken) :
    state.sameThread firstToken secondToken := by
  rcases state.sameThreadEquivalence with
    ⟨reflexive, symmetric, transitive⟩
  induction walk generalizing firstToken secondToken with
  | refl =>
      have tokenEquation : firstToken = secondToken := by
        exact Option.some.inj (firstMarked.symm.trans secondMarked)
      subst secondToken
      exact reflexive firstToken
  | @step middle finish prior adjacency induction =>
      rcases adjacency with
        ⟨edge, edgeActive, forward | backward⟩
      · rcases forward with ⟨edgeFirst, edgeSecond⟩
        have endpoints := (List.mem_filter.mp edgeActive).2
        simp only [Bool.and_eq_true] at endpoints
        rcases token_exists_of_isSome endpoints.1 with
          ⟨edgeFirstToken, edgeFirstMarked⟩
        rcases token_exists_of_isSome endpoints.2 with
          ⟨edgeSecondToken, edgeSecondMarked⟩
        have middleMarked :
            state.mark middle = some edgeFirstToken := by
          simpa [edgeFirst] using edgeFirstMarked
        have finishMarked :
            state.mark finish = some edgeSecondToken := by
          simpa [edgeSecond] using edgeSecondMarked
        have prefixThread :
            state.sameThread firstToken edgeFirstToken :=
          induction firstMarked middleMarked
        have finalTokenEquation :
            edgeSecondToken = secondToken := by
          exact Option.some.inj (finishMarked.symm.trans secondMarked)
        subst edgeSecondToken
        exact transitive
          prefixThread
          (threaded.activeEdge_threaded state edgeActive
            edgeFirstMarked edgeSecondMarked)
      · rcases backward with ⟨edgeFirst, edgeSecond⟩
        have endpoints := (List.mem_filter.mp edgeActive).2
        simp only [Bool.and_eq_true] at endpoints
        rcases token_exists_of_isSome endpoints.1 with
          ⟨edgeFirstToken, edgeFirstMarked⟩
        rcases token_exists_of_isSome endpoints.2 with
          ⟨edgeSecondToken, edgeSecondMarked⟩
        have middleMarked :
            state.mark middle = some edgeSecondToken := by
          simpa [edgeSecond] using edgeSecondMarked
        have finishMarked :
            state.mark finish = some edgeFirstToken := by
          simpa [edgeFirst] using edgeFirstMarked
        have prefixThread :
            state.sameThread firstToken edgeSecondToken :=
          induction firstMarked middleMarked
        have finalTokenEquation :
            edgeFirstToken = secondToken := by
          exact Option.some.inj (finishMarked.symm.trans secondMarked)
        subst edgeFirstToken
        exact transitive
          prefixThread
          (symmetric
            (threaded.activeEdge_threaded state edgeActive
              edgeFirstMarked edgeSecondMarked))

/-- Under exact thread/component correspondence, active graph connectivity is
equivalent to union-find thread equality for marked occurrences. -/
theorem ThreadComponentsExact.walk_iff_sameThread
    (state : UnificationMarking certificate)
    (exact : state.ThreadComponentsExact)
    {first second firstToken secondToken : Nat}
    (firstMarked : state.mark first = some firstToken)
    (secondMarked : state.mark second = some secondToken) :
    state.activeReferenceGraph.Walk first second ↔
      state.sameThread firstToken secondToken := by
  constructor
  · intro walk
    exact exact.2.walk_sameThread state walk
      firstMarked secondMarked
  · intro synchronized
    exact exact.1 firstMarked secondMarked synchronized

/-- Extending the marked occurrence domain can only add active reference
edges. -/
theorem activeReferenceEdges_mono
    {first second : UnificationMarking certificate}
    (extension : MarkDomainExtends first second) :
    ∀ edge ∈ first.activeReferenceEdges,
      edge ∈ second.activeReferenceEdges := by
  intro edge membership
  rcases List.mem_filter.mp membership with
    ⟨retained, endpoints⟩
  apply List.mem_filter.mpr
  refine ⟨retained, ?_⟩
  simp only [Bool.and_eq_true] at endpoints ⊢
  exact
    ⟨extension edge.first endpoints.1,
      extension edge.second endpoints.2⟩

/-- Ordinary endpoint walks lift through inclusion of stored edge values. -/
private theorem walk_mono
    {first second : Graph} {start finish : Vertex}
    (walk : first.Walk start finish)
    (edgeSubset : ∀ edge ∈ first.edges, edge ∈ second.edges) :
    second.Walk start finish := by
  induction walk with
  | refl =>
      exact .refl _
  | step prior adjacency induction =>
      rcases adjacency with ⟨edge, membership, direction⟩
      exact .step induction
        ⟨edge, edgeSubset edge membership, direction⟩

/-- Walk concatenation for the independent endpoint path semantics. -/
private theorem walk_trans
    {graph : Graph} {start middle finish : Vertex}
    (first : graph.Walk start middle)
    (second : graph.Walk middle finish) :
    graph.Walk start finish := by
  induction second with
  | refl =>
      exact first
  | step prior adjacency induction =>
      exact .step induction adjacency

/-- Endpoint walks are symmetric in the undirected graph semantics. -/
private theorem walk_reverse
    {graph : Graph} {start finish : Vertex}
    (walk : graph.Walk start finish) :
    graph.Walk finish start := by
  induction walk with
  | refl =>
      exact .refl _
  | @step middle finish prior adjacency induction =>
      have reverseAdjacency : graph.Adjacent finish middle := by
        rcases adjacency with ⟨edge, membership, direction⟩
        exact ⟨edge, membership, direction.elim
          (fun forward => Or.inr forward)
          (fun backward => Or.inl backward)⟩
      exact walk_trans (.step (.refl finish) reverseAdjacency) induction

/-- Existing thread paths survive a pure extension of the marked domain. -/
theorem ThreadConnected.mono
    {first second : UnificationMarking certificate}
    (connected : first.ThreadConnected)
    (extension : MarkDomainExtends first second)
    (marks :
      ∀ {vertex token},
        second.mark vertex = some token →
          first.mark vertex = some token)
    (threads :
      ∀ {left right},
        second.sameThread left right →
          first.sameThread left right) :
    second.ThreadConnected := by
  intro firstVertex secondVertex firstToken secondToken
    firstMarked secondMarked synchronized
  exact walk_mono
    (connected (marks firstMarked) (marks secondMarked)
      (threads synchronized))
    (activeReferenceEdges_mono extension)

end UnificationMarking

/-- A one-element Boolean filter cannot contain two different accepted
values. -/
private theorem mem_filter_length_one_unique
    {α : Type} {values : List α} {predicate : α → Bool}
    {first second : α}
    (count : (values.filter predicate).length = 1)
    (firstMembership : first ∈ values)
    (firstAccepted : predicate first = true)
    (secondMembership : second ∈ values)
    (secondAccepted : predicate second = true) :
    first = second := by
  have firstFiltered : first ∈ values.filter predicate := by
    simp [firstMembership, firstAccepted]
  have secondFiltered : second ∈ values.filter predicate := by
    simp [secondMembership, secondAccepted]
  rcases List.length_eq_one_iff.mp count with
    ⟨only, filterEquation⟩
  rw [filterEquation] at firstFiltered secondFiltered
  simp at firstFiltered secondFiltered
  exact firstFiltered.trans secondFiltered.symm

/-- In a structurally well-formed certificate, two axiom links sharing one
stored endpoint are the same submitted link. -/
private theorem axiom_eq_of_shared_endpoint
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {firstLeft firstRight secondLeft secondRight vertex : Vertex}
    (firstMembership :
      Link.axiom firstLeft firstRight ∈ certificate.links)
    (firstEndpoint : vertex = firstLeft ∨ vertex = firstRight)
    (secondMembership :
      Link.axiom secondLeft secondRight ∈ certificate.links)
    (secondEndpoint : vertex = secondLeft ∨ vertex = secondRight) :
    Link.axiom firstLeft firstRight =
      Link.axiom secondLeft secondRight := by
  have firstWellFormed :=
    structural.2.2.2.2.1 _ firstMembership
  rcases firstWellFormed.axiom_endpointFormula firstEndpoint with
    ⟨name, positive, formulaLookup⟩
  have vertexBound : vertex < certificate.formulas.size := by
    rcases firstEndpoint with rfl | rfl
    · exact firstWellFormed.2.1
    · exact firstWellFormed.2.2.1
  have node := structural.2.2.2.2.2 vertex vertexBound
  have sourceCount : certificate.axiomCount vertex = 1 := by
    simpa [Certificate.NodeWellFormed, formulaLookup] using node.1
  unfold Certificate.axiomCount at sourceCount
  apply mem_filter_length_one_unique sourceCount
  · exact firstMembership
  · rcases firstEndpoint with rfl | rfl <;>
      simp [Link.containsAxiomEndpoint]
  · exact secondMembership
  · rcases secondEndpoint with rfl | rfl <;>
      simp [Link.containsAxiomEndpoint]

/-- In a structurally well-formed certificate, two connective links producing
the same occurrence are the same submitted link. -/
private theorem connective_eq_of_shared_conclusion
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {first second : Link} {conclusion : Vertex}
    (firstMembership : first ∈ certificate.links)
    (firstProduces : first.produces conclusion = true)
    (secondMembership : second ∈ certificate.links)
    (secondProduces : second.produces conclusion = true) :
    first = second := by
  have firstWellFormed :=
    structural.2.2.2.2.1 _ firstMembership
  have formulaShape :
      ∃ formula,
        certificate.formula? conclusion = some formula ∧
          conclusion < certificate.formulas.size ∧
          formula.isAtom = false := by
    cases first with
    | «axiom» left right =>
        simp [Link.produces] at firstProduces
    | tensor left right produced =>
        simp [Link.produces] at firstProduces
        subst produced
        rcases firstWellFormed.tensor_conclusionFormula with
          ⟨leftFormula, rightFormula, formulaLookup⟩
        exact
          ⟨.tensor leftFormula rightFormula, formulaLookup,
            firstWellFormed.2.2.2.2.2.1, rfl⟩
    | «par» left right produced =>
        simp [Link.produces] at firstProduces
        subst produced
        rcases firstWellFormed.par_conclusionFormula with
          ⟨leftFormula, rightFormula, formulaLookup⟩
        exact
          ⟨.par leftFormula rightFormula, formulaLookup,
            firstWellFormed.2.2.2.2.2.1, rfl⟩
  rcases formulaShape with
    ⟨formula, formulaLookup, conclusionBound, compound⟩
  have node :=
    structural.2.2.2.2.2 conclusion conclusionBound
  have producerCount : certificate.producerCount conclusion = 1 := by
    cases formula <;>
      simp [Certificate.NodeWellFormed, formulaLookup] at compound node
    · contradiction
    · exact node.1
    · exact node.1
  unfold Certificate.producerCount at producerCount
  exact mem_filter_length_one_unique producerCount
    firstMembership firstProduces secondMembership secondProduces

/-- An atomic axiom endpoint cannot simultaneously be the compound
conclusion produced by a connective link. -/
private theorem axiomEndpoint_ne_connectiveConclusion
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {axiomLeft axiomRight : Vertex} {connective : Link}
    (axiomMembership :
      Link.axiom axiomLeft axiomRight ∈ certificate.links)
    {endpoint : Vertex}
    (endpointAtAxiom :
      endpoint = axiomLeft ∨ endpoint = axiomRight)
    (connectiveMembership : connective ∈ certificate.links)
    (connectiveProduces : connective.produces endpoint = true) :
    False := by
  have axiomWellFormed :=
    structural.2.2.2.2.1 _ axiomMembership
  rcases axiomWellFormed.axiom_endpointFormula endpointAtAxiom with
    ⟨name, positive, atomLookup⟩
  have connectiveWellFormed :=
    structural.2.2.2.2.1 _ connectiveMembership
  cases connective with
  | «axiom» left right =>
      simp [Link.produces] at connectiveProduces
  | tensor left right conclusion =>
      simp [Link.produces] at connectiveProduces
      subst conclusion
      rcases connectiveWellFormed.tensor_conclusionFormula with
        ⟨leftFormula, rightFormula, compoundLookup⟩
      have impossible :
          Formula.atom name positive =
            Formula.tensor leftFormula rightFormula :=
        Option.some.inj (atomLookup.symm.trans compoundLookup)
      cases impossible
  | «par» left right conclusion =>
      simp [Link.produces] at connectiveProduces
      subst conclusion
      rcases connectiveWellFormed.par_conclusionFormula with
        ⟨leftFormula, rightFormula, compoundLookup⟩
      have impossible :
          Formula.atom name positive =
            Formula.par leftFormula rightFormula :=
        Option.some.inj (atomLookup.symm.trans compoundLookup)
      cases impossible

private theorem axiomEdge_mem_leftRetained
    {links : List Link} {left right : Vertex}
    (membership : Link.axiom left right ∈ links) :
    ({ first := left, second := right } : Edge) ∈
      Certificate.linkLeftRetainedEdges links := by
  induction links with
  | nil =>
      simp at membership
  | cons head tail induction =>
      rcases List.mem_cons.mp membership with same | rest
      · subst head
        simp [Certificate.linkLeftRetainedEdges]
      · cases head with
        | «axiom» headLeft headRight =>
            simp only [Certificate.linkLeftRetainedEdges,
              List.mem_cons]
            exact Or.inr (induction rest)
        | «par» headLeft headRight headConclusion =>
            simp only [Certificate.linkLeftRetainedEdges,
              List.mem_cons]
            exact Or.inr (induction rest)
        | tensor headLeft headRight headConclusion =>
            simp only [Certificate.linkLeftRetainedEdges,
              List.mem_cons]
            exact Or.inr (Or.inr (induction rest))

private theorem parLeftEdge_mem_leftRetained
    {links : List Link} {left right conclusion : Vertex}
    (membership : Link.par left right conclusion ∈ links) :
    ({ first := left, second := conclusion } : Edge) ∈
      Certificate.linkLeftRetainedEdges links := by
  induction links with
  | nil =>
      simp at membership
  | cons head tail induction =>
      rcases List.mem_cons.mp membership with same | rest
      · subst head
        simp [Certificate.linkLeftRetainedEdges]
      · cases head with
        | «axiom» headLeft headRight =>
            simp only [Certificate.linkLeftRetainedEdges,
              List.mem_cons]
            exact Or.inr (induction rest)
        | «par» headLeft headRight headConclusion =>
            simp only [Certificate.linkLeftRetainedEdges,
              List.mem_cons]
            exact Or.inr (induction rest)
        | tensor headLeft headRight headConclusion =>
            simp only [Certificate.linkLeftRetainedEdges,
              List.mem_cons]
            exact Or.inr (Or.inr (induction rest))

theorem tensorEdges_mem_leftRetained
    {links : List Link} {left right conclusion : Vertex}
    (membership : Link.tensor left right conclusion ∈ links) :
    ({ first := left, second := conclusion } : Edge) ∈
        Certificate.linkLeftRetainedEdges links ∧
      ({ first := right, second := conclusion } : Edge) ∈
        Certificate.linkLeftRetainedEdges links := by
  induction links with
  | nil =>
      simp at membership
  | cons head tail induction =>
      rcases List.mem_cons.mp membership with same | rest
      · subst head
        simp [Certificate.linkLeftRetainedEdges]
      · have tailMembership := induction rest
        cases head with
        | «axiom» headLeft headRight =>
            simp only [Certificate.linkLeftRetainedEdges,
              List.mem_cons]
            exact
              ⟨Or.inr tailMembership.1,
                Or.inr tailMembership.2⟩
        | «par» headLeft headRight headConclusion =>
            simp only [Certificate.linkLeftRetainedEdges,
              List.mem_cons]
            exact
              ⟨Or.inr tailMembership.1,
                Or.inr tailMembership.2⟩
        | tensor headLeft headRight headConclusion =>
            simp only [Certificate.linkLeftRetainedEdges,
              List.mem_cons]
            exact
              ⟨Or.inr (Or.inr tailMembership.1),
                Or.inr (Or.inr tailMembership.2)⟩

namespace UnificationMarking

/-- Both fixed edges of every submitted tensor occur in the deterministic
all-left reference switching. -/
theorem referenceSwitchingGraph_tensorEdges
    (certificate : Certificate)
    {left right conclusion : Vertex}
    (membership : Link.tensor left right conclusion ∈ certificate.links) :
    ({ first := left, second := conclusion } : Edge) ∈
        certificate.referenceSwitchingGraph.edges ∧
      ({ first := right, second := conclusion } : Edge) ∈
        certificate.referenceSwitchingGraph.edges := by
  rw [referenceSwitchingGraph_edges_eq_leftRetained]
  exact tensorEdges_mem_leftRetained membership

/-- A started axiom edge is active in the proof-only reference subgraph. -/
theorem activeReferenceGraph_axiomAdjacent
    (state : UnificationMarking certificate)
    {left right leftToken rightToken : Nat}
    (membership : Link.axiom left right ∈ certificate.links)
    (leftMarked : state.mark left = some leftToken)
    (rightMarked : state.mark right = some rightToken) :
    state.activeReferenceGraph.Adjacent left right := by
  let edge : Edge := { first := left, second := right }
  have retained :
      edge ∈ Certificate.linkLeftRetainedEdges certificate.links := by
    exact axiomEdge_mem_leftRetained membership
  have active : edge ∈ state.activeReferenceEdges := by
    apply List.mem_filter.mpr
    exact ⟨retained, by simp [edge, leftMarked, rightMarked]⟩
  exact ⟨edge, active, Or.inl ⟨rfl, rfl⟩⟩

/-- A fired par exposes its deterministic left switching edge. -/
theorem activeReferenceGraph_parLeftAdjacent
    (state : UnificationMarking certificate)
    {left right conclusion leftToken conclusionToken : Nat}
    (membership : Link.par left right conclusion ∈ certificate.links)
    (leftMarked : state.mark left = some leftToken)
    (conclusionMarked :
      state.mark conclusion = some conclusionToken) :
    state.activeReferenceGraph.Adjacent left conclusion := by
  let edge : Edge := { first := left, second := conclusion }
  have retained :
      edge ∈ Certificate.linkLeftRetainedEdges certificate.links := by
    exact parLeftEdge_mem_leftRetained membership
  have active : edge ∈ state.activeReferenceEdges := by
    apply List.mem_filter.mpr
    exact ⟨retained, by
      simp [edge, leftMarked, conclusionMarked]⟩
  exact ⟨edge, active, Or.inl ⟨rfl, rfl⟩⟩

/-- A fired tensor exposes both fixed switching edges. -/
theorem activeReferenceGraph_tensorAdjacent
    (state : UnificationMarking certificate)
    {left right conclusion leftToken rightToken conclusionToken : Nat}
    (membership : Link.tensor left right conclusion ∈ certificate.links)
    (leftMarked : state.mark left = some leftToken)
    (rightMarked : state.mark right = some rightToken)
    (conclusionMarked :
      state.mark conclusion = some conclusionToken) :
    state.activeReferenceGraph.Adjacent left conclusion ∧
      state.activeReferenceGraph.Adjacent right conclusion := by
  let leftEdge : Edge := { first := left, second := conclusion }
  let rightEdge : Edge := { first := right, second := conclusion }
  have retained := tensorEdges_mem_leftRetained membership
  have leftActive : leftEdge ∈ state.activeReferenceEdges := by
    apply List.mem_filter.mpr
    exact ⟨retained.1, by
      simp [leftEdge, leftMarked, conclusionMarked]⟩
  have rightActive : rightEdge ∈ state.activeReferenceEdges := by
    apply List.mem_filter.mpr
    exact ⟨retained.2, by
      simp [rightEdge, rightMarked, conclusionMarked]⟩
  exact
    ⟨⟨leftEdge, leftActive, Or.inl ⟨rfl, rfl⟩⟩,
      ⟨rightEdge, rightActive, Or.inl ⟨rfl, rfl⟩⟩⟩

end UnificationMarking

/-- The three source-level unification rules. -/
inductive UnificationRuleKind where
  | start
  | forward
  | unify
  deriving Repr, DecidableEq, BEq

/-- Independent one-step semantics for Guerrini's Figure-5 unification.

The constructors state their enabling conditions and exact state update
without mentioning the eager scan, queue, waiting set, or executable
union-find representation. -/
inductive UnificationStep (certificate : Certificate) :
    UnificationMarking certificate →
    UnificationMarking certificate → Prop
  | start
      {state next : UnificationMarking certificate}
      {left right : Vertex}
      (linkMembership : Link.axiom left right ∈ certificate.links)
      (leftUnmarked : state.mark left = none)
      (rightUnmarked : state.mark right = none)
      (freshIsolated :
        state.IsFreshToken state.tokenCount)
      (tokenCount :
        next.tokenCount = state.tokenCount + 1)
      (marking :
        next.mark =
          UnificationMarking.setMark
            (UnificationMarking.setMark state.mark left state.tokenCount)
            right state.tokenCount)
      (threads :
        ∀ first second,
          next.sameThread first second ↔
            state.FreshExtension state.tokenCount first second) :
      UnificationStep certificate state next
  | forward
      {state next : UnificationMarking certificate}
      {left right conclusion : Vertex}
      {leftToken rightToken outputToken : Nat}
      (linkMembership :
        Link.par left right conclusion ∈ certificate.links)
      (conclusionUnmarked : state.mark conclusion = none)
      (leftMarked : state.mark left = some leftToken)
      (rightMarked : state.mark right = some rightToken)
      (premisesSynchronized :
        state.sameThread leftToken rightToken)
      (outputTokenAllocated : outputToken < state.tokenCount)
      (outputTokenSynchronized :
        state.sameThread outputToken leftToken)
      (tokenCount :
        next.tokenCount = state.tokenCount)
      (marking :
        next.mark =
          UnificationMarking.setMark state.mark conclusion outputToken)
      (threads :
        next.sameThread = state.sameThread) :
      UnificationStep certificate state next
  | unify
      {state next : UnificationMarking certificate}
      {left right conclusion : Vertex}
      {leftToken rightToken outputToken : Nat}
      (linkMembership :
        Link.tensor left right conclusion ∈ certificate.links)
      (conclusionUnmarked : state.mark conclusion = none)
      (leftMarked : state.mark left = some leftToken)
      (rightMarked : state.mark right = some rightToken)
      (premisesDistinct :
        ¬state.sameThread leftToken rightToken)
      (outputTokenAllocated : outputToken < state.tokenCount)
      (outputTokenFromPremiseThread :
        state.sameThread outputToken leftToken ∨
          state.sameThread outputToken rightToken)
      (tokenCount :
        next.tokenCount = state.tokenCount)
      (marking :
        next.mark =
          UnificationMarking.setMark state.mark conclusion outputToken)
      (threads :
        ∀ first second,
          next.sameThread first second ↔
            state.MergeExtension leftToken rightToken first second) :
      UnificationStep certificate state next

/-- Reflexive-transitive execution generated by the three independent
Figure-5 transitions. This relation contains no scheduler or executable
union-find implementation choices. -/
inductive UnificationExecution (certificate : Certificate) :
    UnificationMarking certificate →
    UnificationMarking certificate → Prop
  | refl (state : UnificationMarking certificate) :
      UnificationExecution certificate state state
  | step
      {state next final : UnificationMarking certificate}
      (transition : UnificationStep certificate state next)
      (rest : UnificationExecution certificate next final) :
      UnificationExecution certificate state final

namespace UnificationExecution

/-- A single independent transition is an execution. -/
theorem single
    {certificate : Certificate}
    {state next : UnificationMarking certificate}
    (transition : UnificationStep certificate state next) :
    UnificationExecution certificate state next :=
  .step transition (.refl next)

/-- Independent executions compose transitively. -/
theorem trans
    {certificate : Certificate}
    {first second third : UnificationMarking certificate}
    (initialExecution :
      UnificationExecution certificate first second)
    (suffix : UnificationExecution certificate second third) :
    UnificationExecution certificate first third := by
  induction initialExecution with
  | refl =>
      exact suffix
  | step transition rest induction =>
      exact .step transition (induction suffix)

end UnificationExecution

namespace UnificationStep

/-- Every abstract unification rule monotonically extends the occurrence
marking domain. -/
theorem markDomainExtends {certificate : Certificate}
    {state next : UnificationMarking certificate}
    (step : UnificationStep certificate state next) :
    state.MarkDomainExtends next := by
  intro vertex oldMarked
  cases step
  case start left right linkMembership leftUnmarked rightUnmarked
      freshIsolated tokenCount marking threads =>
      rw [marking]
      by_cases rightCase : vertex = right <;>
        by_cases leftCase : vertex = left <;>
          simp [UnificationMarking.setMark, rightCase, leftCase, oldMarked]
  case forward left right conclusion leftToken rightToken outputToken
      linkMembership conclusionUnmarked leftMarked rightMarked
      premisesSynchronized outputTokenAllocated outputTokenSynchronized
      tokenCount marking threads =>
      rw [marking]
      by_cases conclusionCase : vertex = conclusion <;>
        simp [UnificationMarking.setMark, conclusionCase, oldMarked]
  case unify left right conclusion leftToken rightToken outputToken
      linkMembership conclusionUnmarked leftMarked rightMarked
      premisesDistinct outputTokenAllocated outputTokenFromPremiseThread
      tokenCount marking threads =>
      rw [marking]
      by_cases conclusionCase : vertex = conclusion <;>
        simp [UnificationMarking.setMark, conclusionCase, oldMarked]

/-- A unification step never changes the raw token stored at an occurrence
which was already marked.  New marks are written only into explicitly
unmarked axiom endpoints or connective conclusions. -/
theorem preservesMarkedToken {certificate : Certificate}
    {state next : UnificationMarking certificate}
    (step : UnificationStep certificate state next)
    {vertex token : Nat}
    (marked : state.mark vertex = some token) :
    next.mark vertex = some token := by
  cases step
  case start left right linkMembership leftUnmarked rightUnmarked
      freshIsolated tokenCount marking threads =>
      rw [marking]
      by_cases rightCase : vertex = right
      · subst vertex
        rw [rightUnmarked] at marked
        contradiction
      · by_cases leftCase : vertex = left
        · subst vertex
          rw [leftUnmarked] at marked
          contradiction
        · simp [UnificationMarking.setMark, rightCase, leftCase, marked]
  case forward left right conclusion leftToken rightToken outputToken
      linkMembership conclusionUnmarked leftMarked rightMarked
      premisesSynchronized outputTokenAllocated outputTokenSynchronized
      tokenCount marking threads =>
      rw [marking]
      by_cases conclusionCase : vertex = conclusion
      · subst vertex
        rw [conclusionUnmarked] at marked
        contradiction
      · simp [UnificationMarking.setMark, conclusionCase, marked]
  case unify left right conclusion leftToken rightToken outputToken
      linkMembership conclusionUnmarked leftMarked rightMarked
      premisesDistinct outputTokenAllocated outputTokenFromPremiseThread
      tokenCount marking threads =>
      rw [marking]
      by_cases conclusionCase : vertex = conclusion
      · subst vertex
        rw [conclusionUnmarked] at marked
        contradiction
      · simp [UnificationMarking.setMark, conclusionCase, marked]

/-- The semantic token equivalence relation can only grow: start and forward
leave it unchanged, while tensor/unify adds one equivalence-class merge. -/
theorem sameThread_mono {certificate : Certificate}
    {state next : UnificationMarking certificate}
    (step : UnificationStep certificate state next)
    {first second : Nat}
    (related : state.sameThread first second) :
    next.sameThread first second := by
  cases step
  case start threads =>
      exact (threads first second).mpr related
  case forward threads =>
      rw [threads]
      exact related
  case unify threads =>
      exact (threads first second).mpr (Or.inl related)

/-- Causal marking closure is invariant under every structurally valid
Figure-5 transition.  Source uniqueness identifies a newly marked connective
conclusion with the link actually fired; every other marked conclusion was
already present before the step. -/
theorem markingCausallyClosed
    {certificate : Certificate}
    {state next : UnificationMarking certificate}
    (structural : certificate.StructurallyWellFormed)
    (closed : state.MarkingCausallyClosed)
    (step : UnificationStep certificate state next) :
    next.MarkingCausallyClosed := by
  have liftPresent {vertex : Vertex}
      (present : (state.mark vertex).isSome = true) :
      (next.mark vertex).isSome = true := by
    rcases UnificationMarking.token_exists_of_isSome present with
      ⟨token, marked⟩
    simp [step.preservesMarkedToken marked]
  intro candidate candidateMembership
  cases step
  case start left right linkMembership leftUnmarked rightUnmarked
      freshIsolated tokenCount marking threads =>
      cases candidate with
      | «axiom» candidateLeft candidateRight =>
          trivial
      | «par» candidateLeft candidateRight candidateConclusion =>
          intro conclusionMarked
          have conclusionNotLeft : candidateConclusion ≠ left := by
            intro same
            subst candidateConclusion
            exact axiomEndpoint_ne_connectiveConclusion structural
              linkMembership (Or.inl rfl) candidateMembership
                (by simp [Link.produces])
          have conclusionNotRight : candidateConclusion ≠ right := by
            intro same
            subst candidateConclusion
            exact axiomEndpoint_ne_connectiveConclusion structural
              linkMembership (Or.inr rfl) candidateMembership
                (by simp [Link.produces])
          have oldConclusion :
              (state.mark candidateConclusion).isSome = true := by
            rw [marking] at conclusionMarked
            simpa [UnificationMarking.setMark,
              conclusionNotLeft, conclusionNotRight] using
                conclusionMarked
          have premises :=
            closed (.par candidateLeft candidateRight candidateConclusion)
              candidateMembership oldConclusion
          exact ⟨liftPresent premises.1, liftPresent premises.2⟩
      | tensor candidateLeft candidateRight candidateConclusion =>
          intro conclusionMarked
          have conclusionNotLeft : candidateConclusion ≠ left := by
            intro same
            subst candidateConclusion
            exact axiomEndpoint_ne_connectiveConclusion structural
              linkMembership (Or.inl rfl) candidateMembership
                (by simp [Link.produces])
          have conclusionNotRight : candidateConclusion ≠ right := by
            intro same
            subst candidateConclusion
            exact axiomEndpoint_ne_connectiveConclusion structural
              linkMembership (Or.inr rfl) candidateMembership
                (by simp [Link.produces])
          have oldConclusion :
              (state.mark candidateConclusion).isSome = true := by
            rw [marking] at conclusionMarked
            simpa [UnificationMarking.setMark,
              conclusionNotLeft, conclusionNotRight] using
                conclusionMarked
          have premises :=
            closed
              (.tensor candidateLeft candidateRight candidateConclusion)
              candidateMembership oldConclusion
          exact ⟨liftPresent premises.1, liftPresent premises.2⟩
  case forward left right conclusion leftToken rightToken outputToken
      linkMembership conclusionUnmarked leftMarked rightMarked
      premisesSynchronized outputTokenAllocated outputTokenSynchronized
      tokenCount marking threads =>
      cases candidate with
      | «axiom» candidateLeft candidateRight =>
          trivial
      | «par» candidateLeft candidateRight candidateConclusion =>
          intro conclusionMarked
          by_cases sameConclusion : candidateConclusion = conclusion
          · subst candidateConclusion
            have sameLink :
                Link.par left right conclusion =
                  Link.par candidateLeft candidateRight conclusion :=
              connective_eq_of_shared_conclusion structural
                (conclusion := conclusion)
                linkMembership (by simp [Link.produces])
                candidateMembership (by simp [Link.produces])
            injection sameLink with leftEquation rightEquation
            subst candidateLeft
            subst candidateRight
            exact
              ⟨liftPresent (by simp [leftMarked]),
                liftPresent (by simp [rightMarked])⟩
          · have oldConclusion :
                (state.mark candidateConclusion).isSome = true := by
              rw [marking] at conclusionMarked
              simpa [UnificationMarking.setMark,
                sameConclusion] using conclusionMarked
            have premises :=
              closed
                (.par candidateLeft candidateRight candidateConclusion)
                candidateMembership oldConclusion
            exact ⟨liftPresent premises.1, liftPresent premises.2⟩
      | tensor candidateLeft candidateRight candidateConclusion =>
          intro conclusionMarked
          by_cases sameConclusion : candidateConclusion = conclusion
          · subst candidateConclusion
            have impossible :
                Link.par left right conclusion =
                  Link.tensor candidateLeft candidateRight conclusion :=
              connective_eq_of_shared_conclusion structural
                (conclusion := conclusion)
                linkMembership (by simp [Link.produces])
                candidateMembership (by simp [Link.produces])
            cases impossible
          · have oldConclusion :
                (state.mark candidateConclusion).isSome = true := by
              rw [marking] at conclusionMarked
              simpa [UnificationMarking.setMark,
                sameConclusion] using conclusionMarked
            have premises :=
              closed
                (.tensor candidateLeft candidateRight candidateConclusion)
                candidateMembership oldConclusion
            exact ⟨liftPresent premises.1, liftPresent premises.2⟩
  case unify left right conclusion leftToken rightToken outputToken
      linkMembership conclusionUnmarked leftMarked rightMarked
      premisesDistinct outputTokenAllocated outputTokenFromPremiseThread
      tokenCount marking threads =>
      cases candidate with
      | «axiom» candidateLeft candidateRight =>
          trivial
      | «par» candidateLeft candidateRight candidateConclusion =>
          intro conclusionMarked
          by_cases sameConclusion : candidateConclusion = conclusion
          · subst candidateConclusion
            have impossible :
                Link.tensor left right conclusion =
                  Link.par candidateLeft candidateRight conclusion :=
              connective_eq_of_shared_conclusion structural
                (conclusion := conclusion)
                linkMembership (by simp [Link.produces])
                candidateMembership (by simp [Link.produces])
            cases impossible
          · have oldConclusion :
                (state.mark candidateConclusion).isSome = true := by
              rw [marking] at conclusionMarked
              simpa [UnificationMarking.setMark,
                sameConclusion] using conclusionMarked
            have premises :=
              closed
                (.par candidateLeft candidateRight candidateConclusion)
                candidateMembership oldConclusion
            exact ⟨liftPresent premises.1, liftPresent premises.2⟩
      | tensor candidateLeft candidateRight candidateConclusion =>
          intro conclusionMarked
          by_cases sameConclusion : candidateConclusion = conclusion
          · subst candidateConclusion
            have sameLink :
                Link.tensor left right conclusion =
                  Link.tensor candidateLeft candidateRight conclusion :=
              connective_eq_of_shared_conclusion structural
                (conclusion := conclusion)
                linkMembership (by simp [Link.produces])
                candidateMembership (by simp [Link.produces])
            injection sameLink with leftEquation rightEquation
            subst candidateLeft
            subst candidateRight
            exact
              ⟨liftPresent (by simp [leftMarked]),
                liftPresent (by simp [rightMarked])⟩
          · have oldConclusion :
                (state.mark candidateConclusion).isSome = true := by
              rw [marking] at conclusionMarked
              simpa [UnificationMarking.setMark,
                sameConclusion] using conclusionMarked
            have premises :=
              closed
                (.tensor candidateLeft candidateRight candidateConclusion)
                candidateMembership oldConclusion
            exact ⟨liftPresent premises.1, liftPresent premises.2⟩

/-- Link-local threading is invariant under every structurally valid
Figure-5 transition, provided the prior marking is causally closed.  The
causal premise is what rules out an already-fired consumer whose previously
unmarked premise is activated by the current step. -/
theorem referenceLinksThreaded
    {certificate : Certificate}
    {state next : UnificationMarking certificate}
    (structural : certificate.StructurallyWellFormed)
    (closed : state.MarkingCausallyClosed)
    (threaded : state.ReferenceLinksThreaded)
    (step : UnificationStep certificate state next) :
    next.ReferenceLinksThreaded := by
  have liftRelation {first second : Nat}
      (related : state.sameThread first second) :
      next.sameThread first second :=
    step.sameThread_mono related
  have recoverOldToken {vertex token : Nat}
      (nextMarked : next.mark vertex = some token)
      (oldPresent : (state.mark vertex).isSome = true) :
      state.mark vertex = some token := by
    rcases UnificationMarking.token_exists_of_isSome oldPresent with
      ⟨oldToken, oldMarked⟩
    have preserved := step.preservesMarkedToken oldMarked
    have tokenEquation : oldToken = token :=
      Option.some.inj (preserved.symm.trans nextMarked)
    subst token
    exact oldMarked
  intro candidate candidateMembership
  cases step
  case start left right linkMembership leftUnmarked rightUnmarked
      freshIsolated tokenCount marking threads =>
      cases candidate with
      | «axiom» candidateLeft candidateRight =>
          intro candidateLeftToken candidateRightToken
            candidateLeftMarked candidateRightMarked
          by_cases sameLink :
              Link.axiom candidateLeft candidateRight =
                Link.axiom left right
          · injection sameLink with leftEquation rightEquation
            subst candidateLeft
            subst candidateRight
            have different : left ≠ right :=
              (structural.2.2.2.2.1 _ linkMembership).1
            have nextLeft :
                next.mark left = some state.tokenCount := by
              rw [marking]
              simp [UnificationMarking.setMark, different]
            have nextRight :
                next.mark right = some state.tokenCount := by
              rw [marking]
              simp [UnificationMarking.setMark]
            have leftTokenEquation :
                candidateLeftToken = state.tokenCount :=
              Option.some.inj
                (candidateLeftMarked.symm.trans nextLeft)
            have rightTokenEquation :
                candidateRightToken = state.tokenCount :=
              Option.some.inj
                (candidateRightMarked.symm.trans nextRight)
            subst candidateLeftToken
            subst candidateRightToken
            exact (threads _ _).mpr
              (state.sameThreadEquivalence.1 state.tokenCount)
          · have candidateLeftNotLeft : candidateLeft ≠ left := by
              intro same
              have equal :=
                axiom_eq_of_shared_endpoint structural
                  candidateMembership (Or.inl rfl) linkMembership
                    (Or.inl same)
              exact sameLink equal
            have candidateLeftNotRight : candidateLeft ≠ right := by
              intro same
              have equal :=
                axiom_eq_of_shared_endpoint structural
                  candidateMembership (Or.inl rfl) linkMembership
                    (Or.inr same)
              exact sameLink equal
            have candidateRightNotLeft : candidateRight ≠ left := by
              intro same
              have equal :=
                axiom_eq_of_shared_endpoint structural
                  candidateMembership (Or.inr rfl) linkMembership
                    (Or.inl same)
              exact sameLink equal
            have candidateRightNotRight : candidateRight ≠ right := by
              intro same
              have equal :=
                axiom_eq_of_shared_endpoint structural
                  candidateMembership (Or.inr rfl) linkMembership
                    (Or.inr same)
              exact sameLink equal
            have oldLeft :
                state.mark candidateLeft = some candidateLeftToken := by
              rw [marking] at candidateLeftMarked
              simpa [UnificationMarking.setMark,
                candidateLeftNotLeft, candidateLeftNotRight] using
                  candidateLeftMarked
            have oldRight :
                state.mark candidateRight = some candidateRightToken := by
              rw [marking] at candidateRightMarked
              simpa [UnificationMarking.setMark,
                candidateRightNotLeft, candidateRightNotRight] using
                  candidateRightMarked
            exact liftRelation
              (threaded (.axiom candidateLeft candidateRight)
                candidateMembership oldLeft oldRight)
      | «par» candidateLeft candidateRight candidateConclusion =>
          intro candidateLeftToken candidateConclusionToken
            candidateLeftMarked candidateConclusionMarked
          have conclusionNotLeft : candidateConclusion ≠ left := by
            intro same
            subst candidateConclusion
            exact axiomEndpoint_ne_connectiveConclusion structural
              linkMembership (Or.inl rfl) candidateMembership
                (by simp [Link.produces])
          have conclusionNotRight : candidateConclusion ≠ right := by
            intro same
            subst candidateConclusion
            exact axiomEndpoint_ne_connectiveConclusion structural
              linkMembership (Or.inr rfl) candidateMembership
                (by simp [Link.produces])
          have oldConclusion :
              state.mark candidateConclusion =
                some candidateConclusionToken := by
            rw [marking] at candidateConclusionMarked
            simpa [UnificationMarking.setMark,
              conclusionNotLeft, conclusionNotRight] using
                candidateConclusionMarked
          have premisesPresent :=
            closed
              (.par candidateLeft candidateRight candidateConclusion)
              candidateMembership (by simp [oldConclusion])
          have oldLeft :=
            recoverOldToken candidateLeftMarked premisesPresent.1
          exact liftRelation
            (threaded
              (.par candidateLeft candidateRight candidateConclusion)
              candidateMembership oldLeft oldConclusion)
      | tensor candidateLeft candidateRight candidateConclusion =>
          constructor
          · intro candidateLeftToken candidateConclusionToken
              candidateLeftMarked candidateConclusionMarked
            have conclusionNotLeft : candidateConclusion ≠ left := by
              intro same
              subst candidateConclusion
              exact axiomEndpoint_ne_connectiveConclusion structural
                linkMembership (Or.inl rfl) candidateMembership
                  (by simp [Link.produces])
            have conclusionNotRight : candidateConclusion ≠ right := by
              intro same
              subst candidateConclusion
              exact axiomEndpoint_ne_connectiveConclusion structural
                linkMembership (Or.inr rfl) candidateMembership
                  (by simp [Link.produces])
            have oldConclusion :
                state.mark candidateConclusion =
                  some candidateConclusionToken := by
              rw [marking] at candidateConclusionMarked
              simpa [UnificationMarking.setMark,
                conclusionNotLeft, conclusionNotRight] using
                  candidateConclusionMarked
            have premisesPresent :=
              closed
                (.tensor candidateLeft candidateRight candidateConclusion)
                candidateMembership (by simp [oldConclusion])
            have oldLeft :=
              recoverOldToken candidateLeftMarked premisesPresent.1
            exact liftRelation
              ((threaded
                (.tensor candidateLeft candidateRight candidateConclusion)
                candidateMembership).1 oldLeft oldConclusion)
          · intro candidateRightToken candidateConclusionToken
              candidateRightMarked candidateConclusionMarked
            have conclusionNotLeft : candidateConclusion ≠ left := by
              intro same
              subst candidateConclusion
              exact axiomEndpoint_ne_connectiveConclusion structural
                linkMembership (Or.inl rfl) candidateMembership
                  (by simp [Link.produces])
            have conclusionNotRight : candidateConclusion ≠ right := by
              intro same
              subst candidateConclusion
              exact axiomEndpoint_ne_connectiveConclusion structural
                linkMembership (Or.inr rfl) candidateMembership
                  (by simp [Link.produces])
            have oldConclusion :
                state.mark candidateConclusion =
                  some candidateConclusionToken := by
              rw [marking] at candidateConclusionMarked
              simpa [UnificationMarking.setMark,
                conclusionNotLeft, conclusionNotRight] using
                  candidateConclusionMarked
            have premisesPresent :=
              closed
                (.tensor candidateLeft candidateRight candidateConclusion)
                candidateMembership (by simp [oldConclusion])
            have oldRight :=
              recoverOldToken candidateRightMarked premisesPresent.2
            exact liftRelation
              ((threaded
                (.tensor candidateLeft candidateRight candidateConclusion)
                candidateMembership).2 oldRight oldConclusion)
  case forward left right conclusion leftToken rightToken outputToken
      linkMembership conclusionUnmarked leftMarked rightMarked
      premisesSynchronized outputTokenAllocated outputTokenSynchronized
      tokenCount marking threads =>
      cases candidate with
      | «axiom» candidateLeft candidateRight =>
          intro candidateLeftToken candidateRightToken
            candidateLeftMarked candidateRightMarked
          have leftNotConclusion : candidateLeft ≠ conclusion := by
            intro same
            subst candidateLeft
            exact axiomEndpoint_ne_connectiveConclusion structural
              candidateMembership (Or.inl rfl) linkMembership
                (by simp [Link.produces])
          have rightNotConclusion : candidateRight ≠ conclusion := by
            intro same
            subst candidateRight
            exact axiomEndpoint_ne_connectiveConclusion structural
              candidateMembership (Or.inr rfl) linkMembership
                (by simp [Link.produces])
          have oldLeft :
              state.mark candidateLeft = some candidateLeftToken := by
            rw [marking] at candidateLeftMarked
            simpa [UnificationMarking.setMark,
              leftNotConclusion] using candidateLeftMarked
          have oldRight :
              state.mark candidateRight = some candidateRightToken := by
            rw [marking] at candidateRightMarked
            simpa [UnificationMarking.setMark,
              rightNotConclusion] using candidateRightMarked
          exact liftRelation
            (threaded (.axiom candidateLeft candidateRight)
              candidateMembership oldLeft oldRight)
      | «par» candidateLeft candidateRight candidateConclusion =>
          intro candidateLeftToken candidateConclusionToken
            candidateLeftMarked candidateConclusionMarked
          by_cases sameConclusion : candidateConclusion = conclusion
          · subst candidateConclusion
            have sameLink :
                Link.par left right conclusion =
                  Link.par candidateLeft candidateRight conclusion :=
              connective_eq_of_shared_conclusion structural
                (conclusion := conclusion)
                linkMembership (by simp [Link.produces])
                candidateMembership (by simp [Link.produces])
            injection sameLink with leftEquation rightEquation
            subst candidateLeft
            subst candidateRight
            have oldLeft :=
              recoverOldToken candidateLeftMarked (by simp [leftMarked])
            have leftTokenEquation :
                candidateLeftToken = leftToken :=
              Option.some.inj
                (oldLeft.symm.trans leftMarked)
            have conclusionNext :
                next.mark conclusion = some outputToken := by
              rw [marking]
              simp [UnificationMarking.setMark]
            have conclusionTokenEquation :
                candidateConclusionToken = outputToken :=
              Option.some.inj
                (candidateConclusionMarked.symm.trans conclusionNext)
            subst candidateLeftToken
            subst candidateConclusionToken
            rw [threads]
            exact state.sameThreadEquivalence.symm
              outputTokenSynchronized
          · have oldConclusion :
                state.mark candidateConclusion =
                  some candidateConclusionToken := by
              rw [marking] at candidateConclusionMarked
              simpa [UnificationMarking.setMark,
                sameConclusion] using candidateConclusionMarked
            have premisesPresent :=
              closed
                (.par candidateLeft candidateRight candidateConclusion)
                candidateMembership (by simp [oldConclusion])
            have oldLeft :=
              recoverOldToken candidateLeftMarked premisesPresent.1
            exact liftRelation
              (threaded
                (.par candidateLeft candidateRight candidateConclusion)
                candidateMembership oldLeft oldConclusion)
      | tensor candidateLeft candidateRight candidateConclusion =>
          constructor
          · intro candidateLeftToken candidateConclusionToken
              candidateLeftMarked candidateConclusionMarked
            by_cases sameConclusion : candidateConclusion = conclusion
            · subst candidateConclusion
              have impossible :
                  Link.par left right conclusion =
                    Link.tensor candidateLeft candidateRight conclusion :=
                connective_eq_of_shared_conclusion structural
                  (conclusion := conclusion)
                  linkMembership (by simp [Link.produces])
                  candidateMembership (by simp [Link.produces])
              cases impossible
            · have oldConclusion :
                  state.mark candidateConclusion =
                    some candidateConclusionToken := by
                rw [marking] at candidateConclusionMarked
                simpa [UnificationMarking.setMark,
                  sameConclusion] using candidateConclusionMarked
              have premisesPresent :=
                closed
                  (.tensor candidateLeft candidateRight candidateConclusion)
                  candidateMembership (by simp [oldConclusion])
              have oldLeft :=
                recoverOldToken candidateLeftMarked premisesPresent.1
              exact liftRelation
                ((threaded
                  (.tensor candidateLeft candidateRight candidateConclusion)
                  candidateMembership).1 oldLeft oldConclusion)
          · intro candidateRightToken candidateConclusionToken
              candidateRightMarked candidateConclusionMarked
            by_cases sameConclusion : candidateConclusion = conclusion
            · subst candidateConclusion
              have impossible :
                  Link.par left right conclusion =
                    Link.tensor candidateLeft candidateRight conclusion :=
                connective_eq_of_shared_conclusion structural
                  (conclusion := conclusion)
                  linkMembership (by simp [Link.produces])
                  candidateMembership (by simp [Link.produces])
              cases impossible
            · have oldConclusion :
                  state.mark candidateConclusion =
                    some candidateConclusionToken := by
                rw [marking] at candidateConclusionMarked
                simpa [UnificationMarking.setMark,
                  sameConclusion] using candidateConclusionMarked
              have premisesPresent :=
                closed
                  (.tensor candidateLeft candidateRight candidateConclusion)
                  candidateMembership (by simp [oldConclusion])
              have oldRight :=
                recoverOldToken candidateRightMarked premisesPresent.2
              exact liftRelation
                ((threaded
                  (.tensor candidateLeft candidateRight candidateConclusion)
                  candidateMembership).2 oldRight oldConclusion)
  case unify left right conclusion leftToken rightToken outputToken
      linkMembership conclusionUnmarked leftMarked rightMarked
      premisesDistinct outputTokenAllocated outputTokenFromPremiseThread
      tokenCount marking threads =>
      cases candidate with
      | «axiom» candidateLeft candidateRight =>
          intro candidateLeftToken candidateRightToken
            candidateLeftMarked candidateRightMarked
          have leftNotConclusion : candidateLeft ≠ conclusion := by
            intro same
            subst candidateLeft
            exact axiomEndpoint_ne_connectiveConclusion structural
              candidateMembership (Or.inl rfl) linkMembership
                (by simp [Link.produces])
          have rightNotConclusion : candidateRight ≠ conclusion := by
            intro same
            subst candidateRight
            exact axiomEndpoint_ne_connectiveConclusion structural
              candidateMembership (Or.inr rfl) linkMembership
                (by simp [Link.produces])
          have oldLeft :
              state.mark candidateLeft = some candidateLeftToken := by
            rw [marking] at candidateLeftMarked
            simpa [UnificationMarking.setMark,
              leftNotConclusion] using candidateLeftMarked
          have oldRight :
              state.mark candidateRight = some candidateRightToken := by
            rw [marking] at candidateRightMarked
            simpa [UnificationMarking.setMark,
              rightNotConclusion] using candidateRightMarked
          exact liftRelation
            (threaded (.axiom candidateLeft candidateRight)
              candidateMembership oldLeft oldRight)
      | «par» candidateLeft candidateRight candidateConclusion =>
          intro candidateLeftToken candidateConclusionToken
            candidateLeftMarked candidateConclusionMarked
          by_cases sameConclusion : candidateConclusion = conclusion
          · subst candidateConclusion
            have impossible :
                Link.tensor left right conclusion =
                  Link.par candidateLeft candidateRight conclusion :=
              connective_eq_of_shared_conclusion structural
                (conclusion := conclusion)
                linkMembership (by simp [Link.produces])
                candidateMembership (by simp [Link.produces])
            cases impossible
          · have oldConclusion :
                state.mark candidateConclusion =
                  some candidateConclusionToken := by
              rw [marking] at candidateConclusionMarked
              simpa [UnificationMarking.setMark,
                sameConclusion] using candidateConclusionMarked
            have premisesPresent :=
              closed
                (.par candidateLeft candidateRight candidateConclusion)
                candidateMembership (by simp [oldConclusion])
            have oldLeft :=
              recoverOldToken candidateLeftMarked premisesPresent.1
            exact liftRelation
              (threaded
                (.par candidateLeft candidateRight candidateConclusion)
                candidateMembership oldLeft oldConclusion)
      | tensor candidateLeft candidateRight candidateConclusion =>
          constructor
          · intro candidateLeftToken candidateConclusionToken
              candidateLeftMarked candidateConclusionMarked
            by_cases sameConclusion : candidateConclusion = conclusion
            · subst candidateConclusion
              have sameLink :
                  Link.tensor left right conclusion =
                    Link.tensor candidateLeft candidateRight conclusion :=
                connective_eq_of_shared_conclusion structural
                  (conclusion := conclusion)
                  linkMembership (by simp [Link.produces])
                  candidateMembership (by simp [Link.produces])
              injection sameLink with leftEquation rightEquation
              subst candidateLeft
              subst candidateRight
              have oldLeft :=
                recoverOldToken candidateLeftMarked (by simp [leftMarked])
              have leftTokenEquation :
                  candidateLeftToken = leftToken :=
                Option.some.inj
                  (oldLeft.symm.trans leftMarked)
              have conclusionNext :
                  next.mark conclusion = some outputToken := by
                rw [marking]
                simp [UnificationMarking.setMark]
              have conclusionTokenEquation :
                  candidateConclusionToken = outputToken :=
                Option.some.inj
                  (candidateConclusionMarked.symm.trans conclusionNext)
              subst candidateLeftToken
              subst candidateConclusionToken
              exact (threads _ _).mpr
                (Or.inr
                  ⟨Or.inl
                      (state.sameThreadEquivalence.1 leftToken),
                    outputTokenFromPremiseThread⟩)
            · have oldConclusion :
                  state.mark candidateConclusion =
                    some candidateConclusionToken := by
                rw [marking] at candidateConclusionMarked
                simpa [UnificationMarking.setMark,
                  sameConclusion] using candidateConclusionMarked
              have premisesPresent :=
                closed
                  (.tensor candidateLeft candidateRight candidateConclusion)
                  candidateMembership (by simp [oldConclusion])
              have oldLeft :=
                recoverOldToken candidateLeftMarked premisesPresent.1
              exact liftRelation
                ((threaded
                  (.tensor candidateLeft candidateRight candidateConclusion)
                  candidateMembership).1 oldLeft oldConclusion)
          · intro candidateRightToken candidateConclusionToken
              candidateRightMarked candidateConclusionMarked
            by_cases sameConclusion : candidateConclusion = conclusion
            · subst candidateConclusion
              have sameLink :
                  Link.tensor left right conclusion =
                    Link.tensor candidateLeft candidateRight conclusion :=
                connective_eq_of_shared_conclusion structural
                  (conclusion := conclusion)
                  linkMembership (by simp [Link.produces])
                  candidateMembership (by simp [Link.produces])
              injection sameLink with leftEquation rightEquation
              subst candidateLeft
              subst candidateRight
              have oldRight :=
                recoverOldToken candidateRightMarked (by simp [rightMarked])
              have rightTokenEquation :
                  candidateRightToken = rightToken :=
                Option.some.inj
                  (oldRight.symm.trans rightMarked)
              have conclusionNext :
                  next.mark conclusion = some outputToken := by
                rw [marking]
                simp [UnificationMarking.setMark]
              have conclusionTokenEquation :
                  candidateConclusionToken = outputToken :=
                Option.some.inj
                  (candidateConclusionMarked.symm.trans conclusionNext)
              subst candidateRightToken
              subst candidateConclusionToken
              exact (threads _ _).mpr
                (Or.inr
                  ⟨Or.inr
                      (state.sameThreadEquivalence.1 rightToken),
                    outputTokenFromPremiseThread⟩)
            · have oldConclusion :
                  state.mark candidateConclusion =
                    some candidateConclusionToken := by
                rw [marking] at candidateConclusionMarked
                simpa [UnificationMarking.setMark,
                  sameConclusion] using candidateConclusionMarked
              have premisesPresent :=
                closed
                  (.tensor candidateLeft candidateRight candidateConclusion)
                  candidateMembership (by simp [oldConclusion])
              have oldRight :=
                recoverOldToken candidateRightMarked premisesPresent.2
              exact liftRelation
                ((threaded
                  (.tensor candidateLeft candidateRight candidateConclusion)
                  candidateMembership).2 oldRight oldConclusion)

/-- Causal closure and reference-edge threading are preserved together by one
independent unification step. -/
theorem causallyThreaded
    {certificate : Certificate}
    {state next : UnificationMarking certificate}
    (structural : certificate.StructurallyWellFormed)
    (coherent : state.CausallyThreaded)
    (step : UnificationStep certificate state next) :
    next.CausallyThreaded :=
  ⟨step.markingCausallyClosed structural coherent.1,
    step.referenceLinksThreaded structural coherent.1 coherent.2⟩

/-- One abstract unification step preserves connectivity of every semantic
thread inside the active all-left switching subgraph. -/
theorem threadConnected
    {certificate : Certificate}
    {state next : UnificationMarking certificate}
    (connected : state.ThreadConnected)
    (step : UnificationStep certificate state next) :
    next.ThreadConnected := by
  have extension : state.MarkDomainExtends next :=
    step.markDomainExtends
  have liftWalk {first second : Vertex}
      (walk : state.activeReferenceGraph.Walk first second) :
      next.activeReferenceGraph.Walk first second :=
    UnificationMarking.walk_mono walk
      (state.activeReferenceEdges_mono extension)
  rcases state.sameThreadEquivalence with
    ⟨reflexive, symmetric, transitive⟩
  intro firstVertex secondVertex firstToken secondToken
    firstMarked secondMarked synchronized
  cases step
  case start left right linkMembership leftUnmarked rightUnmarked
      freshIsolated tokenCount marking threads =>
      have classify :
          ∀ {vertex token},
            next.mark vertex = some token →
              (((vertex = left ∨ vertex = right) ∧
                  token = state.tokenCount) ∨
                state.mark vertex = some token) := by
        intro vertex token marked
        rw [marking] at marked
        by_cases rightCase : vertex = right
        · left
          exact ⟨Or.inr rightCase, by
            simp [UnificationMarking.setMark, rightCase] at marked
            exact marked.symm⟩
        · by_cases leftCase : vertex = left
          · left
            exact ⟨Or.inl leftCase, by
              simp [UnificationMarking.setMark, leftCase] at marked
              exact marked.symm⟩
          · right
            simpa [UnificationMarking.setMark, rightCase,
              leftCase] using marked
      have leftNext :
          next.mark left = some state.tokenCount := by
        rw [marking]
        by_cases same : left = right
        · simp [UnificationMarking.setMark, same]
        · simp [UnificationMarking.setMark, same]
      have rightNext :
          next.mark right = some state.tokenCount := by
        rw [marking]
        simp [UnificationMarking.setMark]
      have axiomAdjacent :
          next.activeReferenceGraph.Adjacent left right :=
        next.activeReferenceGraph_axiomAdjacent
          linkMembership leftNext rightNext
      have oldSynchronized :
          state.sameThread firstToken secondToken := by
        exact (threads firstToken secondToken).mp synchronized
      rcases classify firstMarked with
        ⟨firstEndpoint, firstFresh⟩ | firstOld
      · rcases classify secondMarked with
          ⟨secondEndpoint, secondFresh⟩ | secondOld
        · subst firstToken
          subst secondToken
          rcases firstEndpoint with firstLeft | firstRight <;>
            rcases secondEndpoint with secondLeft | secondRight
          · subst firstVertex
            subst secondVertex
            exact .refl _
          · subst firstVertex
            subst secondVertex
            exact .step (.refl _) axiomAdjacent
          · subst firstVertex
            subst secondVertex
            exact .step (.refl _)
              (by
                rcases axiomAdjacent with
                  ⟨edge, membership, direction⟩
                exact ⟨edge, membership,
                  direction.elim Or.inr Or.inl⟩)
          · subst firstVertex
            subst secondVertex
            exact .refl _
        · have secondBound : secondToken < state.tokenCount :=
            state.markedTokenBound secondOld
          subst firstToken
          exact False.elim
            (freshIsolated
              (old := secondToken) secondBound
              (symmetric oldSynchronized))
      · rcases classify secondMarked with
          ⟨secondEndpoint, secondFresh⟩ | secondOld
        · have firstBound : firstToken < state.tokenCount :=
            state.markedTokenBound firstOld
          subst secondToken
          exact False.elim
            (freshIsolated
              (old := firstToken) firstBound
              oldSynchronized)
        · exact liftWalk
            (connected firstOld secondOld oldSynchronized)
  case forward left right conclusion leftToken rightToken outputToken
      linkMembership conclusionUnmarked leftMarked rightMarked
      premisesSynchronized outputTokenAllocated outputTokenSynchronized
      tokenCount marking threads =>
      have classify :
          ∀ {vertex token},
            next.mark vertex = some token →
              ((vertex = conclusion ∧ token = outputToken) ∨
                state.mark vertex = some token) := by
        intro vertex token marked
        rw [marking] at marked
        by_cases conclusionCase : vertex = conclusion
        · left
          exact ⟨conclusionCase, by
            simp [UnificationMarking.setMark,
              conclusionCase] at marked
            exact marked.symm⟩
        · right
          simpa [UnificationMarking.setMark,
            conclusionCase] using marked
      have conclusionNext :
          next.mark conclusion = some outputToken := by
        rw [marking]
        simp [UnificationMarking.setMark]
      have leftNextSome :
          (next.mark left).isSome = true :=
        extension left (by simp [leftMarked])
      have leftNext :
          ∃ token, next.mark left = some token := by
        cases lookup : next.mark left with
        | none =>
            simp [lookup] at leftNextSome
        | some token =>
            exact ⟨token, rfl⟩
      rcases leftNext with ⟨nextLeftToken, leftNext⟩
      have parAdjacent :
          next.activeReferenceGraph.Adjacent left conclusion :=
        next.activeReferenceGraph_parLeftAdjacent
          linkMembership leftNext conclusionNext
      have relation :
          state.sameThread firstToken secondToken := by
        rw [threads] at synchronized
        exact synchronized
      rcases classify firstMarked with
        ⟨firstConclusion, firstOutput⟩ | firstOld
      · rcases classify secondMarked with
          ⟨secondConclusion, secondOutput⟩ | secondOld
        · subst firstVertex
          subst secondVertex
          exact .refl _
        · subst firstVertex
          subst firstToken
          have leftRelated :
              state.sameThread leftToken secondToken :=
            transitive (symmetric outputTokenSynchronized) relation
          have oldWalk :=
            connected leftMarked secondOld leftRelated
          exact
            UnificationMarking.walk_trans
              (.step (.refl _)
                (by
                  rcases parAdjacent with
                    ⟨edge, membership, direction⟩
                  exact ⟨edge, membership,
                    direction.elim Or.inr Or.inl⟩))
              (liftWalk oldWalk)
      · rcases classify secondMarked with
          ⟨secondConclusion, secondOutput⟩ | secondOld
        · subst secondVertex
          subst secondToken
          have firstRelated :
              state.sameThread firstToken leftToken :=
            transitive relation outputTokenSynchronized
          have oldWalk :=
            connected firstOld leftMarked firstRelated
          exact
            UnificationMarking.walk_trans
              (liftWalk oldWalk)
              (.step (.refl _) parAdjacent)
        · exact liftWalk
            (connected firstOld secondOld relation)
  case unify left right conclusion leftToken rightToken outputToken
      linkMembership conclusionUnmarked leftMarked rightMarked
      premisesDistinct outputTokenAllocated outputTokenFromPremiseThread
      tokenCount marking threads =>
      have classify :
          ∀ {vertex token},
            next.mark vertex = some token →
              ((vertex = conclusion ∧ token = outputToken) ∨
                state.mark vertex = some token) := by
        intro vertex token marked
        rw [marking] at marked
        by_cases conclusionCase : vertex = conclusion
        · left
          exact ⟨conclusionCase, by
            simp [UnificationMarking.setMark,
              conclusionCase] at marked
            exact marked.symm⟩
        · right
          simpa [UnificationMarking.setMark,
            conclusionCase] using marked
      have conclusionNext :
          next.mark conclusion = some outputToken := by
        rw [marking]
        simp [UnificationMarking.setMark]
      have leftNextSome :
          (next.mark left).isSome = true :=
        extension left (by simp [leftMarked])
      have rightNextSome :
          (next.mark right).isSome = true :=
        extension right (by simp [rightMarked])
      have leftNext :
          ∃ token, next.mark left = some token := by
        cases lookup : next.mark left with
        | none =>
            simp [lookup] at leftNextSome
        | some token =>
            exact ⟨token, rfl⟩
      have rightNext :
          ∃ token, next.mark right = some token := by
        cases lookup : next.mark right with
        | none =>
            simp [lookup] at rightNextSome
        | some token =>
            exact ⟨token, rfl⟩
      rcases leftNext with ⟨nextLeftToken, leftNext⟩
      rcases rightNext with ⟨nextRightToken, rightNext⟩
      have tensorAdjacent :=
        next.activeReferenceGraph_tensorAdjacent
          linkMembership leftNext rightNext conclusionNext
      have leftToRight :
          next.activeReferenceGraph.Walk left right :=
        UnificationMarking.walk_trans
          (.step (.refl _) tensorAdjacent.1)
          (.step (.refl _)
            (by
              rcases tensorAdjacent.2 with
                ⟨edge, membership, direction⟩
              exact ⟨edge, membership,
                direction.elim Or.inr Or.inl⟩))
      have rightToLeft :
          next.activeReferenceGraph.Walk right left :=
        UnificationMarking.walk_reverse leftToRight
      have merged :
          state.MergeExtension leftToken rightToken
            firstToken secondToken :=
        (threads firstToken secondToken).mp synchronized
      rcases classify firstMarked with
        ⟨firstConclusion, firstOutput⟩ | firstOld
      · rcases classify secondMarked with
          ⟨secondConclusion, secondOutput⟩ | secondOld
        · subst firstVertex
          subst secondVertex
          exact .refl _
        · subst firstVertex
          subst firstToken
          have secondMember :
              state.sameThread leftToken secondToken ∨
                state.sameThread rightToken secondToken := by
            rcases merged with old | ⟨_outputMember, member⟩
            · rcases outputTokenFromPremiseThread with
                outputLeft | outputRight
              · exact Or.inl
                  (transitive (symmetric outputLeft) old)
              · exact Or.inr
                  (transitive (symmetric outputRight) old)
            · exact member.elim
                (fun related => Or.inl (symmetric related))
                (fun related => Or.inr (symmetric related))
          rcases secondMember with secondLeft | secondRight
          · have oldWalk :=
              connected leftMarked secondOld secondLeft
            exact
              UnificationMarking.walk_trans
                (.step (.refl _)
                  (by
                    rcases tensorAdjacent.1 with
                      ⟨edge, membership, direction⟩
                    exact ⟨edge, membership,
                      direction.elim Or.inr Or.inl⟩))
                (liftWalk oldWalk)
          · have oldWalk :=
              connected rightMarked secondOld secondRight
            exact
              UnificationMarking.walk_trans
                (.step (.refl _)
                  (by
                    rcases tensorAdjacent.2 with
                      ⟨edge, membership, direction⟩
                    exact ⟨edge, membership,
                      direction.elim Or.inr Or.inl⟩))
                (liftWalk oldWalk)
      · rcases classify secondMarked with
          ⟨secondConclusion, secondOutput⟩ | secondOld
        · subst secondVertex
          subst secondToken
          have firstMember :
              state.sameThread firstToken leftToken ∨
                state.sameThread firstToken rightToken := by
            rcases merged with old | ⟨member, _outputMember⟩
            · rcases outputTokenFromPremiseThread with
                outputLeft | outputRight
              · exact Or.inl (transitive old outputLeft)
              · exact Or.inr (transitive old outputRight)
            · exact member
          rcases firstMember with firstLeft | firstRight
          · have oldWalk :=
              connected firstOld leftMarked firstLeft
            exact
              UnificationMarking.walk_trans
                (liftWalk oldWalk)
                (.step (.refl _) tensorAdjacent.1)
          · have oldWalk :=
              connected firstOld rightMarked firstRight
            exact
              UnificationMarking.walk_trans
                (liftWalk oldWalk)
                (.step (.refl _) tensorAdjacent.2)
        · rcases merged with old | ⟨firstMember, secondMember⟩
          · exact liftWalk (connected firstOld secondOld old)
          · rcases firstMember with firstLeft | firstRight <;>
              rcases secondMember with secondLeft | secondRight
            · have firstWalk :=
                liftWalk (connected firstOld leftMarked firstLeft)
              have secondWalk :=
                liftWalk
                  (connected leftMarked secondOld
                    (symmetric secondLeft))
              exact UnificationMarking.walk_trans
                firstWalk secondWalk
            · have firstWalk :=
                liftWalk (connected firstOld leftMarked firstLeft)
              have secondWalk :=
                liftWalk
                  (connected rightMarked secondOld
                    (symmetric secondRight))
              exact UnificationMarking.walk_trans firstWalk
                (UnificationMarking.walk_trans
                  leftToRight secondWalk)
            · have firstWalk :=
                liftWalk (connected firstOld rightMarked firstRight)
              have secondWalk :=
                liftWalk
                  (connected leftMarked secondOld
                    (symmetric secondLeft))
              exact UnificationMarking.walk_trans firstWalk
                (UnificationMarking.walk_trans
                  rightToLeft secondWalk)
            · have firstWalk :=
                liftWalk (connected firstOld rightMarked firstRight)
              have secondWalk :=
                liftWalk
                  (connected rightMarked secondOld
                    (symmetric secondRight))
              exact UnificationMarking.walk_trans
                firstWalk secondWalk

/-- Every abstract transition uses a submitted link of the corresponding
Figure-5 class. -/
theorem link_exists {certificate : Certificate}
    {state next : UnificationMarking certificate}
    (step : UnificationStep certificate state next) :
    (∃ left right,
      Link.axiom left right ∈ certificate.links) ∨
    (∃ left right conclusion,
      Link.par left right conclusion ∈ certificate.links) ∨
    (∃ left right conclusion,
      Link.tensor left right conclusion ∈ certificate.links) := by
  cases step with
  | start membership =>
      exact Or.inl ⟨_, _, membership⟩
  | forward membership =>
      exact Or.inr <| Or.inl ⟨_, _, _, membership⟩
  | unify membership =>
      exact Or.inr <| Or.inr ⟨_, _, _, membership⟩

/-- Each Figure-5 transition marks the conclusion occurrence of the link it
fires. For an axiom/start transition, both axiom conclusions are marked with
the fresh token. -/
theorem marks_fired_conclusion {certificate : Certificate}
    {state next : UnificationMarking certificate}
    (step : UnificationStep certificate state next) :
    (∃ left right,
      Link.axiom left right ∈ certificate.links ∧
        (next.mark left).isSome = true ∧
        (next.mark right).isSome = true) ∨
    (∃ left right conclusion,
      Link.par left right conclusion ∈ certificate.links ∧
        (next.mark conclusion).isSome = true) ∨
    (∃ left right conclusion,
      Link.tensor left right conclusion ∈ certificate.links ∧
        (next.mark conclusion).isSome = true) := by
  cases step with
  | start membership leftUnmarked rightUnmarked freshIsolated
      tokenCount marking threads =>
      left
      refine ⟨_, _, membership, ?_, ?_⟩
      · simp [marking, UnificationMarking.setMark]
      · simp [marking, UnificationMarking.setMark]
  | forward membership conclusionUnmarked leftMarked rightMarked
      premisesSynchronized outputTokenAllocated outputTokenSynchronized
      tokenCount marking threads =>
      right
      left
      refine ⟨_, _, _, membership, ?_⟩
      simp [marking, UnificationMarking.setMark]
  | unify membership conclusionUnmarked leftMarked rightMarked
      premisesDistinct outputTokenAllocated outputTokenFromPremiseThread
      tokenCount marking threads =>
      right
      right
      refine ⟨_, _, _, membership, ?_⟩
      simp [marking, UnificationMarking.setMark]

/-- Abstract unification never retires an allocated token number. Start adds
one token; forward and unify preserve the allocation count. -/
theorem tokenCount_mono {certificate : Certificate}
    {state next : UnificationMarking certificate}
    (step : UnificationStep certificate state next) :
    state.tokenCount ≤ next.tokenCount := by
  cases step with
  | start _ _ _ _ tokenCount _ _ =>
      rw [tokenCount]
      exact Nat.le_add_right _ _
  | forward _ _ _ _ _ _ _ tokenCount _ _ =>
      exact Nat.le_of_eq tokenCount.symm
  | unify _ _ _ _ _ _ _ tokenCount _ _ =>
      exact Nat.le_of_eq tokenCount.symm

end UnificationStep

namespace UnificationExecution

/-- Every finite abstract execution preserves connectivity of semantic
threads inside the active all-left switching subgraph. -/
theorem threadConnected
    {certificate : Certificate}
    {initial final : UnificationMarking certificate}
    (execution : UnificationExecution certificate initial final)
    (connected : initial.ThreadConnected) :
    final.ThreadConnected := by
  induction execution with
  | refl =>
      exact connected
  | step transition rest induction =>
      exact induction (transition.threadConnected connected)

/-- Every finite independent execution from a causally threaded marking
preserves causal closure and exact threading of retained reference links. -/
theorem causallyThreaded
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {initial final : UnificationMarking certificate}
    (execution : UnificationExecution certificate initial final)
    (coherent : initial.CausallyThreaded) :
    final.CausallyThreaded := by
  induction execution with
  | refl =>
      exact coherent
  | step transition rest induction =>
      exact induction
        (transition.causallyThreaded structural coherent)

end UnificationExecution

end ProofNetIR
