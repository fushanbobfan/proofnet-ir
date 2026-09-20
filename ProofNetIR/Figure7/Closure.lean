import ProofNetIR.Figure7.TailLaw

/-!
# Region closure of the delayed stack

Every marked vertex belongs to the class of the sigma boundary below its raw
mark; the region of a class is its marked vertices together with the raw
vertices of the ready bucket stored at that boundary. `RegionClosure` says
that the marked part of every region is closed under the link structure,
except at par links whose other premise lies outside the region, that the
active class carries no tensor premise still waiting for its `new`, and that
a par whose premises are marked in two different classes has its conclusion
in the waiting cell of the older one.

The predicate is order-free: it never inspects the order of a ready bucket.
Its purpose is the connectivity argument that every non-conclusion left in
the active bucket after a `nop` or `wait` is forced by switching
connectedness, which is the `nop`/`wait` half of the history-tail law.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- The raw mark of a vertex, if any. -/
def Marked (stack : SequentialStackState) (vertex : Vertex) : Prop :=
  ∃ age, stack.marks[vertex]? = some (some age)

/-- The class of a marked vertex: the sigma boundary at or below its raw mark. -/
def markClass? (stack : SequentialStackState) (vertex : Vertex) : Option RawTokenAge :=
  match stack.marks[vertex]? with
  | some (some age) => sigmaBoundary? stack.sigma age
  | _ => none

/-- The ready bucket stored at a sigma boundary. -/
def bucketAt? (stack : SequentialStackState) (boundary : RawTokenAge) : Option (List Vertex) :=
  (stack.sigma.zip stack.ready).lookup boundary

/-- A vertex is in the region of a class when it is marked in that class or
raw in that class's ready bucket. -/
def InRegion (stack : SequentialStackState) (cls : RawTokenAge) (vertex : Vertex) : Prop :=
  markClass? stack vertex = some cls ∨
    ∃ bucket, bucketAt? stack cls = some bucket ∧ vertex ∈ bucket

/-- The two endpoints of a submitted axiom link, in either order. -/
def AxiomLinked (certificate : Certificate) (left right : Vertex) : Prop :=
  .axiom left right ∈ certificate.links ∨ .axiom right left ∈ certificate.links

/-- A premise, its mate, and the conclusion of a submitted tensor link, in
either premise order. -/
def TensorLinked (certificate : Certificate) (premise mate conclusion : Vertex) : Prop :=
  .tensor premise mate conclusion ∈ certificate.links ∨
    .tensor mate premise conclusion ∈ certificate.links

/-- A premise, its mate, and the conclusion of a submitted par link, in either
premise order. -/
def ParLinked (certificate : Certificate) (premise mate conclusion : Vertex) : Prop :=
  .par premise mate conclusion ∈ certificate.links ∨
    .par mate premise conclusion ∈ certificate.links

/-- Region closure of a delayed stack state. -/
structure RegionClosure (certificate : Certificate) (stack : SequentialStackState) : Prop where
  /-- A marked axiom endpoint has its partner in the same region. -/
  pairsMarked : ∀ {left right cls}, AxiomLinked certificate left right →
    markClass? stack left = some cls → InRegion stack cls right
  /-- A raw axiom endpoint has its partner in the same bucket or marked in
  that bucket's class. -/
  pairsRaw : ∀ {left right boundary bucket}, AxiomLinked certificate left right →
    bucketAt? stack boundary = some bucket → left ∈ bucket →
    right ∈ bucket ∨ markClass? stack right = some boundary
  /-- No tensor premise of the active class waits for its mate. -/
  tensorTop : ∀ {premise mate conclusion active}, TensorLinked certificate premise mate conclusion →
    stack.sigma.getLast? = some active → markClass? stack premise = some active →
    Marked stack mate
  /-- Each class has at most one tensor premise waiting for its mate. -/
  tensorOne : ∀ {premise mate conclusion premise' mate' conclusion' cls},
    TensorLinked certificate premise mate conclusion →
    TensorLinked certificate premise' mate' conclusion' →
    markClass? stack premise = some cls → ¬ Marked stack mate →
    markClass? stack premise' = some cls → ¬ Marked stack mate' →
    premise = premise'
  /-- A tensor with both premises marked has fired inside one class. -/
  tensorFired : ∀ {premise mate conclusion cls}, TensorLinked certificate premise mate conclusion →
    markClass? stack premise = some cls → Marked stack mate →
    markClass? stack mate = some cls ∧ InRegion stack cls conclusion
  /-- A par with both premises marked in one class has fired there. -/
  parFired : ∀ {premise mate conclusion cls}, ParLinked certificate premise mate conclusion →
    markClass? stack premise = some cls → markClass? stack mate = some cls →
    InRegion stack cls conclusion
  /-- A connective conclusion in a region has both premises marked there. -/
  down : ∀ {premise mate conclusion cls},
    (TensorLinked certificate premise mate conclusion ∨ ParLinked certificate premise mate conclusion) →
    InRegion stack cls conclusion →
    markClass? stack premise = some cls ∧ markClass? stack mate = some cls
  /-- A par with premises marked in two classes waits at the older boundary. -/
  waitingForward : ∀ {premise mate conclusion cls cls'}, ParLinked certificate premise mate conclusion →
    markClass? stack premise = some cls → markClass? stack mate = some cls' → cls ≠ cls' →
    ∃ payload, stack.waiting[min cls cls']? = some (.initialized payload) ∧ conclusion ∈ payload
  /-- Every waiting vertex is such a par conclusion. -/
  waitingBackward : ∀ {boundary payload conclusion},
    stack.waiting[boundary]? = some (.initialized payload) → conclusion ∈ payload →
    ∃ premise mate cls cls', .par premise mate conclusion ∈ certificate.links ∧
      markClass? stack premise = some cls ∧ markClass? stack mate = some cls' ∧
      cls ≠ cls' ∧ min cls cls' = boundary


/-! ## Switching boundary

For a set of vertices, choose at every par the premise outside the set when
exactly one premise is inside. In the resulting switching graph, every edge
leaving the set starts at a raw vertex of the set's bucket. -/

/-- The par choice that cuts the edge on the inside premise. -/
def cutChoice (inside : Vertex → Bool) (choice : Edge × Edge) : Edge :=
  if inside choice.1.first && !inside choice.2.first then choice.2
  else if inside choice.2.first && !inside choice.1.first then choice.1
  else choice.1

private theorem choiceSelection_cutChoice (inside : Vertex → Bool) :
    ∀ choices : List (Edge × Edge),
      Certificate.ChoiceSelection choices (choices.map (cutChoice inside))
  | [] => .nil
  | (left, right) :: rest => by
      show Certificate.ChoiceSelection ((left, right) :: rest)
        (cutChoice inside (left, right) :: rest.map (cutChoice inside))
      unfold cutChoice
      dsimp only
      split
      · exact .right (choiceSelection_cutChoice inside rest)
      · split
        · exact .left (choiceSelection_cutChoice inside rest)
        · exact .left (choiceSelection_cutChoice inside rest)

private theorem Graph.Walk.boundary {graph : Graph} {P : Vertex → Prop} {start finish : Vertex}
    (walk : graph.Walk start finish) (inside : P start) (outside : ¬ P finish) :
    ∃ u v, P u ∧ ¬ P v ∧ graph.Adjacent u v := by
  induction walk with
  | refl => exact absurd inside outside
  | @step middle _ walk adjacent ih =>
      by_cases inMiddle : P middle
      · exact ⟨_, _, inMiddle, outside, adjacent⟩
      · exact ih inMiddle

private theorem Graph.Adjacent.symm {graph : Graph} {left right : Vertex}
    (adjacent : graph.Adjacent left right) : graph.Adjacent right left := by
  obtain ⟨edge, member, orientation⟩ := adjacent
  exact ⟨edge, member, orientation.symm⟩

private theorem mem_fixedEdges {certificate : Certificate} {edge : Edge}
    (member : edge ∈ certificate.fixedEdges) :
    (∃ left right, .axiom left right ∈ certificate.links ∧ edge = ⟨left, right⟩) ∨
    (∃ left right conclusion, .tensor left right conclusion ∈ certificate.links ∧
      (edge = ⟨left, conclusion⟩ ∨ edge = ⟨right, conclusion⟩)) := by
  unfold Certificate.fixedEdges at member
  rw [List.mem_flatMap] at member
  obtain ⟨link, linkMember, edgeMember⟩ := member
  cases link with
  | «axiom» left right =>
      simp only [List.mem_singleton] at edgeMember
      exact Or.inl ⟨left, right, linkMember, edgeMember⟩
  | tensor left right conclusion =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at edgeMember
      exact Or.inr ⟨left, right, conclusion, linkMember, edgeMember⟩
  | par _ _ _ => simp at edgeMember

private theorem mem_cutSelection {certificate : Certificate} {inside : Vertex → Bool} {edge : Edge}
    (member : edge ∈ certificate.parChoices.map (cutChoice inside)) :
    ∃ left right conclusion, .par left right conclusion ∈ certificate.links ∧
      edge = cutChoice inside (⟨left, conclusion⟩, ⟨right, conclusion⟩) := by
  rw [List.mem_map] at member
  obtain ⟨choice, choiceMember, rfl⟩ := member
  unfold Certificate.parChoices at choiceMember
  rw [List.mem_filterMap] at choiceMember
  obtain ⟨link, linkMember, choiceEq⟩ := choiceMember
  cases link with
  | «axiom» _ _ => simp at choiceEq
  | tensor _ _ _ => simp at choiceEq
  | par left right conclusion =>
      simp only [Option.some.injEq] at choiceEq
      exact ⟨left, right, conclusion, linkMember, by rw [choiceEq]⟩

/-- In a correct certificate, any set containing one in-bounds vertex and
missing another has a boundary edge of the cutting switching. -/
theorem boundary_edge_of_correct {certificate : Certificate}
    (correct : certificate.DeclarativelyCorrect) (inside : Vertex → Bool)
    {start finish : Vertex} (startBound : start < certificate.formulas.size)
    (finishBound : finish < certificate.formulas.size)
    (startInside : inside start = true) (finishOutside : inside finish = false) :
    ∃ u v, inside u = true ∧ inside v = false ∧
      (certificate.graphForSelection (certificate.parChoices.map (cutChoice inside))).Adjacent u v := by
  have switching : certificate.SwitchingGraph
      (certificate.graphForSelection (certificate.parChoices.map (cutChoice inside))) :=
    ⟨_, choiceSelection_cutChoice inside certificate.parChoices, rfl⟩
  have connected := (correct.2 _ switching).2.1
  have walkStart := connected.2 start startBound
  have walkFinish := connected.2 finish finishBound
  by_cases origin : inside 0 = true
  · obtain ⟨u, v, uInside, vOutside, adjacent⟩ :=
      Graph.Walk.boundary (P := fun v ↦ inside v = true) walkFinish origin
        (by simp [finishOutside])
    exact ⟨u, v, uInside, by simpa using vOutside, adjacent⟩
  · obtain ⟨u, v, uOutside, vInside, adjacent⟩ :=
      Graph.Walk.boundary (P := fun v ↦ inside v = false) walkStart
        (by simpa using origin) (by simp [startInside])
    exact ⟨v, u, by simpa using vInside, uOutside, adjacent.symm⟩


/-! ## C12 from region closure

The active region is the active class together with the active bucket.
Every boundary edge of the cutting switching starts at a raw non-conclusion
of the bucket, and the popped par premise's mate lies outside the region, so
connectedness leaves a non-conclusion behind the head. -/

private theorem lookup_zip_last {keys : List Nat} {values : List (List Vertex)} {key : Nat}
    {value : List Vertex} (increasing : keys.Pairwise (· < ·))
    (aligned : values.length = keys.length) (lastKey : keys.getLast? = some key)
    (lastValue : values.getLast? = some value) :
    (keys.zip values).lookup key = some value := by
  induction keys generalizing values with
  | nil => simp at lastKey
  | cons first rest ih =>
      cases values with
      | nil => simp at aligned
      | cons firstValue restValues =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at aligned
          cases rest with
          | nil =>
              cases restValues with
              | nil =>
                  simp only [List.getLast?_singleton, Option.some.injEq] at lastKey lastValue
                  subst lastKey; subst lastValue
                  simp
              | cons _ _ => simp at aligned
          | cons second more =>
              cases restValues with
              | nil => simp at aligned
              | cons secondValue moreValues =>
                  have lastKey' : (second :: more).getLast? = some key := by
                    simpa [List.getLast?_cons_cons] using lastKey
                  have lastValue' : (secondValue :: moreValues).getLast? = some value := by
                    simpa [List.getLast?_cons_cons] using lastValue
                  have keyMem : key ∈ second :: more := List.mem_of_getLast? lastKey'
                  have firstLt : first < key := by
                    exact (List.pairwise_cons.mp increasing).1 key keyMem
                  have firstNe : (key == first) = false := by
                    simp [Nat.ne_of_gt firstLt]
                  rw [List.zip_cons_cons, List.lookup, firstNe]
                  exact ih (List.pairwise_cons.mp increasing).2 aligned lastKey' lastValue'

private theorem bucketAt?_last {stack : SequentialStackState} {age : RawTokenAge} {bucket : List Vertex}
    (increasing : stack.sigma.Pairwise (· < ·)) (aligned : stack.ready.length = stack.sigma.length)
    (sigmaLast : stack.sigma.getLast? = some age) (readyLast : stack.ready.getLast? = some bucket) :
    bucketAt? stack age = some bucket :=
  lookup_zip_last increasing aligned sigmaLast readyLast

private theorem two_le_length_of_mem_ne {α : Type} {a b : α} {l : List α}
    (aMem : a ∈ l) (bMem : b ∈ l) (ne : a ≠ b) : 2 ≤ l.length := by
  induction l with
  | nil => simp at aMem
  | cons head tail ih =>
      simp only [List.mem_cons] at aMem bMem
      simp only [List.length_cons]
      rcases aMem with rfl | aTail
      · rcases bMem with rfl | bTail
        · exact absurd rfl ne
        · have := List.length_pos_of_mem bTail
          omega
      · rcases bMem with rfl | bTail
        · have := List.length_pos_of_mem aTail
          omega
        · have := ih aTail bTail
          omega

/-- A link premise is not a certificate conclusion. -/
private theorem premise_not_conclusion {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {link : Link} (member : link ∈ certificate.links)
    {vertex : Vertex} (premise : vertex ∈ link.premises) (bound : vertex < certificate.formulas.size) :
    vertex ∉ certificate.conclusions := by
  intro conclusion
  have node := structural.2.2.2.2.2 vertex bound
  have zero : (certificate.links.filter (Link.usesAsPremise vertex)).length = 0 := by
    have := node.2
    rw [if_pos conclusion] at this
    exact this
  have inFilter : link ∈ certificate.links.filter (Link.usesAsPremise vertex) := by
    rw [List.mem_filter]
    exact ⟨member, by simpa [Link.usesAsPremise] using premise⟩
  have := List.length_pos_of_mem inFilter
  omega

/-- A vertex is a premise of at most one link. -/
private theorem premise_unique {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {link link' : Link}
    (member : link ∈ certificate.links) (member' : link' ∈ certificate.links)
    {vertex : Vertex} (premise : vertex ∈ link.premises) (premise' : vertex ∈ link'.premises)
    (bound : vertex < certificate.formulas.size) : link = link' := by
  by_cases same : link = link'
  · exact same
  have ne : link ≠ link' := same
  have node := structural.2.2.2.2.2 vertex bound
  have notConclusion := premise_not_conclusion structural member premise bound
  have one : (certificate.links.filter (Link.usesAsPremise vertex)).length = 1 := by
    have := node.2
    rw [if_neg notConclusion] at this
    exact this
  have inFilter : link ∈ certificate.links.filter (Link.usesAsPremise vertex) := by
    rw [List.mem_filter]
    exact ⟨member, by simpa [Link.usesAsPremise] using premise⟩
  have inFilter' : link' ∈ certificate.links.filter (Link.usesAsPremise vertex) := by
    rw [List.mem_filter]
    exact ⟨member', by simpa [Link.usesAsPremise] using premise'⟩
  have := two_le_length_of_mem_ne inFilter inFilter' ne
  omega


/-- The active region: marked in the active class or raw in the active bucket. -/
private def activeInside (stack : SequentialStackState) (age : RawTokenAge) (bucket : List Vertex)
    (vertex : Vertex) : Bool :=
  decide (markClass? stack vertex = some age ∨ vertex ∈ bucket)

private theorem activeInside_iff {stack : SequentialStackState} {age : RawTokenAge} {bucket : List Vertex}
    {vertex : Vertex} :
    activeInside stack age bucket vertex = true ↔
      (markClass? stack vertex = some age ∨ vertex ∈ bucket) :=
  decide_eq_true_iff

/-- The submitted par of a par consumer view, oriented from the queried premise. -/
private theorem ConnectiveBelow.parLinked {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) (par : consumer.kind = .par) :
    ParLinked certificate vertex consumer.mate consumer.conclusion := by
  have member : consumer.kind.asLink consumer.storedLeft consumer.storedRight consumer.conclusion ∈
      certificate.links := List.mem_of_getElem? consumer.link_eq
  rw [par] at member
  have premiseEq := consumer.premise_eq
  show ParLinked certificate vertex (consumer.side.mate consumer.storedLeft consumer.storedRight)
    consumer.conclusion
  generalize consumer.storedLeft = storedLeft at member premiseEq ⊢
  generalize consumer.storedRight = storedRight at member premiseEq ⊢
  generalize consumer.conclusion = conclusion at member ⊢
  generalize consumer.side = side at premiseEq ⊢
  cases side with
  | storedLeft =>
      simp only [TensorPremiseSide.premise] at premiseEq
      subst premiseEq
      exact Or.inl member
  | storedRight =>
      simp only [TensorPremiseSide.premise] at premiseEq
      subst premiseEq
      exact Or.inr member

/-- Region closure, the scheduler invariant, and correctness give C12: after the
head of the active bucket, a guarded par premise, is cut from its mate, the
remaining region still reaches the rest of the net through a raw non-conclusion
of the bucket. -/
theorem RegionClosure.guardedParHeadTail {certificate : Certificate} {state : ReservationState}
    (closure : RegionClosure certificate state.stack)
    (invariant : SchedulerInvariant certificate state)
    (correct : certificate.DeclarativelyCorrect) :
    ParHeadGuardTailNonconclusion certificate state := by
  intro age head rest consumer sigmaLast readyLast par guard
  have structural := correct.1
  have marksEq : state.core.marks = state.stack.marks := invariant.realizesSigma.marks_eq
  have bucketEq : bucketAt? state.stack age = some (head :: rest) :=
    bucketAt?_last invariant.stack_wellShaped.sigma_partition.strictIncreasing
      invariant.stack_wellShaped.ready_aligned sigmaLast readyLast
  have bucketMem : head :: rest ∈ state.stack.ready := List.mem_of_getLast? readyLast
  have inBounds : ∀ vertex ∈ head :: rest, vertex < certificate.formulas.size :=
    invariant.stack_wellShaped.ready_in_bounds _ bucketMem
  have headBound : head < certificate.formulas.size := inBounds head (List.mem_cons_self ..)
  have parLinked := ConnectiveBelow.parLinked consumer par
  have parMember : ∃ link ∈ certificate.links, head ∈ link.premises ∧ consumer.mate ∈ link.premises ∧
      (link = .par head consumer.mate consumer.conclusion ∨
        link = .par consumer.mate head consumer.conclusion) := by
    rcases parLinked with member | member
    · exact ⟨_, member, by simp [Link.premises], by simp [Link.premises], Or.inl rfl⟩
    · exact ⟨_, member, by simp [Link.premises], by simp [Link.premises], Or.inr rfl⟩
  obtain ⟨parLink, parLinkMember, headPremise, matePremise, parLinkEq⟩ := parMember
  have mateBound : consumer.mate < certificate.formulas.size := by
    have wf := consumer.wellFormed
    rw [par] at wf
    unfold ConnectiveBelow.mate
    cases consumer.side with
    | storedLeft => exact wf.2.2.2.2.1
    | storedRight => exact wf.2.2.2.1
  -- a raw premise different from the head is the witness
  have witness : ∀ {vertex : Vertex} {link : Link}, link ∈ certificate.links →
      vertex ∈ link.premises → vertex ∈ head :: rest → vertex ≠ head →
      ∃ pending, pending ∈ rest ∧ pending ∉ certificate.conclusions := by
    intro vertex link member premise bucketMember ne
    exact ⟨vertex, List.mem_of_ne_of_mem ne bucketMember,
      premise_not_conclusion structural member premise (inBounds vertex bucketMember)⟩
  -- the head is a premise of exactly the consumer's link
  have headLink : ∀ {link : Link}, link ∈ certificate.links → head ∈ link.premises → link = parLink :=
    fun member premise ↦ premise_unique structural member parLinkMember premise headPremise headBound
  by_cases mateInBucket : consumer.mate ∈ head :: rest
  · exact witness parLinkMember matePremise mateInBucket consumer.mate_ne
  have mateOutside : activeInside state.stack age (head :: rest) consumer.mate = false := by
    rw [Bool.eq_false_iff, Ne, activeInside_iff]
    rintro (mateClass | mateBucket)
    · unfold markClass? at mateClass
      rw [← marksEq] at mateClass
      rcases guard with unmarked | ⟨mateAge, mateMark, older⟩
      · rw [unmarked] at mateClass
        simp at mateClass
      · rw [mateMark] at mateClass
        have lookup : sigmaBoundary? state.stack.sigma mateAge = some age := mateClass
        exact absurd older (Nat.not_lt.mpr (sigmaBoundary?_le lookup))
    · exact mateInBucket mateBucket
  have headInside : activeInside state.stack age (head :: rest) head = true :=
    activeInside_iff.mpr (Or.inr (List.mem_cons_self ..))
  obtain ⟨u, v, uIn, vOut, adjacent⟩ :=
    boundary_edge_of_correct correct (activeInside state.stack age (head :: rest))
      headBound mateBound headInside mateOutside
  have uIn' := activeInside_iff.mp uIn
  have vOut' : ¬ (markClass? state.stack v = some age ∨ v ∈ head :: rest) := by
    intro h
    have := activeInside_iff.mpr h
    rw [vOut] at this
    exact Bool.false_ne_true this
  -- region membership from the closure's `InRegion`
  have ofRegion : ∀ {vertex : Vertex}, InRegion state.stack age vertex →
      (markClass? state.stack vertex = some age ∨ vertex ∈ head :: rest) := by
    rintro vertex (marked | ⟨bucket, lookup, member⟩)
    · exact Or.inl marked
    · rw [bucketEq] at lookup
      cases lookup
      exact Or.inr member
  have toRegion : ∀ {vertex : Vertex},
      (markClass? state.stack vertex = some age ∨ vertex ∈ head :: rest) →
        InRegion state.stack age vertex := by
    rintro vertex (marked | member)
    · exact Or.inl marked
    · exact Or.inr ⟨_, bucketEq, member⟩
  obtain ⟨edge, edgeMember, orientation⟩ := adjacent
  have edgeMember' : edge ∈ certificate.fixedEdges ∨
      edge ∈ certificate.parChoices.map (cutChoice (activeInside state.stack age (head :: rest))) :=
    List.mem_append.mp edgeMember
  rcases edgeMember' with fixed | selected
  · rcases mem_fixedEdges fixed with ⟨l, r, member, rfl⟩ | ⟨l, r, c, member, edgeEq⟩
    · -- axiom edge: both endpoints share a region
      exfalso
      have linked : AxiomLinked certificate u v := by
        rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl member
        · exact Or.inr member
      rcases uIn' with uClass | uBucket
      · exact vOut' (ofRegion (closure.pairsMarked linked uClass))
      · rcases closure.pairsRaw linked bucketEq uBucket with vBucket | vClass
        · exact vOut' (Or.inr vBucket)
        · exact vOut' (Or.inl vClass)
    · -- tensor edge
      have premiseCase : ∀ {premise mate : Vertex}, TensorLinked certificate premise mate c →
          premise ∈ (Link.tensor l r c).premises → u = premise → v = c →
          ∃ pending, pending ∈ rest ∧ pending ∉ certificate.conclusions := by
        intro premise mate linked premiseMem uEq vEq
        subst uEq; subst vEq
        rcases uIn' with uClass | uBucket
        · exfalso
          have mateMarked := closure.tensorTop linked sigmaLast uClass
          exact vOut' (ofRegion (closure.tensorFired linked uClass mateMarked).2)
        · refine witness member premiseMem uBucket ?_
          intro same
          subst same
          have := headLink member premiseMem
          rcases parLinkEq with rfl | rfl <;> cases this
      have conclusionCase : ∀ {premise mate : Vertex}, TensorLinked certificate premise mate c →
          u = c → v = premise → False := by
        intro premise mate linked uEq vEq
        subst uEq; subst vEq
        exact vOut' (Or.inl (closure.down (Or.inl linked) (toRegion uIn')).1)
      rcases edgeEq with rfl | rfl
      · rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact premiseCase (Or.inl member) (by simp [Link.premises]) rfl rfl
        · exact (conclusionCase (Or.inl member) rfl rfl).elim
      · rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact premiseCase (Or.inr member) (by simp [Link.premises]) rfl rfl
        · exact (conclusionCase (Or.inr member) rfl rfl).elim
  · obtain ⟨l, r, c, member, edgeEq⟩ := mem_cutSelection selected
    have conclusionCase : ∀ {premise mate : Vertex}, ParLinked certificate premise mate c →
        u = c → v = premise → False := by
      intro premise mate linked uEq vEq
      subst uEq; subst vEq
      exact vOut' (Or.inl (closure.down (Or.inr linked) (toRegion uIn')).1)
    unfold cutChoice at edgeEq
    simp only at edgeEq
    split at edgeEq
    · -- l inside, r outside: the chosen edge is at r
      rename_i cond
      rw [Bool.and_eq_true, Bool.not_eq_true'] at cond
      subst edgeEq
      rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exfalso
        rw [uIn] at cond
        exact Bool.false_ne_true cond.2.symm
      · exact (conclusionCase (Or.inr member) rfl rfl).elim
    · split at edgeEq
      · rename_i cond
        rw [Bool.and_eq_true, Bool.not_eq_true'] at cond
        subst edgeEq
        rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exfalso
          rw [uIn] at cond
          exact Bool.false_ne_true cond.2.symm
        · exact (conclusionCase (Or.inl member) rfl rfl).elim
      · rename_i notFirst notSecond
        subst edgeEq
        rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · -- both premises inside: u = l and r is inside as well
          have rIn : activeInside state.stack age (head :: rest) r = true := by
            cases rIn : activeInside state.stack age (head :: rest) r
            · exact absurd (by rw [uIn, rIn]; rfl) notFirst
            · rfl
          have rIn' := activeInside_iff.mp rIn
          have lPremise : l ∈ (Link.par l r c).premises := by simp [Link.premises]
          have rPremise : r ∈ (Link.par l r c).premises := by simp [Link.premises]
          -- if one premise is the head, the other is the mate, which is outside
          have mateOf : (l = head → r = consumer.mate) ∧ (r = head → l = consumer.mate) := by
            constructor
            · intro lHead
              have linkEq := headLink member (by rw [← lHead]; exact lPremise)
              rcases parLinkEq with eq | eq
              · rw [eq] at linkEq
                injection linkEq with h1 h2
              · rw [eq] at linkEq
                injection linkEq with h1 h2
                exact absurd (h1.symm.trans lHead) consumer.mate_ne
            · intro rHead
              have linkEq := headLink member (by rw [← rHead]; exact rPremise)
              rcases parLinkEq with eq | eq
              · rw [eq] at linkEq
                injection linkEq with h1 h2
                exact absurd (h2.symm.trans rHead) consumer.mate_ne
              · rw [eq] at linkEq
                injection linkEq with h1 h2
          have outside : ∀ {q : Vertex}, q = consumer.mate →
              (markClass? state.stack q = some age ∨ q ∈ head :: rest) → False := by
            rintro q rfl qIn
            have := activeInside_iff.mpr qIn
            rw [mateOutside] at this
            exact Bool.false_ne_true this
          rcases uIn' with lClass | lBucket
          · rcases rIn' with rClass | rBucket
            · exact (vOut' (ofRegion (closure.parFired (Or.inl member) lClass rClass))).elim
            · refine witness member rPremise rBucket ?_
              intro rHead
              exact outside (mateOf.2 rHead) (Or.inl lClass)
          · refine witness member lPremise lBucket ?_
            intro lHead
            exact outside (mateOf.1 lHead) rIn'
        · exact (conclusionCase (Or.inl member) rfl rfl).elim


/-! ## Initialization

After a correct initialization nothing is marked, the only bucket holds the
two endpoints of the reserved axiom, and every waiting cell is undefined. -/

/-- An axiom endpoint carries an atom formula. -/
private theorem axiom_endpoint_atom {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {left right : Vertex}
    (linked : AxiomLinked certificate left right) :
    ∃ name positive, certificate.formula? left = some (.atom name positive) := by
  rcases linked with member | member
  · obtain ⟨_, _, _, formulas⟩ := structural.2.2.2.2.1 _ member
    split at formulas
    · rename_i name positive _ leftEq _
      exact ⟨name, positive, leftEq⟩
    · exact formulas.elim
  · obtain ⟨_, _, _, formulas⟩ := structural.2.2.2.2.1 _ member
    split at formulas
    · rename_i name positive _ _ leftEq
      subst formulas
      exact ⟨name, !positive, leftEq⟩
    · exact formulas.elim

/-- A connective conclusion carries a connective formula. -/
private theorem connective_conclusion_not_atom {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {premise mate conclusion : Vertex}
    (linked : TensorLinked certificate premise mate conclusion ∨
      ParLinked certificate premise mate conclusion)
    {name : String} {positive : Bool}
    (atom : certificate.formula? conclusion = some (.atom name positive)) : False := by
  have wf : ∃ link ∈ certificate.links, certificate.LinkWellFormed link ∧
      (link = .tensor premise mate conclusion ∨ link = .tensor mate premise conclusion ∨
        link = .par premise mate conclusion ∨ link = .par mate premise conclusion) := by
    rcases linked with (member | member) | (member | member) <;>
      exact ⟨_, member, structural.2.2.2.2.1 _ member, by simp⟩
  obtain ⟨link, _, wf, shape⟩ := wf
  rcases shape with rfl | rfl | rfl | rfl <;>
  · obtain ⟨_, _, _, _, _, _, formulas⟩ := wf
    split at formulas
    · rename_i _ _ _ _ _ conclusionEq
      rw [atom] at conclusionEq
      cases conclusionEq
      cases formulas
    · exact formulas.elim

/-- An atom is the endpoint of exactly one axiom link. -/
private theorem axiom_partner_unique {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {vertex partner partner' : Vertex}
    (linked : AxiomLinked certificate vertex partner)
    (linked' : AxiomLinked certificate vertex partner')
    (bound : vertex < certificate.formulas.size) : partner = partner' := by
  obtain ⟨name, positive, atom⟩ := axiom_endpoint_atom structural linked
  have node := structural.2.2.2.2.2 vertex bound
  have count : (certificate.links.filter (Link.containsAxiomEndpoint vertex)).length = 1 := by
    have := node.1
    rw [atom] at this
    exact this
  have inFilter : ∀ {other : Vertex}, AxiomLinked certificate vertex other →
      ∃ link ∈ certificate.links.filter (Link.containsAxiomEndpoint vertex),
        link = .axiom vertex other ∨ link = .axiom other vertex := by
    rintro other (member | member)
    · exact ⟨_, List.mem_filter.mpr ⟨member, by simp [Link.containsAxiomEndpoint]⟩, Or.inl rfl⟩
    · exact ⟨_, List.mem_filter.mpr ⟨member, by simp [Link.containsAxiomEndpoint]⟩, Or.inr rfl⟩
  obtain ⟨link, linkMem, linkEq⟩ := inFilter linked
  obtain ⟨link', linkMem', linkEq'⟩ := inFilter linked'
  have same : link = link' := by
    by_cases same : link = link'
    · exact same
    · have := two_le_length_of_mem_ne linkMem linkMem' same
      omega
  subst same
  rcases linkEq with rfl | rfl <;> rcases linkEq' with eq | eq <;>
    simp only [Link.axiom.injEq] at eq
  · exact eq.2
  · exact eq.2.trans eq.1
  · exact eq.1.trans eq.2
  · exact eq.1

private theorem axiomLinked_of_oriented {certificate : Certificate} {state : UnificationState}
    {fuel : Nat} {inputTags : Array Bool}
    (result : SequentialUnification.NextAxiomResult certificate state fuel inputTags)
    {reached partner : Vertex} (oriented : result.orientedEndpoints? = some (reached, partner)) :
    AxiomLinked certificate reached partner := by
  have member : Link.axiom result.left result.right ∈ certificate.links :=
    List.mem_of_getElem? result.exactLink
  unfold SequentialUnification.NextAxiomResult.orientedEndpoints? at oriented
  cases traceLast : result.trace.getLast? with
  | none => rw [traceLast] at oriented; simp [Bind.bind, Option.bind] at oriented
  | some last =>
      rw [traceLast] at oriented
      simp only [Bind.bind, Option.bind] at oriented
      split at oriented
      · rename_i isLeft
        simp only [Option.some.injEq, Prod.mk.injEq] at oriented
        obtain ⟨rfl, rfl⟩ := oriented
        rw [isLeft]
        exact Or.inl member
      · split at oriented
        · rename_i _ isRight
          simp only [Option.some.injEq, Prod.mk.injEq] at oriented
          obtain ⟨rfl, rfl⟩ := oriented
          rw [isRight]
          exact Or.inr member
        · simp at oriented

/-- Every correct initialization is region closed. -/
theorem RegionClosure.ofInitialReservation {certificate : Certificate} {after : ReservationState}
    {start : Vertex} (step : InitialReservationStep certificate after start)
    (structural : certificate.StructurallyWellFormed) :
    RegionClosure certificate after.stack := by
  obtain ⟨marksEq, _, sigmaEq, readyEq, waitingEq, _⟩ := initEnqueue?_exact step.stack_eq
  have stackEq : after.stack = step.stackAfter := congrArg ReservationState.stack step.output_eq
  have linked := axiomLinked_of_oriented step.result step.oriented_eq
  have unmarked : ∀ vertex, markClass? after.stack vertex = none := by
    intro vertex
    have marks : after.stack.marks[vertex]? =
        if vertex < certificate.formulas.size then some none else none := by
      rw [stackEq, marksEq]
      simp only [ReservationState.empty, SequentialStackState.empty, Array.getElem?_replicate]
    unfold markClass?
    rw [marks]
    by_cases h : vertex < certificate.formulas.size <;> simp [h]
  have noMarkClass : ∀ {vertex cls}, markClass? after.stack vertex = some cls → False := by
    intro vertex cls h
    rw [unmarked] at h
    cases h
  have bucketOnly : ∀ {boundary bucket}, bucketAt? after.stack boundary = some bucket →
      bucket = [step.reached, step.partner] := by
    intro boundary bucket lookup
    unfold bucketAt? at lookup
    rw [stackEq, sigmaEq, readyEq] at lookup
    simp only [List.zip_cons_cons, List.zip_nil_right, List.lookup] at lookup
    split at lookup
    · cases lookup; rfl
    · cases lookup
  have endpointBound : ∀ {vertex}, vertex ∈ [step.reached, step.partner] →
      vertex < certificate.formulas.size := by
    intro vertex member
    have wf : certificate.LinkWellFormed (.axiom step.reached step.partner) ∨
        certificate.LinkWellFormed (.axiom step.partner step.reached) := by
      rcases linked with m | m
      · exact Or.inl (structural.2.2.2.2.1 _ m)
      · exact Or.inr (structural.2.2.2.2.1 _ m)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rcases wf with ⟨_, l, r, _⟩ | ⟨_, l, r, _⟩ <;> assumption
  refine {
    pairsMarked := fun _ marked ↦ (noMarkClass marked).elim
    pairsRaw := ?_
    tensorTop := fun _ _ marked ↦ (noMarkClass marked).elim
    tensorOne := fun _ _ marked _ _ _ ↦ (noMarkClass marked).elim
    tensorFired := fun _ marked _ ↦ (noMarkClass marked).elim
    parFired := fun _ marked _ ↦ (noMarkClass marked).elim
    down := ?_
    waitingForward := fun _ marked _ _ ↦ (noMarkClass marked).elim
    waitingBackward := ?_ }
  · intro endpoint other boundary bucket linkedLR lookup member
    rw [bucketOnly lookup] at member ⊢
    have bound := endpointBound member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    refine Or.inl ?_
    rcases member with rfl | rfl
    · rw [axiom_partner_unique structural linkedLR linked bound]
      simp
    · have linked' : AxiomLinked certificate step.partner step.reached := by
        rcases linked with m | m
        · exact Or.inr m
        · exact Or.inl m
      rw [axiom_partner_unique structural linkedLR linked' bound]
      simp
  · rintro premise mate conclusion cls connective (marked | ⟨bucket, lookup, member⟩)
    · exact (noMarkClass marked).elim
    · rw [bucketOnly lookup] at member
      have atomFormula : ∃ name positive, certificate.formula? conclusion = some (.atom name positive) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact axiom_endpoint_atom structural linked
        · have linked' : AxiomLinked certificate step.partner step.reached := by
            rcases linked with m | m
            · exact Or.inr m
            · exact Or.inl m
          exact axiom_endpoint_atom structural linked'
      obtain ⟨name, positive, atom⟩ := atomFormula
      exact (connective_conclusion_not_atom structural connective atom).elim
  · intro boundary payload conclusion lookup _
    rw [stackEq, waitingEq] at lookup
    simp only [ReservationState.empty, SequentialStackState.empty, Array.getElem?_replicate] at lookup
    split at lookup <;> cases lookup

end SequentialFigure7
end ProofNetIR
