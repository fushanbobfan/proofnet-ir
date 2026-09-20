import ProofNetIR.Figure7.TailLaw
import ProofNetIR.SequentialFigure7ActiveTopResidual

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


/-! ## Stack lemmas for preservation

The class of the last boundary is itself, the bucket lookup after the common
pop/mark prefix, and the uniqueness of the bucket holding a queued vertex. -/

/-- The last boundary resolves to itself. -/
private theorem sigmaBoundary?_last {sigma : List RawTokenAge} {age : RawTokenAge}
    (increasing : sigma.Pairwise (· < ·)) (last : sigma.getLast? = some age) :
    sigmaBoundary? sigma age = some age := by
  induction sigma with
  | nil => simp at last
  | cons first rest ih =>
      cases rest with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at last
          subst last
          simp [sigmaBoundary?]
      | cons second more =>
          have last' : (second :: more).getLast? = some age := by
            simpa [List.getLast?_cons_cons] using last
          have firstLt : first < age :=
            (List.pairwise_cons.mp increasing).1 age (List.mem_of_getLast? last')
          have tail := ih (List.pairwise_cons.mp increasing).2 last'
          show (if first ≤ age then
              match sigmaBoundary? (second :: more) age with
              | none => some first
              | some later => some later
            else none) = some age
          rw [if_pos (Nat.le_of_lt firstLt), tail]

/-- A raw age at or above the last boundary resolves to that boundary. -/
private theorem sigmaBoundary?_of_last_le {sigma : List RawTokenAge} {age boundary : RawTokenAge}
    (increasing : sigma.Pairwise (· < ·)) (last : sigma.getLast? = some boundary)
    (le : boundary ≤ age) : sigmaBoundary? sigma age = some boundary := by
  induction sigma with
  | nil => simp at last
  | cons first rest ih =>
      cases rest with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at last
          subst last
          simp [sigmaBoundary?, le]
      | cons second more =>
          have last' : (second :: more).getLast? = some boundary := by
            simpa [List.getLast?_cons_cons] using last
          have firstLt : first < boundary :=
            (List.pairwise_cons.mp increasing).1 boundary (List.mem_of_getLast? last')
          have tail := ih (List.pairwise_cons.mp increasing).2 last'
          show (if first ≤ age then
              match sigmaBoundary? (second :: more) age with
              | none => some first
              | some later => some later
            else none) = some boundary
          rw [if_pos (Nat.le_trans (Nat.le_of_lt firstLt) le), tail]

/-- The bucket lookup after replacing the last bucket. -/
private theorem lookup_zip_replaceLast {keys : List Nat} {values : List (List Vertex)}
    {key : Nat} {old new : List Vertex}
    (increasing : keys.Pairwise (· < ·)) (aligned : values.length = keys.length)
    (lastKey : keys.getLast? = some key) (lastValue : values.getLast? = some old)
    (query : Nat) :
    (keys.zip (values.dropLast ++ [new])).lookup query =
      if query = key then some new else (keys.zip values).lookup query := by
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
                  rw [lastKey] at *
                  by_cases same : query = key
                  · rw [same]
                    simp
                  · have ne : (query == key) = false := by simp [same]
                    simp [List.lookup, ne, same]
              | cons _ _ => simp at aligned
          | cons second more =>
              cases restValues with
              | nil => simp at aligned
              | cons secondValue moreValues =>
                  have lastKey' : (second :: more).getLast? = some key := by
                    simpa [List.getLast?_cons_cons] using lastKey
                  have lastValue' : (secondValue :: moreValues).getLast? = some old := by
                    simpa [List.getLast?_cons_cons] using lastValue
                  have firstLt : first < key :=
                    (List.pairwise_cons.mp increasing).1 key (List.mem_of_getLast? lastKey')
                  have dropLastEq : (firstValue :: secondValue :: moreValues).dropLast =
                      firstValue :: (secondValue :: moreValues).dropLast := by
                    simp [List.dropLast_cons_of_ne_nil]
                  rw [dropLastEq]
                  simp only [List.cons_append, List.zip_cons_cons, List.lookup]
                  by_cases hit : query = first
                  · rw [hit]
                    have ne : first ≠ key := Nat.ne_of_lt firstLt
                    simp [ne]
                  · have ne : (query == first) = false := by simp [hit]
                    rw [ne]
                    exact ih (List.pairwise_cons.mp increasing).2 aligned lastKey' lastValue'

private theorem marked_of_class {stack : SequentialStackState} {v : Vertex} {cls : RawTokenAge}
    (h : markClass? stack v = some cls) : Marked stack v := by
  unfold markClass? at h
  cases eq : stack.marks[v]? with
  | none => simp [eq] at h
  | some mark =>
      cases mark with
      | none => simp [eq] at h
      | some age => exact ⟨age, eq⟩

private theorem pop_class_eq {stack : SequentialStackState} {result : PopReadyMarkResult}
    {size : Nat} (shape : stack.WellShaped size)
    (pop : stack.popReadyMark? = .ok result) (v : Vertex) :
    markClass? result.after v =
      if v = result.vertex then some result.rawAge else markClass? stack v := by
  obtain ⟨_, last, unmarked, marks, _, sigma, _, _, marked⟩ := popReadyMark?_exact pop
  by_cases same : v = result.vertex
  · subst v
    simp only [markClass?, marked, sigma]
    exact sigmaBoundary?_last shape.sigma_partition.strictIncreasing last
  · simp only [if_neg same, markClass?, marks, sigma,
      Array.getElem?_setIfInBounds_ne (Ne.symm same)]

private theorem pop_marked_iff {stack : SequentialStackState} {result : PopReadyMarkResult}
    (pop : stack.popReadyMark? = .ok result) (v : Vertex) :
    Marked result.after v ↔ v = result.vertex ∨ Marked stack v := by
  obtain ⟨_, _, unmarked, marks, _, _, _, _, marked⟩ := popReadyMark?_exact pop
  by_cases same : v = result.vertex
  · subst v
    exact ⟨fun _ ↦ Or.inl rfl, fun _ ↦ ⟨_, marked⟩⟩
  · simp only [Marked, marks, Array.getElem?_setIfInBounds_ne (Ne.symm same), same, false_or]

private theorem pop_bucket_eq {stack : SequentialStackState} {result : PopReadyMarkResult}
    {size : Nat} (shape : stack.WellShaped size)
    (pop : stack.popReadyMark? = .ok result) (cls : RawTokenAge) :
    bucketAt? result.after cls =
      if cls = result.rawAge then some result.remainingTop else bucketAt? stack cls := by
  obtain ⟨top, last, _, _, _, sigma, ready, _, _⟩ := popReadyMark?_exact pop
  unfold bucketAt?
  rw [sigma, ready]
  exact lookup_zip_replaceLast shape.sigma_partition.strictIncreasing shape.ready_aligned last top cls

private theorem pop_region_iff {stack : SequentialStackState} {result : PopReadyMarkResult}
    {size : Nat} (shape : stack.WellShaped size)
    (pop : stack.popReadyMark? = .ok result) (cls : RawTokenAge) (v : Vertex) :
    InRegion result.after cls v ↔ InRegion stack cls v := by
  obtain ⟨top, last, unmarked, _⟩ := popReadyMark?_exact pop
  have bucket := bucketAt?_last shape.sigma_partition.strictIncreasing shape.ready_aligned last top
  have headNone : markClass? stack result.vertex = none := by simp [markClass?, unmarked]
  unfold InRegion
  rw [pop_class_eq shape pop, pop_bucket_eq shape pop]
  by_cases active : cls = result.rawAge <;> by_cases head : v = result.vertex
  · subst cls; subst v
    simp [bucket]
  · subst cls
    simp [head, bucket, eq_comm]
  · subst v
    simp [active, headNone, eq_comm]
  · simp [active, head]

private theorem pop_pairs_raw {certificate : Certificate} {stack : SequentialStackState}
    {result : PopReadyMarkResult} (shape : stack.WellShaped certificate.formulas.size)
    (pop : stack.popReadyMark? = .ok result) (closure : RegionClosure certificate stack)
    {left right : Vertex} {cls : RawTokenAge} {bucket : List Vertex}
    (linked : AxiomLinked certificate left right)
    (lookup : bucketAt? result.after cls = some bucket) (member : left ∈ bucket) :
    right ∈ bucket ∨ markClass? result.after right = some cls := by
  obtain ⟨top, last, unmarked, _⟩ := popReadyMark?_exact pop
  have oldBucket := bucketAt?_last shape.sigma_partition.strictIncreasing shape.ready_aligned last top
  rw [pop_bucket_eq shape pop] at lookup
  by_cases active : cls = result.rawAge
  · subst cls
    simp only [ite_true, Option.some.injEq] at lookup
    subst bucket
    rcases closure.pairsRaw linked oldBucket (List.mem_cons_of_mem _ member) with raw | marked
    · rcases List.mem_cons.mp raw with head | tail
      · exact Or.inr (by simp [pop_class_eq shape pop, head])
      · exact Or.inl tail
    · exact Or.inr (by
        rw [pop_class_eq shape pop]
        split
        · rfl
        · exact marked)
  · rw [if_neg active] at lookup
    rcases closure.pairsRaw linked lookup member with raw | marked
    · exact Or.inl raw
    · have ne : right ≠ result.vertex := by
        intro eq; subst right
        simp [markClass?, unmarked] at marked
      exact Or.inr (by simpa [pop_class_eq shape pop, ne] using marked)

private theorem pop_pairs_marked {certificate : Certificate} {stack : SequentialStackState}
    {result : PopReadyMarkResult} (shape : stack.WellShaped certificate.formulas.size)
    (pop : stack.popReadyMark? = .ok result) (closure : RegionClosure certificate stack)
    {left right : Vertex} {cls : RawTokenAge} (linked : AxiomLinked certificate left right)
    (marked : markClass? result.after left = some cls) : InRegion result.after cls right := by
  apply (pop_region_iff shape pop cls right).mpr
  rw [pop_class_eq shape pop] at marked
  by_cases head : left = result.vertex
  · subst left
    simp only [ite_true, Option.some.injEq] at marked
    subst cls
    obtain ⟨top, last, _⟩ := popReadyMark?_exact pop
    have bucket := bucketAt?_last shape.sigma_partition.strictIncreasing shape.ready_aligned last top
    rcases closure.pairsRaw linked bucket (List.mem_cons_self ..) with raw | marked
    · exact Or.inr ⟨_, bucket, raw⟩
    · exact Or.inl marked
  · rw [if_neg head] at marked
    exact closure.pairsMarked linked marked

private theorem pop_old_class {stack : SequentialStackState} {result : PopReadyMarkResult}
    {size : Nat} (shape : stack.WellShaped size) (pop : stack.popReadyMark? = .ok result)
    {v : Vertex} {cls : RawTokenAge} (marked : markClass? stack v = some cls) :
    markClass? result.after v = some cls := by
  have unmarked := (popReadyMark?_exact pop).2.2.1
  have ne : v ≠ result.vertex := by
    intro same; subst v
    simp [markClass?, unmarked] at marked
  simpa [pop_class_eq shape pop, ne] using marked

private theorem pop_closure_inert {certificate : Certificate} {stack : SequentialStackState}
    {result : PopReadyMarkResult} (shape : stack.WellShaped certificate.formulas.size)
    (pop : stack.popReadyMark? = .ok result) (closure : RegionClosure certificate stack)
    (noTensor : ∀ {mate conclusion}, TensorLinked certificate result.vertex mate conclusion → False)
    (noParMate : ∀ {mate conclusion}, ParLinked certificate result.vertex mate conclusion →
      mate ≠ result.vertex ∧ ¬ Marked stack mate) : RegionClosure certificate result.after := by
  have tensorNe : ∀ {p m c}, TensorLinked certificate p m c →
      p ≠ result.vertex ∧ m ≠ result.vertex := by
    intro p m c linked
    constructor
    · rintro rfl; exact noTensor linked
    · rintro rfl; exact noTensor linked.symm
  have tensorClass : ∀ {p m c cls}, TensorLinked certificate p m c →
      markClass? result.after p = some cls → markClass? stack p = some cls := by
    intro p m c cls linked marked
    simpa [pop_class_eq shape pop, (tensorNe linked).1] using marked
  have parClasses : ∀ {p m c cls cls'}, ParLinked certificate p m c →
      markClass? result.after p = some cls → markClass? result.after m = some cls' →
      markClass? stack p = some cls ∧ markClass? stack m = some cls' := by
    intro p m c cls cls' linked pClass mClass
    have pNe : p ≠ result.vertex := by
      intro eq; subst p
      have ne := (noParMate linked).1
      have oldMate : markClass? stack m = some cls' := by
        simpa [pop_class_eq shape pop, ne] using mClass
      exact (noParMate linked).2 (marked_of_class oldMate)
    have mNe : m ≠ result.vertex := by
      intro eq; subst m
      have oldP : markClass? stack p = some cls := by
        simpa [pop_class_eq shape pop, pNe] using pClass
      exact (noParMate linked.symm).2 (marked_of_class oldP)
    exact ⟨by simpa [pop_class_eq shape pop, pNe] using pClass,
      by simpa [pop_class_eq shape pop, mNe] using mClass⟩
  refine {
    pairsMarked := pop_pairs_marked shape pop closure
    pairsRaw := pop_pairs_raw shape pop closure
    tensorTop := ?_
    tensorOne := ?_
    tensorFired := ?_
    parFired := ?_
    down := ?_
    waitingForward := ?_
    waitingBackward := ?_ }
  · intro p m c active linked last marked
    have sigma := (popReadyMark?_exact pop).2.2.2.2.2.1
    rw [sigma] at last
    exact (pop_marked_iff pop m).mpr
      (Or.inr (closure.tensorTop linked last (tensorClass linked marked)))
  · intro p m c p' m' c' cls linked linked' marked absent marked' absent'
    exact closure.tensorOne linked linked' (tensorClass linked marked)
      (fun old ↦ absent ((pop_marked_iff pop m).mpr (Or.inr old)))
      (tensorClass linked' marked')
      (fun old ↦ absent' ((pop_marked_iff pop m').mpr (Or.inr old)))
  · intro p m c cls linked pClass mMarked
    have oldMate : Marked stack m := by
      rcases (pop_marked_iff pop m).mp mMarked with head | old
      · exact ((tensorNe linked).2 head).elim
      · exact old
    obtain ⟨mClass, conclusion⟩ := closure.tensorFired linked (tensorClass linked pClass) oldMate
    exact ⟨pop_old_class shape pop mClass, (pop_region_iff shape pop cls c).mpr conclusion⟩
  · intro p m c cls linked pClass mClass
    obtain ⟨pOld, mOld⟩ := parClasses linked pClass mClass
    exact (pop_region_iff shape pop cls c).mpr (closure.parFired linked pOld mOld)
  · intro p m c cls linked region
    obtain ⟨pClass, mClass⟩ := closure.down linked ((pop_region_iff shape pop cls c).mp region)
    exact ⟨pop_old_class shape pop pClass, pop_old_class shape pop mClass⟩
  · intro p m c cls cls' linked pClass mClass different
    obtain ⟨pOld, mOld⟩ := parClasses linked pClass mClass
    rw [(popReadyMark?_exact pop).2.2.2.2.2.2.2.1]
    exact closure.waitingForward linked pOld mOld different
  · intro boundary payload c lookup member
    rw [(popReadyMark?_exact pop).2.2.2.2.2.2.2.1] at lookup
    obtain ⟨p, m, cls, cls', linked, pClass, mClass, ne, eq⟩ :=
      closure.waitingBackward lookup member
    exact ⟨p, m, cls, cls', linked, pop_old_class shape pop pClass,
      pop_old_class shape pop mClass, ne, eq⟩

private theorem par_tensor_disjoint {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {p m c m' c' : Vertex}
    (bound : p < certificate.formulas.size) (par : ParLinked certificate p m c)
    (tensor : TensorLinked certificate p m' c') : False := by
  rcases par with par | par <;> rcases tensor with tensor | tensor <;>
    have eq := premise_unique structural par tensor
      (by simp [Link.premises]) (by simp [Link.premises]) bound <;> cases eq

private theorem par_mate_unique {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {p m c m' c' : Vertex}
    (bound : p < certificate.formulas.size) (par : ParLinked certificate p m c)
    (par' : ParLinked certificate p m' c') : m = m' ∧ c = c' := by
  rcases par with par | par <;> rcases par' with par' | par' <;>
    have eq := premise_unique structural par par'
      (by simp [Link.premises]) (by simp [Link.premises]) bound <;>
    simp only [Link.par.injEq] at eq <;> grind

private theorem pop_vertex_bound {stack : SequentialStackState} {result : PopReadyMarkResult}
    {size : Nat} (shape : stack.WellShaped size) (pop : stack.popReadyMark? = .ok result) :
    result.vertex < size := by
  have top := (popReadyMark?_exact pop).1
  exact shape.ready_in_bounds _ (List.mem_of_getLast? top) _ (List.mem_cons_self ..)

/-- The conclusion rule preserves region closure after its exact pop/mark prefix. -/
theorem ConclStep.regionClosure {certificate : Certificate} {before after : ReservationState}
    (step : ConclStep certificate before after) (structural : certificate.StructurallyWellFormed)
    (closure : RegionClosure certificate before.stack) : RegionClosure certificate after.stack := by
  rw [step.output_eq]
  have noPremise : ∀ {link}, link ∈ certificate.links →
      step.prepared.stackResult.vertex ∈ link.premises → False := by
    intro link member premise
    exact premise_not_conclusion structural member premise
      (pop_vertex_bound step.before_invariant.stack_wellShaped step.prepared.stack_eq)
      step.boundary.boundary
  apply pop_closure_inert step.before_invariant.stack_wellShaped step.prepared.stack_eq closure
  · intro m c linked
    rcases linked with member | member <;> exact noPremise member (by simp [Link.premises])
  · intro m c linked
    rcases linked with member | member <;> exact (noPremise member (by simp [Link.premises])).elim

/-- The nop rule preserves region closure because its par mate is still unmarked. -/
theorem NopStep.regionClosure {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after) (structural : certificate.StructurallyWellFormed)
    (closure : RegionClosure certificate before.stack) : RegionClosure certificate after.stack := by
  rw [step.output_eq]
  have linked := ConnectiveBelow.parLinked step.consumer step.par_eq
  have shape := step.before_invariant.stack_wellShaped
  have bound := pop_vertex_bound shape step.prepared.stack_eq
  apply pop_closure_inert shape step.prepared.stack_eq closure
  · exact fun tensor ↦ par_tensor_disjoint structural bound linked tensor
  · intro m c par
    obtain ⟨mateEq, _⟩ := par_mate_unique structural bound par linked
    rw [mateEq]
    refine ⟨step.consumer.mate_ne, ?_⟩
    rintro ⟨age, marked⟩
    have unmarked := step.mate_unmarked_before
    rw [step.before_invariant.realizesSigma.marks_eq, marked] at unmarked
    cases unmarked

private theorem axiom_region {certificate : Certificate} {stack : SequentialStackState}
    (closure : RegionClosure certificate stack) {left right : Vertex} {cls : RawTokenAge}
    (linked : AxiomLinked certificate left right) (region : InRegion stack cls left) :
    InRegion stack cls right := by
  rcases region with marked | ⟨bucket, lookup, member⟩
  · exact closure.pairsMarked linked marked
  · rcases closure.pairsRaw linked lookup member with raw | marked
    · exact Or.inr ⟨bucket, lookup, raw⟩
    · exact Or.inl marked

private theorem par_update_closure {certificate : Certificate} {stack after : SequentialStackState}
    {result : PopReadyMarkResult} {mate conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (shape : stack.WellShaped certificate.formulas.size)
    (pop : stack.popReadyMark? = .ok result) (closure : RegionClosure certificate stack)
    (linked : ParLinked certificate result.vertex mate conclusion)
    (marksEq : after.marks = result.after.marks) (sigmaEq : after.sigma = stack.sigma)
    (extend : ∀ {cls v}, InRegion stack cls v → InRegion after cls v)
    (restrict : ∀ {cls l r}, AxiomLinked certificate l r →
      InRegion after cls l → InRegion stack cls l)
    (down : ∀ {p m c cls}, (TensorLinked certificate p m c ∨ ParLinked certificate p m c) →
      InRegion after cls c → markClass? after p = some cls ∧ markClass? after m = some cls)
    (fire : ∀ {cls}, markClass? after result.vertex = some cls →
      markClass? after mate = some cls → InRegion after cls conclusion)
    (wait : ∀ {cls cls'}, markClass? after result.vertex = some cls →
      markClass? after mate = some cls' → cls ≠ cls' →
      ∃ payload, after.waiting[min cls cls']? = some (.initialized payload) ∧ conclusion ∈ payload)
    (keepWaiting : ∀ {boundary : RawTokenAge} {payload : List Vertex} {v : Vertex},
      stack.waiting[boundary]? = some (.initialized payload) →
      v ∈ payload → ∃ payload', after.waiting[boundary]? = some (.initialized payload') ∧ v ∈ payload')
    (waitingBack : ∀ {boundary payload c}, after.waiting[boundary]? = some (.initialized payload) →
      c ∈ payload → ∃ p m cls cls', .par p m c ∈ certificate.links ∧
        markClass? after p = some cls ∧ markClass? after m = some cls' ∧
        cls ≠ cls' ∧ min cls cls' = boundary) : RegionClosure certificate after := by
  have classEq : ∀ v, markClass? after v =
      if v = result.vertex then some result.rawAge else markClass? stack v := by
    intro v
    have eq : markClass? after v = markClass? result.after v := by
      simp only [markClass?, marksEq, sigmaEq, (popReadyMark?_exact pop).2.2.2.2.2.1]
    rw [eq, pop_class_eq shape pop]
  have oldClass : ∀ {v cls}, markClass? stack v = some cls → markClass? after v = some cls := by
    intro v cls marked
    have eq := pop_old_class shape pop marked
    simpa only [markClass?, marksEq, sigmaEq,
      (popReadyMark?_exact pop).2.2.2.2.2.1] using eq
  have markedEq : ∀ v, Marked after v ↔ v = result.vertex ∨ Marked stack v := by
    intro v
    rw [Marked, marksEq]
    exact pop_marked_iff pop v
  have bound := pop_vertex_bound shape pop
  have tensorNe : ∀ {p m c}, TensorLinked certificate p m c →
      p ≠ result.vertex ∧ m ≠ result.vertex := by
    intro p m c tensor
    constructor
    · rintro rfl; exact par_tensor_disjoint structural bound linked tensor
    · rintro rfl; exact par_tensor_disjoint structural bound linked tensor.symm
  have tensorClass : ∀ {p m c cls}, TensorLinked certificate p m c →
      markClass? after p = some cls → markClass? stack p = some cls := by
    intro p m c cls tensor marked
    simpa [classEq, (tensorNe tensor).1] using marked
  refine {
    pairsMarked := fun link marked ↦ extend (axiom_region closure link (restrict link (Or.inl marked)))
    pairsRaw := ?_
    tensorTop := ?_
    tensorOne := ?_
    tensorFired := ?_
    parFired := ?_
    down := down
    waitingForward := ?_
    waitingBackward := waitingBack }
  · intro l r cls bucket link lookup member
    have region := extend (axiom_region closure link (restrict link (Or.inr ⟨_, lookup, member⟩)))
    rcases region with marked | ⟨bucket', lookup', raw⟩
    · exact Or.inr marked
    · have eq := Option.some.inj (lookup'.symm.trans lookup)
      subst bucket'
      exact Or.inl raw
  · intro p m c active tensor last marked
    rw [sigmaEq] at last
    exact (markedEq m).mpr (Or.inr (closure.tensorTop tensor last (tensorClass tensor marked)))
  · intro p m c p' m' c' cls tensor tensor' marked absent marked' absent'
    exact closure.tensorOne tensor tensor' (tensorClass tensor marked)
      (fun old ↦ absent ((markedEq m).mpr (Or.inr old))) (tensorClass tensor' marked')
      (fun old ↦ absent' ((markedEq m').mpr (Or.inr old)))
  · intro p m c cls tensor marked mateMarked
    have oldMate : Marked stack m := by
      rcases (markedEq m).mp mateMarked with eq | old
      · exact ((tensorNe tensor).2 eq).elim
      · exact old
    obtain ⟨mateClass, region⟩ := closure.tensorFired tensor (tensorClass tensor marked) oldMate
    exact ⟨oldClass mateClass, extend region⟩
  · intro p m c cls par pClass mClass
    by_cases pHead : p = result.vertex
    · subst p
      obtain ⟨rfl, rfl⟩ := par_mate_unique structural bound par linked
      exact fire pClass mClass
    · by_cases mHead : m = result.vertex
      · subst m
        obtain ⟨rfl, rfl⟩ := par_mate_unique structural bound par.symm linked
        exact fire mClass pClass
      · exact extend (closure.parFired par (by simpa [classEq, pHead] using pClass)
          (by simpa [classEq, mHead] using mClass))
  · intro p m c cls cls' par pClass mClass different
    by_cases pHead : p = result.vertex
    · subst p
      obtain ⟨rfl, rfl⟩ := par_mate_unique structural bound par linked
      exact wait pClass mClass different
    · by_cases mHead : m = result.vertex
      · subst m
        obtain ⟨rfl, rfl⟩ := par_mate_unique structural bound par.symm linked
        simpa [Nat.min_comm] using wait mClass pClass (Ne.symm different)
      · obtain ⟨payload, lookup, member⟩ := closure.waitingForward par
          (by simpa [classEq, pHead] using pClass) (by simpa [classEq, mHead] using mClass) different
        exact keepWaiting lookup member

/-- Waiting preserves region closure at the exact older destination cell. -/
theorem WaitStep.regionClosure {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after) (structural : certificate.StructurallyWellFormed)
    (closure : RegionClosure certificate before.stack) : RegionClosure certificate after.stack := by
  have shape := step.before_invariant.stack_wellShaped
  have pop := step.prepared.stack_eq
  obtain ⟨_, _, _, _, _, popSigma, _, popWaiting, _⟩ := popReadyMark?_exact pop
  obtain ⟨payload, initialized, waitingEq, updated, marksEq, _, sigmaEq, readyEq⟩ :=
    prependWaiting?_exact step.destination.stack_eq
  have stackEq : after.stack = step.destination.stackAfter :=
    congrArg ReservationState.stack step.destination.output_eq
  have afterMarks : after.stack.marks = step.prepared.stackResult.after.marks := by
    rw [stackEq]; exact marksEq
  have afterSigma : after.stack.sigma = step.prepared.stackResult.after.sigma := by
    rw [stackEq]; exact sigmaEq
  have afterReady : after.stack.ready = step.prepared.stackResult.after.ready := by
    rw [stackEq]; exact readyEq
  have classEq : ∀ v, markClass? after.stack v = markClass? step.prepared.stackResult.after v := by
    intro v; simp only [markClass?, afterMarks, afterSigma]
  have oldClass : ∀ {v cls}, markClass? before.stack v = some cls →
      markClass? after.stack v = some cls := by
    intro v cls marked; rw [classEq]; exact pop_old_class shape pop marked
  have regions : ∀ cls v, InRegion after.stack cls v ↔ InRegion before.stack cls v := by
    intro cls v
    have eq : InRegion after.stack cls v ↔ InRegion step.prepared.stackResult.after cls v := by
      simp only [InRegion, markClass?, bucketAt?, afterMarks, afterSigma, afterReady]
    exact eq.trans (pop_region_iff shape pop cls v)
  have headClass : markClass? after.stack step.prepared.stackResult.vertex =
      some step.prepared.stackResult.rawAge := by simp [classEq, pop_class_eq shape pop]
  have mateMark : before.stack.marks[step.consumer.mate]? = some (some step.mateRawAge) := by
    rw [← step.before_invariant.realizesSigma.marks_eq]
    exact step.mate_marked_before
  have mateClass : markClass? after.stack step.consumer.mate = some step.destination.boundary := by
    apply oldClass
    unfold markClass?
    rw [mateMark]
    simpa only [PreparedStep.after, popSigma] using step.destination.boundary_eq
  have older : step.destination.boundary < step.prepared.stackResult.rawAge :=
    Nat.lt_of_le_of_lt step.destination.boundary_properties.2 step.younger
  have waiting : after.stack.waiting = before.stack.waiting.setIfInBounds
      step.destination.boundary (.initialized (step.consumer.conclusion :: payload)) := by
    rw [stackEq, waitingEq]
    change step.prepared.stackResult.after.waiting.setIfInBounds _ _ = _
    rw [popWaiting]
  have oldLookup : before.stack.waiting[step.destination.boundary]? =
      some (.initialized payload) := by
    simpa only [PreparedStep.after, popWaiting] using initialized
  have newLookup : after.stack.waiting[step.destination.boundary]? =
      some (.initialized (step.consumer.conclusion :: payload)) := by rw [stackEq]; exact updated
  have linked := ConnectiveBelow.parLinked step.consumer step.par_eq
  apply par_update_closure structural shape pop closure linked afterMarks (afterSigma.trans popSigma)
  · intro cls v region; exact (regions cls v).mpr region
  · intro cls l r _ region; exact (regions cls l).mp region
  · intro p m c cls link region
    obtain ⟨pClass, mClass⟩ := closure.down link ((regions cls c).mp region)
    exact ⟨oldClass pClass, oldClass mClass⟩
  · intro cls hClass mClass
    have hEq := Option.some.inj (headClass.symm.trans hClass)
    have mEq := Option.some.inj (mateClass.symm.trans mClass)
    exact (Nat.ne_of_gt older (hEq.trans mEq.symm)).elim
  · intro cls cls' hClass mClass _
    have hEq := Option.some.inj (headClass.symm.trans hClass)
    have mEq := Option.some.inj (mateClass.symm.trans mClass)
    subst cls; subst cls'
    rw [Nat.min_eq_right (Nat.le_of_lt older)]
    exact ⟨_, newLookup, List.mem_cons_self ..⟩
  · intro boundary oldPayload v lookup member
    by_cases same : boundary = step.destination.boundary
    · subst boundary
      have eq := Option.some.inj (oldLookup.symm.trans lookup)
      cases eq
      exact ⟨_, newLookup, List.mem_cons_of_mem _ member⟩
    · refine ⟨oldPayload, ?_, member⟩
      rw [waiting, Array.getElem?_setIfInBounds_ne (Ne.symm same)]
      exact lookup
  · intro boundary newPayload c lookup member
    have oldEntry : before.stack.waiting[boundary]? = some (.initialized newPayload) →
        ∃ p m cls cls', .par p m c ∈ certificate.links ∧
          markClass? after.stack p = some cls ∧ markClass? after.stack m = some cls' ∧
          cls ≠ cls' ∧ min cls cls' = boundary := by
      intro old
      obtain ⟨p, m, cls, cls', link, pClass, mClass, ne, eq⟩ := closure.waitingBackward old member
      exact ⟨p, m, cls, cls', link, oldClass pClass, oldClass mClass, ne, eq⟩
    by_cases same : boundary = step.destination.boundary
    · subst boundary
      have eq := Option.some.inj (newLookup.symm.trans lookup)
      cases eq
      rcases List.mem_cons.mp member with rfl | oldMember
      · rcases linked with link | link
        · exact ⟨_, _, _, _, link, headClass, mateClass, Nat.ne_of_gt older,
            Nat.min_eq_right (Nat.le_of_lt older)⟩
        · exact ⟨_, _, _, _, link, mateClass, headClass, Nat.ne_of_lt older,
            Nat.min_eq_left (Nat.le_of_lt older)⟩
      · obtain ⟨p, m, cls, cls', link, pClass, mClass, ne, eq⟩ :=
          closure.waitingBackward oldLookup oldMember
        exact ⟨p, m, cls, cls', link, oldClass pClass, oldClass mClass, ne, eq⟩
    · apply oldEntry
      rw [waiting, Array.getElem?_setIfInBounds_ne (Ne.symm same)] at lookup
      exact lookup

private theorem par_producer_classes {certificate : Certificate} {stack : SequentialStackState}
    (structural : certificate.StructurallyWellFormed) {left right conclusion cls : Nat}
    (linked : ParLinked certificate left right conclusion)
    (leftClass : markClass? stack left = some cls) (rightClass : markClass? stack right = some cls)
    {p m : Vertex} (other : TensorLinked certificate p m conclusion ∨
      ParLinked certificate p m conclusion) :
    markClass? stack p = some cls ∧ markClass? stack m = some cls := by
  rcases linked with link | link <;>
    rcases other with (other | other) | (other | other) <;>
    have eq := UnificationState.StructurallyWellFormed.producerLink_unique structural (conclusion := conclusion)
      link (by simp [Link.produces]) other (by simp [Link.produces]) <;>
    cases eq <;> first | exact ⟨leftClass, rightClass⟩ | exact ⟨rightClass, leftClass⟩

/-- Forwarding preserves region closure by adding the fired par conclusion to the active bucket. -/
theorem ForwardStep.regionClosure {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) (structural : certificate.StructurallyWellFormed)
    (closure : RegionClosure certificate before.stack) : RegionClosure certificate after.stack := by
  have shape := step.before_invariant.stack_wellShaped
  have pop := step.prepared.stack_eq
  obtain ⟨_, last, _, _, _, popSigma, _, popWaiting, _⟩ := popReadyMark?_exact pop
  have midShape := popReadyMark?_wellShaped shape pop
  have afterMarks : after.stack.marks = step.prepared.stackResult.after.marks := by
    simp only [step.output_eq, step.prependStep.after_eq]
  have afterSigma : after.stack.sigma = step.prepared.stackResult.after.sigma := by
    simp only [step.output_eq, step.prependStep.after_eq]
  have afterWaiting : after.stack.waiting = before.stack.waiting := by
    simp only [step.output_eq, step.prependStep.after_eq]
    exact popWaiting
  have classEq : ∀ v, markClass? after.stack v = markClass? step.prepared.stackResult.after v := by
    intro v; simp only [markClass?, afterMarks, afterSigma]
  have oldClass : ∀ {v cls}, markClass? before.stack v = some cls →
      markClass? after.stack v = some cls := by
    intro v cls marked; rw [classEq]; exact pop_old_class shape pop marked
  have headClass : markClass? after.stack step.prepared.stackResult.vertex =
      some step.prepared.stackResult.rawAge := by simp [classEq, pop_class_eq shape pop]
  have mateMark : step.prepared.stackResult.after.marks[step.consumer.mate]? =
      some (some step.mateRawAge) := by
    change step.prepared.after.stack.marks[step.consumer.mate]? = _
    rw [← (step.prepared.reservationInvariant step.before_invariant).realizesSigma.marks_eq]
    exact step.mate_marked
  have mateClass : markClass? after.stack step.consumer.mate =
      some step.prepared.stackResult.rawAge := by
    rw [classEq]
    unfold markClass?
    rw [mateMark, popSigma]
    exact sigmaBoundary?_of_last_le shape.sigma_partition.strictIncreasing last step.not_older
  have midLast : step.prepared.stackResult.after.sigma.getLast? =
      some step.prepared.stackResult.rawAge := by rw [popSigma]; exact last
  have readyLast : step.prepared.stackResult.after.ready.getLast? =
      some step.prependStep.activeReady := by rw [step.prependStep.ready_eq]; simp
  have midBucket := bucketAt?_last midShape.sigma_partition.strictIncreasing
    midShape.ready_aligned midLast readyLast
  have buckets : ∀ cls, bucketAt? after.stack cls =
      if cls = step.prepared.stackResult.rawAge then
        some (step.consumer.conclusion :: step.prependStep.activeReady)
      else bucketAt? step.prepared.stackResult.after cls := by
    intro cls
    have ready : after.stack.ready = step.prepared.stackResult.after.ready.dropLast ++
        [step.consumer.conclusion :: step.prependStep.activeReady] := by
      simp [step.output_eq, step.prependStep.after_eq, step.prependStep.ready_eq]
    unfold bucketAt?
    rw [afterSigma, ready]
    exact lookup_zip_replaceLast midShape.sigma_partition.strictIncreasing
      midShape.ready_aligned midLast readyLast cls
  have regions : ∀ cls v, InRegion after.stack cls v ↔
      InRegion before.stack cls v ∨
        (cls = step.prepared.stackResult.rawAge ∧ v = step.consumer.conclusion) := by
    intro cls v
    rw [← pop_region_iff shape pop cls v]
    unfold InRegion
    rw [classEq, buckets]
    by_cases active : cls = step.prepared.stackResult.rawAge
    · subst cls
      simp only [ite_true, midBucket, Option.some.injEq, true_and]
      grind
    · simp [active]
  have linked := ConnectiveBelow.parLinked step.consumer step.par_eq
  apply par_update_closure structural shape pop closure linked afterMarks (afterSigma.trans popSigma)
  · intro cls v region; exact (regions cls v).mpr (Or.inl region)
  · intro cls l r axLinked region
    rcases (regions cls l).mp region with old | ⟨_, rfl⟩
    · exact old
    · obtain ⟨name, positive, atom⟩ := axiom_endpoint_atom structural axLinked
      exact (connective_conclusion_not_atom structural (Or.inr linked) atom).elim
  · intro p m c cls link region
    rcases (regions cls c).mp region with old | ⟨rfl, rfl⟩
    · obtain ⟨pClass, mClass⟩ := closure.down link old
      exact ⟨oldClass pClass, oldClass mClass⟩
    · exact par_producer_classes structural linked headClass mateClass link
  · intro cls hClass _
    have eq := Option.some.inj (headClass.symm.trans hClass)
    exact (regions cls step.consumer.conclusion).mpr (Or.inr ⟨eq.symm, rfl⟩)
  · intro cls cls' hClass mClass different
    have hEq := Option.some.inj (headClass.symm.trans hClass)
    have mEq := Option.some.inj (mateClass.symm.trans mClass)
    exact (different (hEq.symm.trans mEq)).elim
  · intro boundary payload v lookup member
    exact ⟨payload, by rw [afterWaiting]; exact lookup, member⟩
  · intro boundary payload c lookup member
    rw [afterWaiting] at lookup
    obtain ⟨p, m, cls, cls', link, pClass, mClass, ne, eq⟩ := closure.waitingBackward lookup member
    exact ⟨p, m, cls, cls', link, oldClass pClass, oldClass mClass, ne, eq⟩

private theorem class_lt_next {stack : SequentialStackState} {size : Nat}
    (shape : stack.WellShaped size) {v : Vertex} {cls : RawTokenAge}
    (marked : markClass? stack v = some cls) : cls < stack.nextAge := by
  unfold markClass? at marked
  cases eq : stack.marks[v]? with
  | none => simp [eq] at marked
  | some mark =>
      cases mark with
      | none => simp [eq] at marked
      | some age =>
          simp only [eq] at marked
          exact Nat.lt_of_le_of_lt (sigmaBoundary?_le marked) (shape.assigned_age_bound v age eq)

private theorem lookup_zip_append_fresh {keys : List Nat} {values : List (List Vertex)}
    {fresh : Nat} {value : List Vertex} (aligned : keys.length = values.length)
    (absent : fresh ∉ keys) (query : Nat) :
    ((keys ++ [fresh]).zip (values ++ [value])).lookup query =
      if query = fresh then some value else (keys.zip values).lookup query := by
  have none : (keys.zip values).lookup fresh = none := by
    apply List.lookup_eq_none_iff.mpr
    intro pair member
    have ne : fresh ≠ pair.1 := fun eq ↦ absent (eq ▸ (List.of_mem_zip member).1)
    simpa using ne
  rw [List.zip_append aligned, List.lookup_append]
  by_cases same : query = fresh
  · subst query; simp [none]
  · have ne : (query == fresh) = false := by simp [same]
    simp [List.lookup, same, ne]

private theorem tensorLinked_of_query {certificate : Certificate} {v : Vertex} {tensor : TensorBelow}
    (query : certificate.tensorBelow? v = some tensor) :
    TensorLinked certificate v tensor.mate tensor.conclusion := by
  have member := List.mem_of_getElem? (certificate.tensorBelow?_link query)
  have premise := certificate.tensorBelow?_premise query
  rw [premise]
  cases sideEq : tensor.side <;> simp_all [TensorBelow.premise, TensorBelow.mate,
    TensorPremiseSide.premise, TensorPremiseSide.mate, TensorLinked]

private theorem tensor_mate_unique {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) {p m c m' c' : Vertex}
    (bound : p < certificate.formulas.size) (tensor : TensorLinked certificate p m c)
    (tensor' : TensorLinked certificate p m' c') : m = m' ∧ c = c' := by
  rcases tensor with tensor | tensor <;> rcases tensor' with tensor' | tensor' <;>
    have eq := premise_unique structural tensor tensor'
      (by simp [Link.premises]) (by simp [Link.premises]) bound <;>
    simp only [Link.tensor.injEq] at eq <;> grind

/-- A new reservation preserves region closure while making a fresh, unmarked axiom region active. -/
theorem NewStep.regionClosure {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) (structural : certificate.StructurallyWellFormed)
    (closure : RegionClosure certificate before.stack) : RegionClosure certificate after.stack := by
  have shape := step.before_invariant.stack_wellShaped
  have pop := step.stack_eq
  have midShape := popReadyMark?_wellShaped shape pop
  obtain ⟨_, last, _, _, _, popSigma, _, popWaiting, _⟩ := popReadyMark?_exact pop
  obtain ⟨active, activeLast, _, marksEq, _, sigmaEq, readyEq, waitingEq, updated, _⟩ :=
    operationalNewEnqueue?_exact step.stack_enqueue_eq
  have activeEq : active = step.stackResult.rawAge := by
    rw [popSigma] at activeLast
    exact Option.some.inj (activeLast.symm.trans last)
  subst active
  have stackEq : after.stack = step.stackAfter := congrArg ReservationState.stack step.output_eq
  have classEq : ∀ v, markClass? after.stack v = markClass? step.stackResult.after v := by
    intro v
    unfold markClass?
    rw [stackEq, marksEq, sigmaEq]
    cases mark : step.stackResult.after.marks[v]? with
    | none => rfl
    | some raw =>
        cases raw with
        | none => rfl
        | some age =>
            exact sigmaBoundary?_append_fresh_old (midShape.assigned_age_bound v age mark)
  have oldClass : ∀ {v cls}, markClass? before.stack v = some cls →
      markClass? after.stack v = some cls := by
    intro v cls marked; rw [classEq]; exact pop_old_class shape pop marked
  have markedEq : ∀ v, Marked after.stack v ↔ v = step.stackResult.vertex ∨ Marked before.stack v := by
    intro v
    have eq : Marked after.stack v ↔ Marked step.stackResult.after v := by
      simp only [Marked, stackEq, marksEq]
    exact eq.trans (pop_marked_iff pop v)
  have noFresh : ∀ v, markClass? after.stack v ≠ some step.stackResult.after.nextAge := by
    intro v marked
    rw [classEq] at marked
    exact Nat.lt_irrefl _ (class_lt_next midShape marked)
  have absent : step.stackResult.after.nextAge ∉ step.stackResult.after.sigma := by
    intro member
    exact Nat.lt_irrefl _ (midShape.sigma_partition.boundary_lt _ member)
  have buckets : ∀ cls, bucketAt? after.stack cls =
      if cls = step.stackResult.after.nextAge then some [step.reached, step.partner]
      else bucketAt? step.stackResult.after cls := by
    intro cls
    unfold bucketAt?
    rw [stackEq, sigmaEq, readyEq]
    exact lookup_zip_append_fresh midShape.ready_aligned.symm absent cls
  have freshNone : bucketAt? step.stackResult.after step.stackResult.after.nextAge = none := by
    unfold bucketAt?
    apply List.lookup_eq_none_iff.mpr
    intro pair member
    have ne : step.stackResult.after.nextAge ≠ pair.1 :=
      fun eq ↦ absent (eq ▸ (List.of_mem_zip member).1)
    simpa using ne
  have regions : ∀ cls v, InRegion after.stack cls v ↔ InRegion before.stack cls v ∨
      (cls = step.stackResult.after.nextAge ∧ v ∈ [step.reached, step.partner]) := by
    intro cls v
    rw [← pop_region_iff shape pop cls v]
    unfold InRegion
    rw [classEq, buckets]
    by_cases fresh : cls = step.stackResult.after.nextAge
    · subst cls
      simp only [ite_true, freshNone, Option.some.injEq, reduceCtorEq, false_and,
        exists_false, or_false, true_and]
      grind
    · simp [fresh]
  have extend : ∀ {cls v}, InRegion before.stack cls v → InRegion after.stack cls v :=
    fun {cls v} region ↦ (regions cls v).mpr (Or.inl region)
  have newAxiom := axiomLinked_of_oriented step.search step.oriented_eq
  have tensor := tensorLinked_of_query step.tensor_eq
  have bound := pop_vertex_bound shape pop
  have mateUnmarked : ¬ Marked after.stack step.tensor.mate := by
    rintro ⟨age, marked⟩
    have unmarked := step.mate_unmarked
    have markEq := step.markedMiddle_reservationInvariant.realizesSigma.marks_eq
    change step.coreMarked.marks = step.stackResult.after.marks at markEq
    rw [stackEq, marksEq, ← markEq] at marked
    rw [unmarked] at marked
    cases marked
  have parNe : ∀ {p m c}, ParLinked certificate p m c →
      p ≠ step.stackResult.vertex ∧ m ≠ step.stackResult.vertex := by
    intro p m c par
    constructor
    · rintro rfl; exact par_tensor_disjoint structural bound par tensor
    · rintro rfl; exact par_tensor_disjoint structural bound par.symm tensor
  have headClass : markClass? after.stack step.stackResult.vertex = some step.stackResult.rawAge := by
    simp [classEq, pop_class_eq shape pop]
  have beforeClass : ∀ {v cls}, v ≠ step.stackResult.vertex →
      markClass? after.stack v = some cls → markClass? before.stack v = some cls := by
    intro v cls ne marked
    simpa [classEq, pop_class_eq shape pop, ne] using marked
  have waiting : after.stack.waiting = before.stack.waiting.setIfInBounds step.stackResult.rawAge
      (.initialized []) := by rw [stackEq, waitingEq, popWaiting]
  have activeEmpty : after.stack.waiting[step.stackResult.rawAge]? = some (.initialized []) := by
    rw [stackEq]; exact updated
  have oldUndefined : before.stack.waiting[step.stackResult.rawAge]? = some .undefined := by
    obtain ⟨enqueue⟩ := operationalNewEnqueue?_some_iff.mp step.stack_enqueue_eq
    have same : enqueue.active = step.stackResult.rawAge := by
      have h := enqueue.ready.2.1
      rw [popSigma] at h
      exact Option.some.inj (h.symm.trans last)
    have h := enqueue.ready.2.2.2.2.2.2.2.2.2.2.1
    simpa only [same, popWaiting] using h
  refine {
    pairsMarked := ?_
    pairsRaw := ?_
    tensorTop := ?_
    tensorOne := ?_
    tensorFired := ?_
    parFired := ?_
    down := ?_
    waitingForward := ?_
    waitingBackward := ?_ }
  · intro l r cls linked marked
    rw [classEq] at marked
    exact extend ((pop_region_iff shape pop cls r).mp (pop_pairs_marked shape pop closure linked marked))
  · intro l r cls bucket linked lookup member
    rw [buckets] at lookup
    by_cases fresh : cls = step.stackResult.after.nextAge
    · subst cls
      simp only [ite_true, Option.some.injEq] at lookup
      subst bucket
      have bounds : ∀ v ∈ [step.reached, step.partner], v < certificate.formulas.size := by
        intro v mem
        exact step.reservationInvariant.stack_wellShaped.ready_in_bounds _
          (by rw [stackEq, readyEq]; simp) v mem
      have vBound := bounds l member
      refine Or.inl ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · rw [axiom_partner_unique structural linked newAxiom vBound]; simp
      · rw [axiom_partner_unique structural linked newAxiom.symm vBound]; simp
    · rw [if_neg fresh] at lookup
      rcases pop_pairs_raw shape pop closure linked lookup member with raw | marked
      · exact Or.inl raw
      · exact Or.inr (by rw [classEq]; exact marked)
  · intro p m c active linked top marked
    have topEq : after.stack.sigma.getLast? = some step.stackResult.after.nextAge := by
      rw [stackEq, sigmaEq]; simp
    have eq := Option.some.inj (top.symm.trans topEq)
    subst active
    exact (noFresh p marked).elim
  · intro p m c p' m' c' cls linked linked' pClass mAbsent pClass' mAbsent'
    by_cases pHead : p = step.stackResult.vertex
    · subst p
      by_cases pHead' : p' = step.stackResult.vertex
      · exact pHead'.symm
      · have eq := Option.some.inj (headClass.symm.trans pClass)
        subst cls
        have oldMate := closure.tensorTop linked' last (beforeClass pHead' pClass')
        exact (mAbsent' ((markedEq m').mpr (Or.inr oldMate))).elim
    · by_cases pHead' : p' = step.stackResult.vertex
      · subst p'
        have eq := Option.some.inj (headClass.symm.trans pClass')
        subst cls
        have oldMate := closure.tensorTop linked last (beforeClass pHead pClass)
        exact (mAbsent ((markedEq m).mpr (Or.inr oldMate))).elim
      · exact closure.tensorOne linked linked' (beforeClass pHead pClass)
          (fun old ↦ mAbsent ((markedEq m).mpr (Or.inr old))) (beforeClass pHead' pClass')
          (fun old ↦ mAbsent' ((markedEq m').mpr (Or.inr old)))
  · intro p m c cls linked pClass mMarked
    have pNe : p ≠ step.stackResult.vertex := by
      intro eq; subst p
      obtain ⟨mateEq, _⟩ := tensor_mate_unique structural bound linked tensor
      rw [mateEq] at mMarked
      exact mateUnmarked mMarked
    have mNe : m ≠ step.stackResult.vertex := by
      intro eq; subst m
      obtain ⟨mateEq, _⟩ := tensor_mate_unique structural bound linked.symm tensor
      rw [mateEq] at pClass
      exact mateUnmarked (marked_of_class pClass)
    have oldMate : Marked before.stack m := by simpa [mNe] using (markedEq m).mp mMarked
    obtain ⟨mClass, region⟩ := closure.tensorFired linked (beforeClass pNe pClass) oldMate
    exact ⟨oldClass mClass, extend region⟩
  · intro p m c cls linked pClass mClass
    exact extend (closure.parFired linked (beforeClass (parNe linked).1 pClass)
      (beforeClass (parNe linked).2 mClass))
  · intro p m c cls linked region
    rcases (regions cls c).mp region with old | ⟨_, member⟩
    · obtain ⟨pClass, mClass⟩ := closure.down linked old
      exact ⟨oldClass pClass, oldClass mClass⟩
    · have atom : ∃ name positive, certificate.formula? c = some (.atom name positive) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact axiom_endpoint_atom structural newAxiom
        · exact axiom_endpoint_atom structural newAxiom.symm
      obtain ⟨name, positive, atom⟩ := atom
      exact (connective_conclusion_not_atom structural linked atom).elim
  · intro p m c cls cls' linked pClass mClass different
    obtain ⟨payload, lookup, member⟩ := closure.waitingForward linked
      (beforeClass (parNe linked).1 pClass) (beforeClass (parNe linked).2 mClass) different
    have ne : min cls cls' ≠ step.stackResult.rawAge := by
      intro eq
      rw [eq, oldUndefined] at lookup
      cases lookup
    exact ⟨payload, by rw [waiting, Array.getElem?_setIfInBounds_ne (Ne.symm ne)]; exact lookup,
      member⟩
  · intro boundary payload c lookup member
    have ne : boundary ≠ step.stackResult.rawAge := by
      intro eq; subst boundary
      rw [activeEmpty] at lookup
      cases lookup
      cases member
    rw [waiting, Array.getElem?_setIfInBounds_ne (Ne.symm ne)] at lookup
    obtain ⟨p, m, cls, cls', link, pClass, mClass, different, eq⟩ := closure.waitingBackward lookup member
    exact ⟨p, m, cls, cls', link, oldClass pClass, oldClass mClass, different, eq⟩

private def mergedClass (active previous cls : RawTokenAge) : RawTokenAge :=
  if cls = active then previous else cls

private theorem boundary_merge {sigmaPrefix : List RawTokenAge} {previous active age : RawTokenAge}
    (increasing : (sigmaPrefix ++ [previous, active]).Pairwise (· < ·)) :
    sigmaBoundary? (sigmaPrefix ++ [previous]) age =
      (sigmaBoundary? (sigmaPrefix ++ [previous, active]) age).map (mergedClass active previous) := by
  by_cases below : age < active
  · rw [sigmaBoundary?_popActive_of_lt rfl below]
    cases lookup : sigmaBoundary? (sigmaPrefix ++ [previous, active]) age with
    | none => rfl
    | some cls =>
        have le := sigmaBoundary?_le lookup
        have ne : cls ≠ active := Nat.ne_of_lt (Nat.lt_of_le_of_lt le below)
        simp [mergedClass, ne]
  · have lower : active ≤ age := Nat.le_of_not_gt below
    have previousLt : previous < active := by
      simpa using (List.pairwise_append.mp increasing).2.1
    have reduced : (sigmaPrefix ++ [previous]).Pairwise (· < ·) := by
      have h : ((sigmaPrefix ++ [previous]) ++ [active]).Pairwise (· < ·) := by
        simpa [List.append_assoc] using increasing
      exact (List.pairwise_append.mp h).1
    rw [sigmaBoundary?_of_last_le increasing (by simp) lower,
      sigmaBoundary?_of_last_le reduced (by simp) (Nat.le_trans (Nat.le_of_lt previousLt) lower)]
    simp [mergedClass]

private theorem class_mem_sigma {stack : SequentialStackState} {v : Vertex} {cls : RawTokenAge}
    (marked : markClass? stack v = some cls) : cls ∈ stack.sigma := by
  unfold markClass? at marked
  cases eq : stack.marks[v]? with
  | none => simp [eq] at marked
  | some mark =>
      cases mark with
      | none => simp [eq] at marked
      | some age =>
          simp only [eq] at marked
          exact sigmaBoundary?_mem marked

private theorem bucket_mem_sigma {stack : SequentialStackState} {cls : RawTokenAge}
    {bucket : List Vertex} (lookup : bucketAt? stack cls = some bucket) : cls ∈ stack.sigma := by
  obtain ⟨front, back, eq, _⟩ := List.lookup_eq_some_iff.mp lookup
  apply (List.of_mem_zip (l₁ := stack.sigma) (l₂ := stack.ready) (a := cls) (b := bucket) ?_).1
  rw [eq]
  simp

private theorem merged_class_cases {previous active s t : RawTokenAge}
    (same : mergedClass active previous s = mergedClass active previous t) :
    s = t ∨ (s = previous ∧ t = active) ∨ (s = active ∧ t = previous) := by
  unfold mergedClass at same
  split at same <;> split at same <;> grind

private theorem lookup_zip_none {keys : List Nat} {values : List (List Vertex)} {key : Nat}
    (absent : key ∉ keys) : (keys.zip values).lookup key = none := by
  apply List.lookup_eq_none_iff.mpr
  intro pair member
  have ne : key ≠ pair.1 := fun eq ↦ absent (eq ▸ (List.of_mem_zip member).1)
  simpa using ne

private theorem merge_class_eq {before after : SequentialStackState} {previous c : Nat} {size : Nat}
    (shape : before.WellShaped size) (step : MergeTopReadyWaitingStep before after previous c)
    (v : Vertex) : markClass? after v =
      (markClass? before v).map (mergedClass step.activeBoundary previous) := by
  have increasing : (step.sigmaPrefix ++ [previous, step.activeBoundary]).Pairwise (· < ·) := by
    rw [← step.sigma_eq]; exact shape.sigma_partition.strictIncreasing
  unfold markClass?
  have marks : after.marks = before.marks := by
    simpa only using congrArg SequentialStackState.marks step.after_eq
  have sigma : after.sigma = step.sigmaPrefix ++ [previous] :=
    congrArg SequentialStackState.sigma step.after_eq
  rw [marks, sigma]
  cases eq : before.marks[v]? with
  | none => rfl
  | some mark =>
      cases mark with
      | none => rfl
      | some age => rw [step.sigma_eq]; exact boundary_merge increasing

private theorem merge_region_iff {before after : SequentialStackState} {previous c : Nat} {size : Nat}
    (shape : before.WellShaped size) (step : MergeTopReadyWaitingStep before after previous c)
    (cls : RawTokenAge) (v : Vertex) :
    InRegion after cls v ↔
      (∃ old, InRegion before old v ∧ mergedClass step.activeBoundary previous old = cls) ∨
        (cls = previous ∧ (v = c ∨ v ∈ step.payload)) := by
  have increasing : (step.sigmaPrefix ++ [previous, step.activeBoundary]).Pairwise (· < ·) := by
    rw [← step.sigma_eq]; exact shape.sigma_partition.strictIncreasing
  have lt : previous < step.activeBoundary := by
    simpa using (List.pairwise_append.mp increasing).2.1
  have below : ∀ q ∈ step.sigmaPrefix, q < previous := by
    intro q member
    exact (List.pairwise_append.mp increasing).2.2 q member previous (by simp)
  have previousAbsent : previous ∉ step.sigmaPrefix := fun member ↦ Nat.lt_irrefl _ (below _ member)
  have activeAbsent : step.activeBoundary ∉ step.sigmaPrefix := by
    intro member
    exact Nat.lt_asymm lt (below _ member)
  have aligned : step.sigmaPrefix.length = step.readyPrefix.length := by
    have h := shape.ready_aligned
    rw [step.sigma_eq, step.ready_eq] at h
    simpa using h.symm
  have oldBuckets : ∀ q, bucketAt? before q =
      if q = step.activeBoundary then some step.activeReady
      else if q = previous then some step.previousReady
      else (step.sigmaPrefix.zip step.readyPrefix).lookup q := by
    intro q
    unfold bucketAt?
    rw [step.sigma_eq, step.ready_eq]
    have keyEq : step.sigmaPrefix ++ [previous, step.activeBoundary] =
        (step.sigmaPrefix ++ [previous]) ++ [step.activeBoundary] := by simp
    have valueEq : step.readyPrefix ++ [step.previousReady, step.activeReady] =
        (step.readyPrefix ++ [step.previousReady]) ++ [step.activeReady] := by simp
    rw [keyEq, valueEq, lookup_zip_append_fresh (by simp [aligned])
      (by simp [activeAbsent, Nat.ne_of_gt lt]), lookup_zip_append_fresh aligned previousAbsent]
  have newBuckets : ∀ q, bucketAt? after q =
      if q = previous then some (c :: (step.payload ++ step.previousReady ++ step.activeReady))
      else (step.sigmaPrefix.zip step.readyPrefix).lookup q := by
    intro q
    have sigma := congrArg SequentialStackState.sigma step.after_eq
    have ready := congrArg SequentialStackState.ready step.after_eq
    unfold bucketAt?
    rw [sigma, ready]
    exact lookup_zip_append_fresh aligned previousAbsent q
  have noActive : (step.sigmaPrefix.zip step.readyPrefix).lookup step.activeBoundary = none :=
    lookup_zip_none activeAbsent
  have moveMarked : ∀ {old}, markClass? before v = some old →
      markClass? after v = some (mergedClass step.activeBoundary previous old) := by
    intro old marked
    rw [merge_class_eq shape step, marked]
    rfl
  constructor
  · rintro (marked | ⟨bucket, lookup, member⟩)
    · rw [merge_class_eq shape step] at marked
      cases oldEq : markClass? before v with
      | none => simp [oldEq] at marked
      | some old =>
          simp only [oldEq, Option.map_some, Option.some.injEq] at marked
          exact Or.inl ⟨old, Or.inl oldEq, marked⟩
    · rw [newBuckets] at lookup
      by_cases current : cls = previous
      · subst cls
        simp only [ite_true, Option.some.injEq] at lookup
        subst bucket
        rcases List.mem_cons.mp member with created | member
        · exact Or.inr ⟨rfl, Or.inl created⟩
        · rcases List.mem_append.mp member with left | active
          · rcases List.mem_append.mp left with payload | previousMem
            · exact Or.inr ⟨rfl, Or.inr payload⟩
            · exact Or.inl ⟨previous, Or.inr ⟨_, by simp [oldBuckets, Nat.ne_of_lt lt], previousMem⟩,
                by simp [mergedClass, Nat.ne_of_lt lt]⟩
          · exact Or.inl ⟨step.activeBoundary, Or.inr ⟨_, by simp [oldBuckets], active⟩,
              by simp [mergedClass]⟩
      · rw [if_neg current] at lookup
        have ne : cls ≠ step.activeBoundary := by
          intro eq; subst cls; rw [noActive] at lookup; cases lookup
        exact Or.inl ⟨cls, Or.inr ⟨_, by simpa [oldBuckets, ne, current] using lookup, member⟩,
          by simp [mergedClass, ne]⟩
  · rintro (⟨old, marked | ⟨bucket, lookup, member⟩, rfl⟩ | ⟨rfl, created | payload⟩)
    · exact Or.inl (moveMarked marked)
    · rw [oldBuckets] at lookup
      by_cases active : old = step.activeBoundary
      · subst old
        simp only [ite_true, Option.some.injEq] at lookup
        subst bucket
        refine Or.inr ⟨c :: (step.payload ++ step.previousReady ++ step.activeReady), ?_, ?_⟩
        · simp [newBuckets, mergedClass]
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ member)
      · rw [if_neg active] at lookup
        by_cases prev : old = previous
        · subst old
          simp only [ite_true, Option.some.injEq] at lookup
          subst bucket
          refine Or.inr ⟨c :: (step.payload ++ step.previousReady ++ step.activeReady), ?_, ?_⟩
          · simp [newBuckets, mergedClass, active]
          · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ member))
        · rw [if_neg prev] at lookup
          exact Or.inr ⟨_, by simpa [newBuckets, mergedClass, active, prev] using lookup, member⟩
    · subst v
      exact Or.inr ⟨c :: (step.payload ++ step.previousReady ++ step.activeReady), by simp [newBuckets], List.mem_cons_self ..⟩
    · exact Or.inr ⟨c :: (step.payload ++ step.previousReady ++ step.activeReady), by simp [newBuckets], List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_append_left _ payload))⟩

private theorem merge_min_eq {a p s t : Nat} (lt : p < a)
    (sDom : s ≤ p ∨ s = a) (tDom : t ≤ p ∨ t = a) (different : s ≠ t)
    (eq : min s t = p) : mergedClass a p s = p ∧ mergedClass a p t = p := by
  by_cases sa : s = a <;> by_cases ta : t = a <;>
    simp only [mergedClass, sa, ta, ite_true, ite_false] <;> grind

private theorem merge_min_ne {a p s t : Nat} (lt : p < a)
    (sDom : s ≤ p ∨ s = a) (tDom : t ≤ p ∨ t = a) (different : s ≠ t)
    (ne : min s t ≠ p) :
    mergedClass a p s ≠ mergedClass a p t ∧
      min (mergedClass a p s) (mergedClass a p t) = min s t := by
  by_cases sa : s = a <;> by_cases ta : t = a <;>
    simp only [mergedClass, sa, ta, ite_true, ite_false] <;> grind

private theorem tensor_producer_classes {certificate : Certificate} {stack : SequentialStackState}
    (structural : certificate.StructurallyWellFormed) {left right conclusion cls : Nat}
    (linked : TensorLinked certificate left right conclusion)
    (leftClass : markClass? stack left = some cls) (rightClass : markClass? stack right = some cls)
    {p m : Vertex} (other : TensorLinked certificate p m conclusion ∨
      ParLinked certificate p m conclusion) :
    markClass? stack p = some cls ∧ markClass? stack m = some cls := by
  rcases linked with link | link <;>
    rcases other with (other | other) | (other | other) <;>
    have eq := UnificationState.StructurallyWellFormed.producerLink_unique structural
      (conclusion := conclusion) link (by simp [Link.produces]) other (by simp [Link.produces]) <;>
    cases eq <;> first | exact ⟨leftClass, rightClass⟩ | exact ⟨rightClass, leftClass⟩

/-- Payload unification preserves region closure when the adjacent classes and waiting payload merge. -/
theorem UnifyPayloadStep.regionClosure {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) (structural : certificate.StructurallyWellFormed)
    (closure : RegionClosure certificate before.stack) : RegionClosure certificate after.stack := by
  have shape := step.before_invariant.stack_wellShaped
  have pop := step.prepared.stack_eq
  have midShape := popReadyMark?_wellShaped shape pop
  obtain ⟨_, last, headUnmarked, _, _, popSigma, _, popWaiting, _⟩ := popReadyMark?_exact pop
  have stackEq : after.stack = step.stackAfter := congrArg ReservationState.stack step.output_eq
  have oldSigma : before.stack.sigma =
      step.mergeStep.sigmaPrefix ++ [step.previousBoundary, step.mergeStep.activeBoundary] :=
    popSigma.symm.trans step.mergeStep.sigma_eq
  have activeEq : step.mergeStep.activeBoundary = step.prepared.stackResult.rawAge := by
    rw [oldSigma] at last
    simpa using last
  have increasing : (step.mergeStep.sigmaPrefix ++
      [step.previousBoundary, step.mergeStep.activeBoundary]).Pairwise (· < ·) := by
    rw [← oldSigma]; exact shape.sigma_partition.strictIncreasing
  have lt : step.previousBoundary < step.mergeStep.activeBoundary := by
    simpa using (List.pairwise_append.mp increasing).2.1
  let collapse := mergedClass step.mergeStep.activeBoundary step.previousBoundary
  have collapseActive : collapse step.mergeStep.activeBoundary = step.previousBoundary := by
    simp [collapse, mergedClass]
  have collapsePrevious : collapse step.previousBoundary = step.previousBoundary := by
    simp [collapse, mergedClass, Nat.ne_of_lt lt]
  have classEq : ∀ v, markClass? after.stack v =
      (markClass? step.prepared.stackResult.after v).map collapse := by
    intro v
    rw [stackEq]
    exact merge_class_eq midShape step.mergeStep v
  have oldClass : ∀ {v cls}, markClass? before.stack v = some cls →
      markClass? after.stack v = some (collapse cls) := by
    intro v cls marked
    rw [classEq, pop_old_class shape pop marked]
    rfl
  have headClass : markClass? after.stack step.prepared.stackResult.vertex =
      some step.previousBoundary := by
    simp [classEq, pop_class_eq shape pop, collapse, ← activeEq, mergedClass]
  have newClass : ∀ {v cls}, markClass? after.stack v = some cls →
      (v = step.prepared.stackResult.vertex ∧ cls = step.previousBoundary) ∨
        ∃ old, markClass? before.stack v = some old ∧ collapse old = cls := by
    intro v cls marked
    by_cases head : v = step.prepared.stackResult.vertex
    · subst v
      exact Or.inl ⟨rfl, (Option.some.inj (headClass.symm.trans marked)).symm⟩
    · rw [classEq, pop_class_eq shape pop, if_neg head] at marked
      cases old : markClass? before.stack v with
      | none => simp [old] at marked
      | some oldCls =>
          simp only [old, Option.map_some, Option.some.injEq] at marked
          exact Or.inr ⟨oldCls, rfl, marked⟩
  have markedEq : ∀ v, Marked after.stack v ↔
      v = step.prepared.stackResult.vertex ∨ Marked before.stack v := by
    intro v
    have marks : after.stack.marks = step.prepared.stackResult.after.marks := by
      simp only [stackEq, step.mergeStep.after_eq]
    rw [Marked, marks]
    exact pop_marked_iff pop v
  have regions : ∀ cls v, InRegion after.stack cls v ↔
      (∃ old, InRegion before.stack old v ∧ collapse old = cls) ∨
        (cls = step.previousBoundary ∧ (v = step.consumer.conclusion ∨ v ∈ step.mergeStep.payload)) := by
    intro cls v
    rw [stackEq]
    simpa only [pop_region_iff shape pop] using merge_region_iff midShape step.mergeStep cls v
  have extend : ∀ {cls v}, InRegion before.stack cls v → InRegion after.stack (collapse cls) v := by
    intro cls v region
    exact (regions (collapse cls) v).mpr (Or.inl ⟨cls, region, rfl⟩)
  have created : InRegion after.stack step.previousBoundary step.consumer.conclusion :=
    (regions _ _).mpr (Or.inr ⟨rfl, Or.inl rfl⟩)
  have fromPayload : ∀ {v}, v ∈ step.mergeStep.payload → InRegion after.stack step.previousBoundary v :=
    fun member ↦ (regions _ _).mpr (Or.inr ⟨rfl, Or.inr member⟩)
  have domain : ∀ {cls}, cls ∈ before.stack.sigma →
      cls ≤ step.previousBoundary ∨ cls = step.mergeStep.activeBoundary := by
    intro cls member
    rw [oldSigma] at member
    rcases List.mem_append.mp member with member | member
    · exact Or.inl (Nat.le_of_lt ((List.pairwise_append.mp increasing).2.2 cls member _ (by simp)))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | eq
      · exact Or.inl (Nat.le_refl _)
      · exact Or.inr eq
  have markedDomain : ∀ {v cls}, markClass? before.stack v = some cls →
      cls ≤ step.previousBoundary ∨ cls = step.mergeStep.activeBoundary :=
    fun marked ↦ domain (class_mem_sigma marked)
  have tensor := tensorLinked_of_query step.consumer_eq
  have bound := pop_vertex_bound shape pop
  have mateOld : markClass? before.stack step.consumer.mate = some step.previousBoundary := by
    have marked := step.mate_marked_before
    rw [step.before_invariant.realizesSigma.marks_eq] at marked
    unfold markClass?
    rw [marked]
    exact shape.sigma_partition.sigmaBoundary?_eq_previous_of_between oldSigma step.lower
      (by rw [activeEq]; exact step.upper)
  have mateClass : markClass? after.stack step.consumer.mate = some step.previousBoundary := by
    simpa only [collapsePrevious] using oldClass mateOld
  have headAbsent : ¬ Marked before.stack step.prepared.stackResult.vertex := by
    rintro ⟨age, marked⟩; rw [headUnmarked] at marked; cases marked
  have parNe : ∀ {p m c}, ParLinked certificate p m c →
      p ≠ step.prepared.stackResult.vertex ∧ m ≠ step.prepared.stackResult.vertex := by
    intro p m c par
    constructor
    · rintro rfl; exact par_tensor_disjoint structural bound par tensor
    · rintro rfl; exact par_tensor_disjoint structural bound par.symm tensor
  have parOld : ∀ {p m c cls}, ParLinked certificate p m c →
      markClass? after.stack p = some cls → ∃ old, markClass? before.stack p = some old ∧ collapse old = cls := by
    intro p m c cls par marked
    rcases newClass marked with ⟨eq, _⟩ | old
    · exact ((parNe par).1 eq).elim
    · exact old
  have waiting : after.stack.waiting = before.stack.waiting.setIfInBounds step.previousBoundary
      .undefined := by simp only [stackEq, step.mergeStep.after_eq, popWaiting]
  have payloadLookup : before.stack.waiting[step.previousBoundary]? =
      some (.initialized step.mergeStep.payload) := by
    simpa only [popWaiting] using step.mergeStep.waiting_initialized
  have payloadClasses : ∀ {c}, c ∈ step.mergeStep.payload →
      ∃ p m, ParLinked certificate p m c ∧
        markClass? after.stack p = some step.previousBoundary ∧
        markClass? after.stack m = some step.previousBoundary := by
    intro c member
    obtain ⟨p, m, s, t, link, pClass, mClass, different, eq⟩ := closure.waitingBackward payloadLookup member
    have both := merge_min_eq lt (markedDomain pClass) (markedDomain mClass) different eq
    exact ⟨p, m, Or.inl link, by simpa only [collapse, both.1] using oldClass pClass,
      by simpa only [collapse, both.2] using oldClass mClass⟩
  have activeTensor : ∀ {p m c}, TensorLinked certificate p m c →
      markClass? after.stack p = some step.previousBoundary → Marked after.stack m := by
    intro p m c linked marked
    by_cases oldMarked : Marked before.stack m
    · exact (markedEq m).mpr (Or.inr oldMarked)
    · rcases newClass marked with ⟨rfl, _⟩ | ⟨old, pClass, eq⟩
      · obtain ⟨mateEq, _⟩ := tensor_mate_unique structural bound linked tensor
        rw [mateEq]
        exact marked_of_class mateClass
      · have cases : old = step.previousBoundary ∨ old = step.mergeStep.activeBoundary := by
          have h := merged_class_cases (eq.trans collapsePrevious.symm)
          rcases h with h | ⟨h, _⟩ | ⟨h, _⟩
          · exact Or.inl h
          · exact Or.inl h
          · exact Or.inr h
        rcases cases with rfl | rfl
        · have premiseEq := closure.tensorOne linked tensor.symm pClass oldMarked mateOld headAbsent
          subst p
          have mateBound := (marked_of_class mateOld)
          have consumerBound : step.consumer.mate < certificate.formulas.size := by
            obtain ⟨age, raw⟩ := mateBound
            have rawBound := (Array.getElem?_eq_some_iff.mp raw).1
            rw [shape.marks_size] at rawBound
            exact rawBound
          obtain ⟨mateEq, _⟩ := tensor_mate_unique structural consumerBound linked tensor.symm
          rw [mateEq]
          exact marked_of_class headClass
        · have oldMate := closure.tensorTop linked last (by simpa only [activeEq] using pClass)
          exact (oldMarked oldMate).elim
  refine {
    pairsMarked := ?_
    pairsRaw := ?_
    tensorTop := ?_
    tensorOne := ?_
    tensorFired := ?_
    parFired := ?_
    down := ?_
    waitingForward := ?_
    waitingBackward := ?_ }
  · intro l r cls linked marked
    rcases (regions cls l).mp (Or.inl marked) with ⟨old, region, eq⟩ | ⟨_, createdOrPayload⟩
    · rw [← eq]; exact extend (axiom_region closure linked region)
    · obtain ⟨name, positive, atom⟩ := axiom_endpoint_atom structural linked
      rcases createdOrPayload with rfl | member
      · exact (connective_conclusion_not_atom structural (Or.inl tensor) atom).elim
      · obtain ⟨p, m, par, _⟩ := payloadClasses member
        exact (connective_conclusion_not_atom structural (Or.inr par) atom).elim
  · intro l r cls bucket linked lookup member
    have region : InRegion after.stack cls r := by
      rcases (regions cls l).mp (Or.inr ⟨_, lookup, member⟩) with ⟨old, region, eq⟩ | ⟨_, other⟩
      · rw [← eq]; exact extend (axiom_region closure linked region)
      · obtain ⟨name, positive, atom⟩ := axiom_endpoint_atom structural linked
        rcases other with rfl | member
        · exact (connective_conclusion_not_atom structural (Or.inl tensor) atom).elim
        · obtain ⟨p, m, par, _⟩ := payloadClasses member
          exact (connective_conclusion_not_atom structural (Or.inr par) atom).elim
    rcases region with marked | ⟨bucket', lookup', member'⟩
    · exact Or.inr marked
    · have eq := Option.some.inj (lookup'.symm.trans lookup)
      subst bucket'; exact Or.inl member'
  · intro p m c active linked top marked
    have topEq : after.stack.sigma.getLast? = some step.previousBoundary := by
      simp [stackEq, step.mergeStep.after_eq]
    have eq := Option.some.inj (top.symm.trans topEq)
    subst active; exact activeTensor linked marked
  · intro p m c p' m' c' cls linked linked' pClass absent pClass' absent'
    have notPrevious : cls ≠ step.previousBoundary := by
      rintro rfl; exact absent (activeTensor linked pClass)
    obtain ⟨old, pOld, eq⟩ := (newClass pClass).resolve_left (fun h ↦ notPrevious h.2)
    obtain ⟨old', pOld', eq'⟩ := (newClass pClass').resolve_left (fun h ↦ notPrevious h.2)
    have oldEq : old = old' := by
      rcases merged_class_cases (eq.trans eq'.symm) with same | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact same
      · exact (notPrevious (eq.symm.trans collapsePrevious)).elim
      · exact (notPrevious (eq.symm.trans collapseActive)).elim
    subst old'
    exact closure.tensorOne linked linked' pOld
      (fun h ↦ absent ((markedEq m).mpr (Or.inr h))) pOld'
      (fun h ↦ absent' ((markedEq m').mpr (Or.inr h)))
  · intro p m c cls linked pClass mMarked
    by_cases pHead : p = step.prepared.stackResult.vertex
    · subst p
      obtain ⟨rfl, rfl⟩ := tensor_mate_unique structural bound linked tensor
      have eq := Option.some.inj (headClass.symm.trans pClass)
      subst cls; exact ⟨mateClass, created⟩
    · by_cases mHead : m = step.prepared.stackResult.vertex
      · subst m
        obtain ⟨rfl, rfl⟩ := tensor_mate_unique structural bound linked.symm tensor
        have eq := Option.some.inj (mateClass.symm.trans pClass)
        subst cls; exact ⟨headClass, created⟩
      · obtain ⟨old, pOld, eq⟩ := (newClass pClass).resolve_left (fun h ↦ pHead h.1)
        have oldMarked : Marked before.stack m := ((markedEq m).mp mMarked).resolve_left mHead
        obtain ⟨mOld, region⟩ := closure.tensorFired linked pOld oldMarked
        rw [← eq]; exact ⟨oldClass mOld, extend region⟩
  · intro p m c cls linked pClass mClass
    obtain ⟨s, pOld, eq⟩ := parOld linked pClass
    obtain ⟨t, mOld, eq'⟩ := parOld linked.symm mClass
    by_cases same : s = t
    · subst t
      rw [← eq]; exact extend (closure.parFired linked pOld mOld)
    · have minEq : min s t = step.previousBoundary := by
        rcases merged_class_cases (eq.trans eq'.symm) with equal | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (same equal).elim
        · exact Nat.min_eq_left (Nat.le_of_lt lt)
        · exact Nat.min_eq_right (Nat.le_of_lt lt)
      obtain ⟨payload, lookup, member⟩ := closure.waitingForward linked pOld mOld same
      rw [minEq] at lookup
      have payloadEq := Option.some.inj (lookup.symm.trans payloadLookup)
      cases payloadEq
      have both := merge_min_eq lt (markedDomain pOld) (markedDomain mOld) same minEq
      have clsEq : cls = step.previousBoundary := eq.symm.trans both.1
      rw [clsEq]; exact fromPayload member
  · intro p m c cls linked region
    rcases (regions cls c).mp region with ⟨old, oldRegion, eq⟩ | ⟨rfl, createdOrPayload⟩
    · obtain ⟨pOld, mOld⟩ := closure.down linked oldRegion
      rw [← eq]; exact ⟨oldClass pOld, oldClass mOld⟩
    · rcases createdOrPayload with rfl | member
      · exact tensor_producer_classes structural tensor headClass mateClass linked
      · obtain ⟨p', m', par, pClass, mClass⟩ := payloadClasses member
        exact par_producer_classes structural par pClass mClass linked
  · intro p m c cls cls' linked pClass mClass different
    obtain ⟨s, pOld, eq⟩ := parOld linked pClass
    obtain ⟨t, mOld, eq'⟩ := parOld linked.symm mClass
    have oldDifferent : s ≠ t := by rintro rfl; exact different (eq.symm.trans eq')
    have ne : min s t ≠ step.previousBoundary := by
      intro minEq
      have both := merge_min_eq lt (markedDomain pOld) (markedDomain mOld) oldDifferent minEq
      exact different (eq.symm.trans (both.1.trans (both.2.symm.trans eq')))
    have minEq := (merge_min_ne lt (markedDomain pOld) (markedDomain mOld) oldDifferent ne).2
    obtain ⟨payload, lookup, member⟩ := closure.waitingForward linked pOld mOld oldDifferent
    refine ⟨payload, ?_, member⟩
    rw [← eq, ← eq', minEq, waiting, Array.getElem?_setIfInBounds_ne (Ne.symm ne)]
    exact lookup
  · intro boundary payload c lookup member
    have ne : boundary ≠ step.previousBoundary := by
      intro eq; subst boundary
      rw [waiting, Array.getElem?_setIfInBounds_self,
        if_pos ((Array.getElem?_eq_some_iff.mp payloadLookup).1)] at lookup
      cases lookup
    rw [waiting, Array.getElem?_setIfInBounds_ne (Ne.symm ne)] at lookup
    obtain ⟨p, m, s, t, link, pClass, mClass, different, minEq⟩ := closure.waitingBackward lookup member
    have facts := merge_min_ne lt (markedDomain pClass) (markedDomain mClass) different
      (fun eq ↦ ne (minEq.symm.trans eq))
    exact ⟨p, m, collapse s, collapse t, link, oldClass pClass, oldClass mClass,
      facts.1, facts.2.trans minEq⟩

private theorem empty_region_closure (certificate : Certificate) :
    RegionClosure certificate (ReservationState.empty certificate).stack := by
  have noClass : ∀ {v cls}, markClass? (ReservationState.empty certificate).stack v ≠ some cls := by
    intro v cls
    by_cases bound : v < certificate.formulas.size <;>
      simp [markClass?, ReservationState.empty, SequentialStackState.empty, bound]
  have noBucket : ∀ {cls bucket}, bucketAt? (ReservationState.empty certificate).stack cls ≠
      some bucket := by intro cls bucket; simp [bucketAt?, ReservationState.empty, SequentialStackState.empty]
  refine {
    pairsMarked := fun _ marked ↦ (noClass marked).elim
    pairsRaw := fun _ lookup _ ↦ (noBucket lookup).elim
    tensorTop := fun _ _ marked ↦ (noClass marked).elim
    tensorOne := fun _ _ marked _ _ _ ↦ (noClass marked).elim
    tensorFired := fun _ marked _ ↦ (noClass marked).elim
    parFired := fun _ marked _ ↦ (noClass marked).elim
    down := ?_
    waitingForward := fun _ marked _ _ ↦ (noClass marked).elim
    waitingBackward := ?_ }
  · rintro p m c cls _ (marked | ⟨bucket, lookup, _⟩)
    · exact (noClass marked).elim
    · exact (noBucket lookup).elim
  · intro boundary payload c lookup _
    by_cases bound : boundary < certificate.formulas.size <;>
      simp [ReservationState.empty, SequentialStackState.empty, bound] at lookup

/-- Every exact canonical dispatcher success preserves region closure. -/
theorem DispatchStep.regionClosure {certificate : Certificate} {before : ReservationState}
    {invariant : SchedulerInvariant certificate before} {result : Figure7DispatchResult}
    (step : DispatchStep certificate before invariant result)
    (closure : RegionClosure certificate before.stack) : RegionClosure certificate result.after.stack := by
  obtain ⟨evidence⟩ := step.tagEvidence
  cases evidence with
  | concl typed => exact typed.regionClosure invariant.structural closure
  | nop typed => exact typed.regionClosure invariant.structural closure
  | new typed => exact typed.regionClosure invariant.structural closure
  | wait typed => exact typed.regionClosure invariant.structural closure
  | forward typed => exact typed.regionClosure invariant.structural closure
  | unifyPayload typed => exact typed.regionClosure invariant.structural closure

/-- Region closure holds at the endpoint of every executed history of a structurally valid certificate. -/
theorem ExecutedHistory.regionClosure {certificate : Certificate} {state : ReservationState}
    (history : ExecutedHistory certificate state) (structural : certificate.StructurallyWellFormed) :
    RegionClosure certificate state.stack := by
  induction history with
  | empty => exact empty_region_closure certificate
  | init step => exact RegionClosure.ofInitialReservation step structural
  | later history invariant step ih => exact step.regionClosure ih

/-- Every dispatcher-reachable stack of a structurally valid certificate is region closed. -/
theorem ReachableByImplementedDispatcher.regionClosure
    {certificate : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate state)
    (structural : certificate.StructurallyWellFormed) : RegionClosure certificate state.stack := by
  obtain ⟨history⟩ := reachable
  exact history.regionClosure structural

/-- Correctness gives C12 at every dispatcher-reachable state. -/
theorem ReachableByImplementedDispatcher.guardedHeadTail
    {certificate : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate state)
    (correct : certificate.DeclarativelyCorrect) : ParHeadGuardTailNonconclusion certificate state :=
  (reachable.regionClosure correct.1).guardedParHeadTail (reachable.schedulerInvariant correct.1) correct

/-- A nop or wait extension of a canonical prefix adds no remaining tail-law obligation. -/
theorem CanonicalTagHistory.nopWaitTailLaw_iff
    {certificate : Certificate} {before : ReservationState} {result : Figure7DispatchResult}
    {history : ExecutedHistory certificate before} {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant result}
    (prior : CanonicalTagHistory certificate history) (evidence : DispatchTagEvidence certificate before result)
    (correct : certificate.DeclarativelyCorrect) (kind : result.kind = .nop ∨ result.kind = .wait) :
    (CanonicalTagHistory.later (dispatch := dispatch) prior evidence).ActiveTopDebtTailLaw ↔
      prior.ActiveTopDebtTailLaw := by
  have guard : ParHeadGuardTailNonconclusion certificate before :=
    ReachableByImplementedDispatcher.guardedHeadTail ⟨history⟩ correct
  cases evidence with
  | concl step => simp at kind
  | new step => simp at kind
  | forward step => simp at kind
  | unifyPayload step => simp at kind
  | nop step =>
      change (_ ∧ prior.ActiveTopDebtTailLaw) ↔ prior.ActiveTopDebtTailLaw
      exact ⟨And.right, fun law ↦ ⟨step.tailNonconclusion_of_parHeadGuard guard, law⟩⟩
  | wait step =>
      change (_ ∧ prior.ActiveTopDebtTailLaw) ↔ prior.ActiveTopDebtTailLaw
      exact ⟨And.right, fun law ↦ ⟨step.tailNonconclusion_of_parHeadGuard guard, law⟩⟩

/-
The remaining created-head goals, for a canonical prefix ending at `before`,
with `correct : certificate.DeclarativelyCorrect`, are exactly:

  (step : ForwardStep certificate before after) ⊢
    step.consumer.conclusion ∉ certificate.conclusions ∨
      (ActiveTopMarkedNonconclusionPresent certificate after →
        ∃ pending, pending ∈ step.prependStep.activeReady ∧
          pending ∉ certificate.conclusions)

  (step : UnifyPayloadStep certificate before after) ⊢
    step.consumer.conclusion ∉ certificate.conclusions ∨
      (ActiveTopMarkedNonconclusionPresent certificate after →
        ∃ pending, pending ∈ step.mergeStep.payload ++ step.mergeStep.previousReady ++
          step.mergeStep.activeReady ∧ pending ∉ certificate.conclusions)
-/


/-! ## Draining

When the active bucket is empty, the active region has no boundary edge at
all, so switching connectedness makes the active class the whole net. -/

/-- With an empty active bucket and one vertex of the active class, every
in-bounds vertex is marked in the active class. -/
theorem RegionClosure.class_of_empty_active {certificate : Certificate} {state : ReservationState}
    (closure : RegionClosure certificate state.stack)
    (invariant : SchedulerInvariant certificate state)
    (correct : certificate.DeclarativelyCorrect) {age : RawTokenAge}
    (sigmaLast : state.stack.sigma.getLast? = some age)
    (readyLast : state.stack.ready.getLast? = some [])
    {seed : Vertex} (seedClass : markClass? state.stack seed = some age)
    (seedBound : seed < certificate.formulas.size)
    {vertex : Vertex} (bound : vertex < certificate.formulas.size) :
    markClass? state.stack vertex = some age := by
  by_cases inside : markClass? state.stack vertex = some age
  · exact inside
  exfalso
  have structural := correct.1
  have bucketEq : bucketAt? state.stack age = some [] :=
    bucketAt?_last invariant.stack_wellShaped.sigma_partition.strictIncreasing
      invariant.stack_wellShaped.ready_aligned sigmaLast readyLast
  have seedInside : activeInside state.stack age [] seed = true :=
    activeInside_iff.mpr (Or.inl seedClass)
  have vertexOutside : activeInside state.stack age [] vertex = false := by
    rw [Bool.eq_false_iff, Ne, activeInside_iff]
    rintro (marked | member)
    · exact inside marked
    · simp at member
  obtain ⟨u, v, uIn, vOut, adjacent⟩ :=
    boundary_edge_of_correct correct (activeInside state.stack age []) seedBound bound
      seedInside vertexOutside
  have uIn' : markClass? state.stack u = some age := by
    rcases activeInside_iff.mp uIn with marked | member
    · exact marked
    · simp at member
  have vOut' : ¬ markClass? state.stack v = some age := by
    intro h
    have := (activeInside_iff (bucket := [])).mpr (Or.inl h)
    rw [vOut] at this
    exact Bool.false_ne_true this
  have ofRegion : ∀ {w : Vertex}, InRegion state.stack age w → markClass? state.stack w = some age := by
    rintro w (marked | ⟨bucket, lookup, member⟩)
    · exact marked
    · rw [bucketEq] at lookup
      cases lookup
      simp at member
  obtain ⟨edge, edgeMember, orientation⟩ := adjacent
  rcases List.mem_append.mp edgeMember with fixed | selected
  · rcases mem_fixedEdges fixed with ⟨l, r, member, rfl⟩ | ⟨l, r, c, member, edgeEq⟩
    · have linked : AxiomLinked certificate u v := by
        rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl member
        · exact Or.inr member
      exact vOut' (ofRegion (closure.pairsMarked linked uIn'))
    · have premiseCase : ∀ {premise mate : Vertex}, TensorLinked certificate premise mate c →
          u = premise → v = c → False := by
        intro premise mate linked uEq vEq
        subst uEq; subst vEq
        have mateMarked := closure.tensorTop linked sigmaLast uIn'
        exact vOut' (ofRegion (closure.tensorFired linked uIn' mateMarked).2)
      have conclusionCase : ∀ {premise mate : Vertex}, TensorLinked certificate premise mate c →
          u = c → v = premise → False := by
        intro premise mate linked uEq vEq
        subst uEq; subst vEq
        exact vOut' (closure.down (Or.inl linked) (Or.inl uIn')).1
      rcases edgeEq with rfl | rfl
      · rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact premiseCase (Or.inl member) rfl rfl
        · exact conclusionCase (Or.inl member) rfl rfl
      · rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact premiseCase (Or.inr member) rfl rfl
        · exact conclusionCase (Or.inr member) rfl rfl
  · obtain ⟨l, r, c, member, edgeEq⟩ := mem_cutSelection selected
    have conclusionCase : ∀ {premise mate : Vertex}, ParLinked certificate premise mate c →
        u = c → v = premise → False := by
      intro premise mate linked uEq vEq
      subst uEq; subst vEq
      exact vOut' (closure.down (Or.inr linked) (Or.inl uIn')).1
    unfold cutChoice at edgeEq
    simp only at edgeEq
    split at edgeEq
    · rename_i cond
      rw [Bool.and_eq_true, Bool.not_eq_true'] at cond
      subst edgeEq
      rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [uIn] at cond
        exact Bool.false_ne_true cond.2.symm
      · exact conclusionCase (Or.inr member) rfl rfl
    · split at edgeEq
      · rename_i cond
        rw [Bool.and_eq_true, Bool.not_eq_true'] at cond
        subst edgeEq
        rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [uIn] at cond
          exact Bool.false_ne_true cond.2.symm
        · exact conclusionCase (Or.inl member) rfl rfl
      · rename_i notFirst _
        subst edgeEq
        rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have rIn : activeInside state.stack age [] r = true := by
            cases rIn : activeInside state.stack age [] r
            · exact absurd (by rw [uIn, rIn]; rfl) notFirst
            · rfl
          have rClass : markClass? state.stack r = some age := by
            rcases activeInside_iff.mp rIn with marked | member
            · exact marked
            · simp at member
          exact vOut' (ofRegion (closure.parFired (Or.inl member) uIn' rClass))
        · exact conclusionCase (Or.inl member) rfl rfl


private theorem owned_ne_nil {certificate : Certificate} {tree : CutFreeDerivation}
    {frontier usedLinks owned : List Nat}
    (witness : Certificate.OccurrenceDerivation certificate tree frontier usedLinks owned) :
    owned ≠ [] := by
  induction witness <;> simp_all

/-- A started drained state has an empty active bucket and a vertex marked in
the active class: the seed of the connectivity argument. -/
private theorem seed_of_drained {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state) (drained : ActiveTopDrained state) :
    ∃ age seed, state.stack.sigma.getLast? = some age ∧
      state.stack.ready.getLast? = some [] ∧
      markClass? state.stack seed = some age ∧ seed < certificate.formulas.size := by
  obtain ⟨age, component, sigmaLast, componentLookup, frontierMarked⟩ := drained
  have shape := invariant.stack_wellShaped
  have marksEq : state.core.marks = state.stack.marks := invariant.realizesSigma.marks_eq
  -- the last bucket is exactly the raw-unmarked frontier, hence empty
  have sigmaIndex : state.stack.sigma[state.stack.sigma.length - 1]? = some age := by
    rw [← List.getLast?_eq_getElem?]; exact sigmaLast
  have readyLength : state.stack.ready.length - 1 = state.stack.sigma.length - 1 := by
    rw [shape.ready_aligned]
  have readyLast : state.stack.ready.getLast? = some [] := by
    rw [List.getLast?_eq_getElem?, readyLength]
    cases readyIndex : state.stack.ready[state.stack.sigma.length - 1]? with
    | none =>
        exfalso
        obtain ⟨sigmaPos, _⟩ := List.getElem?_eq_some_iff.mp sigmaIndex
        have := List.getElem?_eq_none_iff.mp readyIndex
        rw [shape.ready_aligned] at this
        omega
    | some bucket =>
        obtain ⟨component', componentLookup', exact⟩ :=
          invariant.ready_bucket_frontier_exact sigmaIndex readyIndex
        rw [componentLookup] at componentLookup'
        cases componentLookup'
        congr
        cases bucket with
        | nil => rfl
        | cons head rest =>
            exfalso
            have := (exact head).mp (List.mem_cons_self ..)
            exact frontierMarked head this.1 this.2
  -- a marked owned occurrence of the active component
  obtain ⟨usedAt, ownedAt, live, _, _⟩ := invariant.component_forest_provenance
  obtain ⟨witness, accounted⟩ := live componentLookup
  have ownedNonempty : ownedAt age ≠ [] := owned_ne_nil witness.derivation
  cases ownedEq : ownedAt age with
  | nil => exact (ownedNonempty ownedEq).elim
  | cons seed _ =>
      have seedOwned : seed ∈ ownedAt age := by rw [ownedEq]; simp
      rcases accounted seed seedOwned with ⟨raw, marked, representative⟩ | ⟨unmarked, frontier⟩
      · have rawBound : raw < state.stack.nextAge := by
          apply shape.assigned_age_bound seed raw
          rw [← marksEq]; exact marked
        have seedBound : seed < certificate.formulas.size := by
          have := (Array.getElem?_eq_some_iff.mp marked).1
          rwa [invariant.core_abstractable.markArraySize] at this
        refine ⟨age, seed, sigmaLast, readyLast, ?_, seedBound⟩
        unfold markClass?
        rw [← marksEq, marked]
        show sigmaBoundary? state.stack.sigma raw = some age
        rw [invariant.realizesSigma.representative_eq_boundary rawBound, representative]
      · exact (frontierMarked seed frontier unmarked).elim

/-- A drained, dispatcher-reachable state of a correct certificate has every
occurrence marked: the active class is the whole net. -/
theorem ReachableByImplementedDispatcher.allMarked_of_drained
    {certificate : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate state)
    (correct : certificate.DeclarativelyCorrect)
    (drained : ActiveTopDrained state) : state.core.allMarked = true := by
  have invariant := reachable.schedulerInvariant correct.1
  have closure := reachable.regionClosure correct.1
  obtain ⟨age, seed, sigmaLast, readyLast, seedClass, seedBound⟩ :=
    seed_of_drained invariant drained
  have marksEq : state.core.marks = state.stack.marks := invariant.realizesSigma.marks_eq
  unfold UnificationState.allMarked
  rw [Array.all_eq_true]
  intro vertex bound
  have bound' : vertex < certificate.formulas.size := by
    rwa [invariant.core_abstractable.markArraySize] at bound
  have marked : Marked state.stack vertex :=
    marked_of_class (closure.class_of_empty_active invariant correct sigmaLast readyLast
      seedClass seedBound bound')
  obtain ⟨raw, lookup⟩ := marked
  have : state.core.marks[vertex]? = some (some raw) := by rw [marksEq]; exact lookup
  rw [Array.getElem?_eq_getElem bound] at this
  rw [Option.some.inj this]
  rfl

/-- Figure-7 progress: a started reachable state of a correct certificate
either dispatches or is completely marked. -/
theorem ReachableByImplementedDispatcher.dispatch_or_allMarked
    {certificate : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate state)
    (correct : certificate.DeclarativelyCorrect) (started : 0 < state.stack.nextAge) :
    let invariant := reachable.schedulerInvariant correct.1
    (∃ result : Figure7DispatchResult, dispatch? certificate state invariant = some result) ∨
      state.core.allMarked = true := by
  intro invariant
  rcases reachable.dispatch_or_activeTopDrained correct started with dispatch | drained
  · exact Or.inl dispatch
  · exact Or.inr (reachable.allMarked_of_drained correct drained)

/-- The ledger form of Figure-7 progress, over the exact canonical history. -/
theorem CanonicalTagHistory.dispatch_or_allMarked
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (_tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect) (started : 0 < state.stack.nextAge) :
    let invariant := history.schedulerInvariant correct.1
    (∃ result : Figure7DispatchResult, dispatch? certificate state invariant = some result) ∨
      state.core.allMarked = true :=
  ReachableByImplementedDispatcher.dispatch_or_allMarked ⟨history⟩ correct started

end SequentialFigure7
end ProofNetIR
