import ProofNetIR.SequentialUnification

namespace ProofNetIR

/-!
# Oriented `NEXTAXIOM` source routes

`NextAxiomResult.left` and `.right` retain the submitted orientation of the
returned axiom.  They therefore do not, by themselves, identify which endpoint
the recursive search reached.  This module exposes that missing orientation
without changing the executable result type.
-/

namespace SequentialUnification

/-- Recover search-oriented axiom endpoints from a successful result.

The stored `left/right` fields retain submitted-link orientation.  The last
recursive trace vertex determines which of them was actually reached. -/
def NextAxiomResult.orientedEndpoints?
    {certificate : Certificate} {state : UnificationState} {fuel : Nat}
    {inputTags : Array Bool}
    (result : NextAxiomResult certificate state fuel inputTags) :
    Option (Vertex × Vertex) := do
  let reached ← result.trace.getLast?
  if reached = result.left then
    some (reached, result.right)
  else if reached = result.right then
    some (reached, result.left)
  else
    none

/-- One recursive `NEXTAXIOM` step: from the conclusion of an exact submitted
tensor or par link to that link's stored left premise. -/
inductive SourceLeftStep (certificate : Certificate) : Vertex → Vertex → Prop
  | tensor
      {linkIndex : Nat} {left right conclusion : Vertex}
      (exactLink :
        certificate.links[linkIndex]? =
          some (.tensor left right conclusion)) :
      SourceLeftStep certificate conclusion left
  | par
      {linkIndex : Nat} {left right conclusion : Vertex}
      (exactLink :
        certificate.links[linkIndex]? =
          some (.par left right conclusion)) :
      SourceLeftStep certificate conclusion left

/-- Reflexive-transitive reachability along exact submitted source-left
steps.  Reflexivity covers a call whose starting vertex is already an axiom
endpoint. -/
inductive SourceLeftReachable (certificate : Certificate) :
    Vertex → Vertex → Prop
  | refl (vertex : Vertex) :
      SourceLeftReachable certificate vertex vertex
  | step
      {source next target : Vertex}
      (head : SourceLeftStep certificate source next)
      (tail : SourceLeftReachable certificate next target) :
      SourceLeftReachable certificate source target

/-- Every exact source-left step strictly decreases formula complexity on a
structurally well-formed certificate. -/
theorem SourceLeftStep.formulaComplexity_lt
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {source next : Vertex}
    (step : SourceLeftStep certificate source next) :
    certificate.formulaComplexityAt next <
      certificate.formulaComplexityAt source := by
  cases step with
  | tensor exactLink =>
      have membership := List.mem_of_getElem? exactLink
      have wellFormed := structural.2.2.2.2.1 _ membership
      simpa [Certificate.linkConclusionComplexity] using
        wellFormed.premise_complexity_lt_conclusion
          (premise := _) (by simp [Link.premises])
  | par exactLink =>
      have membership := List.mem_of_getElem? exactLink
      have wellFormed := structural.2.2.2.2.1 _ membership
      simpa [Certificate.linkConclusionComplexity] using
        wellFormed.premise_complexity_lt_conclusion
          (premise := _) (by simp [Link.premises])

/-- Source-left reachability weakly decreases formula complexity, with the
reflexive case accounting for equality. -/
theorem SourceLeftReachable.formulaComplexity_le
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {source target : Vertex}
    (reachable : SourceLeftReachable certificate source target) :
    certificate.formulaComplexityAt target ≤
      certificate.formulaComplexityAt source := by
  induction reachable with
  | refl => exact Nat.le_refl _
  | step head tail induction =>
      exact Nat.le_trans induction
        (Nat.le_of_lt (head.formulaComplexity_lt structural))

/-- A source-left route is either reflexive or has an exact final source-left
step after a shorter prefix.  This endpoint-oriented view avoids reversing the
inductive route representation in downstream geometry arguments. -/
theorem SourceLeftReachable.eq_or_exists_lastStep
    {certificate : Certificate}
    {source target : Vertex}
    (reachable : SourceLeftReachable certificate source target) :
    source = target ∨
      ∃ previous,
        SourceLeftReachable certificate source previous ∧
          SourceLeftStep certificate previous target := by
  induction reachable with
  | refl => exact Or.inl rfl
  | @step source next target head tail induction =>
      rcases induction with same | ⟨previous, pathPrefix, last⟩
      · subst target
        exact Or.inr ⟨source, .refl source, head⟩
      · exact Or.inr ⟨previous, .step head pathPrefix, last⟩

/-- A list records precisely a (possibly empty-step) source-left route. -/
inductive SourceLeftChain (certificate : Certificate) : List Vertex → Prop
  | singleton (vertex : Vertex) :
      SourceLeftChain certificate [vertex]
  | cons
      {source next : Vertex} {tail : List Vertex}
      (head : SourceLeftStep certificate source next)
      (rest : SourceLeftChain certificate (next :: tail)) :
      SourceLeftChain certificate (source :: next :: tail)

/-- Prepend one exact source-left step to a nonempty recorded route. -/
theorem SourceLeftChain.cons_of_head
    {certificate : Certificate} {source next : Vertex}
    {trace : List Vertex}
    (step : SourceLeftStep certificate source next)
    (chain : SourceLeftChain certificate trace)
    (head : trace.head? = some next) :
    SourceLeftChain certificate (source :: trace) := by
  cases trace with
  | nil =>
      simp at head
  | cons actual tail =>
      simp only [List.head?_cons, Option.some.injEq] at head
      subst actual
      exact .cons step chain

/-- A recorded chain with named endpoints is sound for source-left
reachability. -/
theorem SourceLeftChain.reachable_of_head_last
    {certificate : Certificate} {trace : List Vertex}
    {source target : Vertex}
    (chain : SourceLeftChain certificate trace)
    (head : trace.head? = some source)
    (last : trace.getLast? = some target) :
    SourceLeftReachable certificate source target := by
  induction chain generalizing source target with
  | singleton vertex =>
      simp only [List.head?_cons, Option.some.injEq] at head
      simp only [List.getLast?_singleton, Option.some.injEq] at last
      subst source
      subst target
      exact .refl vertex
  | @cons current next tail step rest induction =>
      simp only [List.head?_cons, Option.some.injEq] at head
      subst source
      have restHead : (next :: tail).head? = some next := by
        simp
      have restLast : (next :: tail).getLast? = some target := by
        simpa [List.getLast?_cons_of_ne_nil (by simp :
          next :: tail ≠ [])] using last
      exact .step step (induction restHead restLast)

/-- The oriented semantic content of a successful bounded `NEXTAXIOM` call.

`reached` is the final vertex actually visited by the recursive search;
`partner` is the other endpoint of the submitted axiom.  The disjunction in
`exactAxiom` is intentional: the submitted link keeps its own stored
orientation, independently of the search orientation. -/
structure NextAxiomRoute
    {certificate : Certificate} {state : UnificationState} {fuel : Nat}
    {inputTags : Array Bool}
    (start : Vertex)
    (result : NextAxiomResult certificate state fuel inputTags)
    (reached partner : Vertex) : Prop where
  traceNonempty : result.trace ≠ []
  traceHead : result.trace.head? = some start
  traceLast : result.trace.getLast? = some reached
  chain : SourceLeftChain certificate result.trace
  reachable : SourceLeftReachable certificate start reached
  exactAxiom :
    certificate.links[result.linkIndex]? =
        some (.axiom reached partner) ∨
      certificate.links[result.linkIndex]? =
        some (.axiom partner reached)
  storedEndpoints :
    (reached = result.left ∧ partner = result.right) ∨
      (reached = result.right ∧ partner = result.left)

/-- An exact route proves that the executable endpoint extractor returns the
actual search orientation. -/
theorem NextAxiomRoute.orientedEndpoints?_eq
    {certificate : Certificate} {state : UnificationState} {fuel : Nat}
    {inputTags : Array Bool} {start reached partner : Vertex}
    {result : NextAxiomResult certificate state fuel inputTags}
    (route : NextAxiomRoute start result reached partner) :
    result.orientedEndpoints? = some (reached, partner) := by
  unfold NextAxiomResult.orientedEndpoints?
  rw [route.traceLast]
  rcases route.storedEndpoints with
    ⟨reachedEq, partnerEq⟩ | ⟨reachedEq, partnerEq⟩
  · subst reached
    subst partner
    simp
  · subst reached
    subst partner
    by_cases same : result.right = result.left
    · simp [same]
    · simp [same]

/-- A successful bounded `NEXTAXIOM` computation determines the actual
reached axiom endpoint and the exact source-left route to it. -/
theorem nextAxiomWithFuel?_route
    {certificate : Certificate} {state : UnificationState}
    {index : SourceIndex} {fuel : Nat} {tags : Array Bool}
    {indexSound : SourceIndex.Sound certificate index}
    {start : Vertex}
    {result : NextAxiomResult certificate state fuel tags}
    (equation :
      nextAxiomWithFuel? certificate state index indexSound fuel tags start =
        some result) :
    ∃ reached partner, NextAxiomRoute start result reached partner := by
  induction fuel generalizing tags start with
  | zero =>
      simp [nextAxiomWithFuel?] at equation
  | succ fuel induction =>
      simp only [nextAxiomWithFuel?] at equation
      repeat
        first
        | split at equation
        | contradiction
      all_goals simp at equation
      case h_1.isTrue.isTrue.isTrue.isTrue.isTrue.isTrue =>
        rename_i vertexTag vertexReady source sourceLookup left right
          linkEquation different atEndpoint leftTag rightTag leftReady
          rightReady
        have sourceMembership :
            source ∈ (index[start]?).getD [] := by
          simp [sourceLookup]
        have exactStored :
            certificate.links[source.linkIndex]? =
              some (.axiom left right) := by
          simpa [linkEquation] using (indexSound sourceMembership).1
        subst result
        rcases atEndpoint with startEq | startEq
        · refine ⟨start, right, ?_⟩
          exact {
            traceNonempty := by simp
            traceHead := by simp
            traceLast := by simp
            chain := .singleton start
            reachable := .refl start
            exactAxiom := .inl (by simpa [startEq] using exactStored)
            storedEndpoints := .inl ⟨startEq, rfl⟩
          }
        · refine ⟨start, left, ?_⟩
          exact {
            traceNonempty := by simp
            traceHead := by simp
            traceLast := by simp
            chain := .singleton start
            reachable := .refl start
            exactAxiom := .inr (by simpa [startEq] using exactStored)
            storedEndpoints := .inr ⟨startEq, rfl⟩
          }
      case h_2 =>
        rename_i vertexTag vertexReady source sourceLookup left right
          conclusion linkEquation
        rcases equation with ⟨produced, equation⟩
        split at equation
        · simp at equation
        · rename_i recursiveResult recursiveEquation
          simp at equation
          have sourceMembership :
              source ∈ (index[start]?).getD [] := by
            simp [sourceLookup]
          have exactStored :
              certificate.links[source.linkIndex]? =
                some (.tensor left right conclusion) := by
            simpa [linkEquation] using (indexSound sourceMembership).1
          have sourceStep :
              SourceLeftStep certificate start left := by
            simpa [produced] using
              (SourceLeftStep.tensor exactStored)
          rcases induction recursiveEquation with
            ⟨reached, partner, recursiveRoute⟩
          subst result
          refine ⟨reached, partner, ?_⟩
          exact {
            traceNonempty := by simp
            traceHead := by simp
            traceLast := by
              simpa [List.getLast?_cons_of_ne_nil
                recursiveRoute.traceNonempty] using
                  recursiveRoute.traceLast
            chain :=
              SourceLeftChain.cons_of_head sourceStep
                recursiveRoute.chain recursiveRoute.traceHead
            reachable :=
              .step sourceStep recursiveRoute.reachable
            exactAxiom := recursiveRoute.exactAxiom
            storedEndpoints := recursiveRoute.storedEndpoints
          }
      case h_3 =>
        rename_i vertexTag vertexReady source sourceLookup left right
          conclusion linkEquation
        rcases equation with ⟨produced, equation⟩
        split at equation
        · simp at equation
        · rename_i recursiveResult recursiveEquation
          simp at equation
          have sourceMembership :
              source ∈ (index[start]?).getD [] := by
            simp [sourceLookup]
          have exactStored :
              certificate.links[source.linkIndex]? =
                some (.par left right conclusion) := by
            simpa [linkEquation] using (indexSound sourceMembership).1
          have sourceStep :
              SourceLeftStep certificate start left := by
            simpa [produced] using
              (SourceLeftStep.par exactStored)
          rcases induction recursiveEquation with
            ⟨reached, partner, recursiveRoute⟩
          subst result
          refine ⟨reached, partner, ?_⟩
          exact {
            traceNonempty := by simp
            traceHead := by simp
            traceLast := by
              simpa [List.getLast?_cons_of_ne_nil
                recursiveRoute.traceNonempty] using
                  recursiveRoute.traceLast
            chain :=
              SourceLeftChain.cons_of_head sourceStep
                recursiveRoute.chain recursiveRoute.traceHead
            reachable :=
              .step sourceStep recursiveRoute.reachable
            exactAxiom := recursiveRoute.exactAxiom
            storedEndpoints := recursiveRoute.storedEndpoints
          }

/-- Production-wrapper form of `nextAxiomWithFuel?_route`. -/
theorem nextAxiom?_route
    {certificate : Certificate} {state : UnificationState}
    {index : SourceIndex} {tags : Array Bool}
    {indexSound : SourceIndex.Sound certificate index}
    {start : Vertex}
    {result :
      NextAxiomResult certificate state certificate.formulas.size tags}
    (equation :
      nextAxiom? certificate state index indexSound tags start =
        some result) :
    ∃ reached partner, NextAxiomRoute start result reached partner := by
  exact nextAxiomWithFuel?_route (by
    simpa [nextAxiom?] using equation)

end SequentialUnification

end ProofNetIR
