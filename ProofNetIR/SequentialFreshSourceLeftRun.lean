import ProofNetIR.SequentialSchedulerBridge

namespace ProofNetIR

/-!
# Exact fresh source-left runs

`FreshSourceLeftRun` is a fuel-indexed, proof-relevant, input-only account of
one successful call to `SequentialUnification.nextAxiomWithFuel?` over the
production `sourceIndex`.  Its four constructors mirror the executable
branches exactly: either endpoint of a submitted axiom terminates the run,
while submitted tensor and par producers recurse through their stored left
premise after tagging the current conclusion.

The production marking state is fixed throughout a run.  Every visited
occurrence and both terminal endpoints must be false in the tag carrier seen
at that exact recursive call and must have raw mark `none`.  This module says
nothing about multiple scheduler calls, Figure-7 history reachability,
later-call totality, dispatcher progress, or worklist completeness.
-/

namespace SequentialUnification

/-- One exact proof-relevant execution path through the production source
index. Source-bucket and submitted-link equations retain exact occurrence and
link-slot identity. Structural well-formedness is deliberately not an index:
the executable is defined for every certificate, while scheduler guards carry
well-formedness separately where it is semantically required. -/
inductive FreshSourceLeftRun
    (certificate : Certificate)
    (state : UnificationState) :
    Nat → Array Bool → Vertex → List Vertex → Vertex → Vertex →
      Nat → Type
  | axiomLeft
      {fuel : Nat} {tags : Array Bool} {linkIndex : Nat}
      {left right : Vertex}
      (source : SourceIncidence)
      (sourceLookup :
        (sourceIndex certificate)[left]? = some [source])
      (sourceLinkIndex : source.linkIndex = linkIndex)
      (sourceLink : source.link = .axiom left right)
      (exactLink :
        certificate.links[linkIndex]? = some (.axiom left right))
      (different : left ≠ right)
      (leftFresh : tags[left]? = some false)
      (rightFresh : tags[right]? = some false)
      (leftReady : state.marks[left]? = some none)
      (rightReady : state.marks[right]? = some none) :
      FreshSourceLeftRun certificate state (fuel + 1) tags left
        [left] left right linkIndex
  | axiomRight
      {fuel : Nat} {tags : Array Bool} {linkIndex : Nat}
      {left right : Vertex}
      (source : SourceIncidence)
      (sourceLookup :
        (sourceIndex certificate)[right]? = some [source])
      (sourceLinkIndex : source.linkIndex = linkIndex)
      (sourceLink : source.link = .axiom left right)
      (exactLink :
        certificate.links[linkIndex]? = some (.axiom left right))
      (different : left ≠ right)
      (leftFresh : tags[left]? = some false)
      (rightFresh : tags[right]? = some false)
      (leftReady : state.marks[left]? = some none)
      (rightReady : state.marks[right]? = some none) :
      FreshSourceLeftRun certificate state (fuel + 1) tags right
        [right] right left linkIndex
  | tensor
      {fuel : Nat} {tags : Array Bool}
      {producerIndex linkIndex : Nat}
      {left right conclusion reached partner : Vertex}
      {trace : List Vertex}
      (source : SourceIncidence)
      (sourceLookup :
        (sourceIndex certificate)[conclusion]? = some [source])
      (sourceLinkIndex : source.linkIndex = producerIndex)
      (sourceLink : source.link = .tensor left right conclusion)
      (exactLink :
        certificate.links[producerIndex]? =
          some (.tensor left right conclusion))
      (currentFresh : tags[conclusion]? = some false)
      (currentReady : state.marks[conclusion]? = some none)
      (tail :
        FreshSourceLeftRun certificate state fuel
          (nextAxiomSetTag tags conclusion) left trace reached partner
          linkIndex) :
      FreshSourceLeftRun certificate state (fuel + 1) tags
        conclusion (conclusion :: trace) reached partner linkIndex
  | par
      {fuel : Nat} {tags : Array Bool}
      {producerIndex linkIndex : Nat}
      {left right conclusion reached partner : Vertex}
      {trace : List Vertex}
      (source : SourceIncidence)
      (sourceLookup :
        (sourceIndex certificate)[conclusion]? = some [source])
      (sourceLinkIndex : source.linkIndex = producerIndex)
      (sourceLink : source.link = .par left right conclusion)
      (exactLink :
        certificate.links[producerIndex]? =
          some (.par left right conclusion))
      (currentFresh : tags[conclusion]? = some false)
      (currentReady : state.marks[conclusion]? = some none)
      (tail :
        FreshSourceLeftRun certificate state fuel
          (nextAxiomSetTag tags conclusion) left trace reached partner
          linkIndex) :
      FreshSourceLeftRun certificate state (fuel + 1) tags
        conclusion (conclusion :: trace) reached partner linkIndex

namespace FreshSourceLeftRun

private theorem setIfInBounds_false_reflection
    {tags : Array Bool} {tagged vertex : Vertex}
    (outputFalse :
      (tags.setIfInBounds tagged true)[vertex]? = some false) :
    tags[vertex]? = some false ∧ vertex ≠ tagged := by
  by_cases same : tagged = vertex
  · subst vertex
    simp [Array.getElem?_setIfInBounds_self] at outputFalse
  · exact ⟨by simpa [same] using outputFalse,
      fun reverse ↦ same reverse.symm⟩

/-- Every exact run records a nonempty recursive trace. -/
theorem traceNonempty
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate state fuel tags start
      trace reached partner linkIndex) :
    trace ≠ [] := by
  cases run <;> simp

/-- The terminal partner is false in the original input tag carrier. -/
theorem partnerFresh
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate state fuel tags start
      trace reached partner linkIndex) :
    tags[partner]? = some false := by
  induction run with
  | axiomLeft _ _ _ _ _ _ _ rightFresh _ _ => exact rightFresh
  | axiomRight _ _ _ _ _ _ leftFresh _ _ _ => exact leftFresh
  | tensor _ _ _ _ _ _ _ _ induction =>
      exact (setIfInBounds_false_reflection (by
        simpa [nextAxiomSetTag_eq] using induction)).1
  | par _ _ _ _ _ _ _ _ induction =>
      exact (setIfInBounds_false_reflection (by
        simpa [nextAxiomSetTag_eq] using induction)).1

/-- The terminal partner never appears among the recursively visited
occurrences.  In recursive cases the current occurrence has already been set
to `true`, while the tail still requires the partner to be `false`. -/
theorem partner_not_mem_trace
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate state fuel tags start
      trace reached partner linkIndex) :
    partner ∉ trace := by
  induction run with
  | axiomLeft _ _ _ _ _ different _ _ _ _ => simp [different.symm]
  | axiomRight _ _ _ _ _ different _ _ _ _ => simp [different]
  | tensor _ _ _ _ _ _ _ tail induction =>
      simp only [List.mem_cons, not_or]
      refine ⟨?_, induction⟩
      exact (setIfInBounds_false_reflection (by
        simpa [nextAxiomSetTag_eq] using tail.partnerFresh)).2
  | par _ _ _ _ _ _ _ tail induction =>
      simp only [List.mem_cons, not_or]
      refine ⟨?_, induction⟩
      exact (setIfInBounds_false_reflection (by
        simpa [nextAxiomSetTag_eq] using tail.partnerFresh)).2

/-- Exact submitted storage orientation and production readiness of the
terminal axiom reached by a run.  This is intentionally proof-relevant so a
later reservation bridge can select the corresponding executable branch
without re-inducting over the recursive source-left run. -/
inductive TerminalAxiom
    (certificate : Certificate) (state : UnificationState)
    (reached partner : Vertex) (linkIndex : Nat) : Type
  | reachedLeft
      (exactLink :
        certificate.links[linkIndex]? =
          some (.axiom reached partner))
      (different : reached ≠ partner)
      (reachedReady : state.marks[reached]? = some none)
      (partnerReady : state.marks[partner]? = some none) :
      TerminalAxiom certificate state reached partner linkIndex
  | reachedRight
      (exactLink :
        certificate.links[linkIndex]? =
          some (.axiom partner reached))
      (different : reached ≠ partner)
      (reachedReady : state.marks[reached]? = some none)
      (partnerReady : state.marks[partner]? = some none) :
      TerminalAxiom certificate state reached partner linkIndex

/-- A run exposes its exact terminal submitted axiom, storage orientation,
distinct endpoints, and both endpoint readiness facts. -/
def terminalAxiom
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate state fuel tags start
      trace reached partner linkIndex) :
    TerminalAxiom certificate state reached partner linkIndex :=
  match run with
  | .axiomLeft _ _ _ _ exactLink different _ _ leftReady rightReady =>
      .reachedLeft exactLink different leftReady rightReady
  | .axiomRight _ _ _ _ exactLink different _ _ leftReady rightReady =>
      .reachedRight exactLink different.symm rightReady leftReady
  | .tensor _ _ _ _ _ _ _ tail => terminalAxiom tail
  | .par _ _ _ _ _ _ _ tail => terminalAxiom tail

/-- The terminal submitted axiom has the run's reached/partner orientation,
up to its exact stored left/right orientation. -/
theorem exactAxiom
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate state fuel tags start
      trace reached partner linkIndex) :
    certificate.links[linkIndex]? = some (.axiom reached partner) ∨
      certificate.links[linkIndex]? = some (.axiom partner reached) := by
  cases run.terminalAxiom with
  | reachedLeft exactLink => exact Or.inl exactLink
  | reachedRight exactLink => exact Or.inr exactLink

/-- The reached endpoint is unmarked in the run's fixed production state. -/
theorem reachedReady
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate state fuel tags start
      trace reached partner linkIndex) :
    state.marks[reached]? = some none := by
  cases run.terminalAxiom with
  | reachedLeft _ _ ready _ => exact ready
  | reachedRight _ _ ready _ => exact ready

/-- The partner endpoint is unmarked in the run's fixed production state. -/
theorem partnerReady
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate state fuel tags start
      trace reached partner linkIndex) :
    state.marks[partner]? = some none := by
  cases run.terminalAxiom with
  | reachedLeft _ _ _ ready => exact ready
  | reachedRight _ _ _ ready => exact ready

/-- Exact terminal data plus structural local well-formedness and production
carrier alignment suffice to reserve the submitted axiom slot. -/
theorem TerminalAxiom.exists_reserveAxiomAt
    {certificate : Certificate} {state : UnificationState}
    {reached partner : Vertex} {linkIndex : Nat}
    (terminal : TerminalAxiom certificate state reached partner linkIndex)
    (structural : certificate.StructurallyWellFormed)
    (carriersAligned : state.components.size = state.parents.size) :
    ∃ after,
      certificate.reserveAxiomAt? state linkIndex = some after := by
  cases terminal with
  | reachedLeft exactLink different reachedReady partnerReady =>
      have membership :
          Link.axiom reached partner ∈ certificate.links :=
        List.mem_of_getElem? exactLink
      have wellFormed :
          certificate.LinkWellFormed (.axiom reached partner) :=
        structural.2.2.2.2.1 _ membership
      have localWellFormed :
          certificate.linkLocallyWellFormed (.axiom reached partner) = true :=
        (certificate.linkLocallyWellFormed_iff _).mpr wellFormed
      rcases wellFormed.axiom_endpointFormula (Or.inl rfl) with
        ⟨name, positive, leftFormula⟩
      simp [Certificate.reserveAxiomAt?, exactLink,
        Certificate.AxiomReservationReady, localWellFormed, reachedReady,
        partnerReady, carriersAligned,
        Certificate.UnificationComponent.axiom?,
        leftFormula]
  | reachedRight exactLink different reachedReady partnerReady =>
      have membership :
          Link.axiom partner reached ∈ certificate.links :=
        List.mem_of_getElem? exactLink
      have wellFormed :
          certificate.LinkWellFormed (.axiom partner reached) :=
        structural.2.2.2.2.1 _ membership
      have localWellFormed :
          certificate.linkLocallyWellFormed (.axiom partner reached) = true :=
        (certificate.linkLocallyWellFormed_iff _).mpr wellFormed
      rcases wellFormed.axiom_endpointFormula (Or.inl rfl) with
        ⟨name, positive, leftFormula⟩
      simp [Certificate.reserveAxiomAt?, exactLink,
        Certificate.AxiomReservationReady, localWellFormed, reachedReady,
        partnerReady, carriersAligned,
        Certificate.UnificationComponent.axiom?,
        leftFormula]

/-- Exact executable success data for a named trace, oriented terminal pair,
and submitted axiom-link slot. -/
def FreshSourceLeftExecution
    (certificate : Certificate) (state : UnificationState)
    (fuel : Nat) (tags : Array Bool) (start : Vertex)
    (trace : List Vertex) (reached partner : Vertex)
    (linkIndex : Nat) : Prop :=
  ∃ result,
    nextAxiomWithFuel? certificate state (sourceIndex certificate)
        (sourceIndex_sound certificate) fuel tags start = some result ∧
      result.trace = trace ∧
      result.linkIndex = linkIndex ∧
      result.orientedEndpoints? = some (reached, partner)

set_option maxHeartbeats 800000 in
/-- Every exact input-only run replays as the production executable search. -/
theorem execution
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate state fuel tags start
      trace reached partner linkIndex) :
    FreshSourceLeftExecution certificate state fuel tags start trace reached
      partner linkIndex := by
  induction run with
  | axiomLeft source sourceLookup sourceLinkIndex sourceLink exactLink
      different leftFresh rightFresh leftReady rightReady =>
      rcases source with ⟨actualIndex, actualLink⟩
      simp only at sourceLinkIndex sourceLink sourceLookup
      subst actualLink
      subst actualIndex
      simp only [FreshSourceLeftExecution, nextAxiomWithFuel?]
      repeat
        first
        | split
        | contradiction
      all_goals
        subst_vars
        simp_all [NextAxiomResult.orientedEndpoints?]
      all_goals simp_all
  | axiomRight source sourceLookup sourceLinkIndex sourceLink exactLink
      different leftFresh rightFresh leftReady rightReady =>
      rcases source with ⟨actualIndex, actualLink⟩
      simp only at sourceLinkIndex sourceLink sourceLookup
      subst actualLink
      subst actualIndex
      simp only [FreshSourceLeftExecution, nextAxiomWithFuel?]
      repeat
        first
        | split
        | contradiction
      all_goals
        subst_vars
        simp_all [NextAxiomResult.orientedEndpoints?]
      all_goals simp_all
  | tensor source sourceLookup sourceLinkIndex sourceLink exactLink
      currentFresh currentReady tail induction =>
      rcases source with ⟨actualIndex, actualLink⟩
      simp only at sourceLinkIndex sourceLink sourceLookup
      subst actualLink
      subst actualIndex
      rcases induction with
        ⟨result, recursiveEquation, traceEquation, linkEquation,
          orientedEquation⟩
      simp only [FreshSourceLeftExecution, nextAxiomWithFuel?]
      repeat
        first
        | split
        | contradiction
      all_goals
        subst_vars
        simp_all [NextAxiomResult.orientedEndpoints?,
          List.getLast?_cons_of_ne_nil tail.traceNonempty]
      case h_1.isTrue.isTrue.isTrue.isTrue.isTrue.isTrue =>
        have conflict := congrArg SourceIncidence.link sourceLookup
        simp_all
  | par source sourceLookup sourceLinkIndex sourceLink exactLink
      currentFresh currentReady tail induction =>
      rcases source with ⟨actualIndex, actualLink⟩
      simp only at sourceLinkIndex sourceLink sourceLookup
      subst actualLink
      subst actualIndex
      rcases induction with
        ⟨result, recursiveEquation, traceEquation, linkEquation,
          orientedEquation⟩
      simp only [FreshSourceLeftExecution, nextAxiomWithFuel?]
      repeat
        first
        | split
        | contradiction
      all_goals
        subst_vars
        simp_all [NextAxiomResult.orientedEndpoints?,
          List.getLast?_cons_of_ne_nil tail.traceNonempty]
      case h_1.isTrue.isTrue.isTrue.isTrue.isTrue.isTrue =>
        have conflict := congrArg SourceIncidence.link sourceLookup
        simp_all

/-- Exact production execution reconstructs the corresponding proof-relevant
run by structural recursion on the supplied fuel. -/
theorem ofExecution
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (exactExecution :
      FreshSourceLeftExecution certificate state fuel tags start trace reached
        partner linkIndex) :
    Nonempty
      (FreshSourceLeftRun certificate state fuel tags start trace
        reached partner linkIndex) := by
  rcases exactExecution with
    ⟨result, equation, traceEquation, resultLinkEquation,
      orientedEquation⟩
  induction fuel generalizing tags start trace reached partner linkIndex with
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
          sourceLink different atEndpoint leftTag rightTag leftReady
          rightReady
        have sourceMembership :
            source ∈ ((sourceIndex certificate)[start]?).getD [] := by
          simp [sourceLookup]
        have exactStored :
            certificate.links[source.linkIndex]? =
              some (.axiom left right) := by
          simpa [sourceLink] using
            (sourceIndex_sound certificate sourceMembership).1
        subst result
        subst trace
        subst linkIndex
        rcases atEndpoint with startEquation | startEquation
        · subst start
          simp [NextAxiomResult.orientedEndpoints?] at orientedEquation
          rcases orientedEquation with ⟨rfl, rfl⟩
          exact ⟨.axiomLeft source sourceLookup rfl sourceLink exactStored
            different leftTag rightTag leftReady rightReady⟩
        · subst start
          simp [NextAxiomResult.orientedEndpoints?, different.symm] at orientedEquation
          rcases orientedEquation with ⟨rfl, rfl⟩
          exact ⟨.axiomRight source sourceLookup rfl sourceLink exactStored
            different leftTag rightTag leftReady rightReady⟩
      case h_2 =>
        rename_i vertexTag vertexReady source sourceLookup left right
          conclusion sourceLink
        rcases equation with ⟨produced, equation⟩
        split at equation
        · simp at equation
        · rename_i recursiveResult recursiveEquation
          simp at equation
          have sourceMembership :
              source ∈ ((sourceIndex certificate)[start]?).getD [] := by
            simp [sourceLookup]
          have exactStored :
              certificate.links[source.linkIndex]? =
                some (.tensor left right conclusion) := by
            simpa [sourceLink] using
              (sourceIndex_sound certificate sourceMembership).1
          subst result
          subst trace
          subst linkIndex
          have recursiveNonempty : recursiveResult.trace ≠ [] := by
            rcases nextAxiomWithFuel?_route recursiveEquation with
              ⟨routeReached, routePartner, route⟩
            exact route.traceNonempty
          have recursiveOriented :
              recursiveResult.orientedEndpoints? =
                some (reached, partner) := by
            simpa [NextAxiomResult.orientedEndpoints?,
              List.getLast?_cons_of_ne_nil recursiveNonempty] using
                orientedEquation
          subst start
          rcases induction recursiveResult recursiveEquation rfl rfl
              recursiveOriented with
            ⟨tail⟩
          exact ⟨.tensor source sourceLookup rfl sourceLink exactStored
            vertexTag vertexReady tail⟩
      case h_3 =>
        rename_i vertexTag vertexReady source sourceLookup left right
          conclusion sourceLink
        rcases equation with ⟨produced, equation⟩
        split at equation
        · simp at equation
        · rename_i recursiveResult recursiveEquation
          simp at equation
          have sourceMembership :
              source ∈ ((sourceIndex certificate)[start]?).getD [] := by
            simp [sourceLookup]
          have exactStored :
              certificate.links[source.linkIndex]? =
                some (.par left right conclusion) := by
            simpa [sourceLink] using
              (sourceIndex_sound certificate sourceMembership).1
          subst result
          subst trace
          subst linkIndex
          have recursiveNonempty : recursiveResult.trace ≠ [] := by
            rcases nextAxiomWithFuel?_route recursiveEquation with
              ⟨routeReached, routePartner, route⟩
            exact route.traceNonempty
          have recursiveOriented :
              recursiveResult.orientedEndpoints? =
                some (reached, partner) := by
            simpa [NextAxiomResult.orientedEndpoints?,
              List.getLast?_cons_of_ne_nil recursiveNonempty] using
                orientedEquation
          subst start
          rcases induction recursiveResult recursiveEquation rfl rfl
              recursiveOriented with
            ⟨tail⟩
          exact ⟨.par source sourceLookup rfl sourceLink exactStored
            vertexTag vertexReady tail⟩

/-- The production executable equation and the exact input-only run are
logically equivalent, including the exact recursive trace, reached/partner
orientation, and submitted terminal axiom-link position. -/
theorem execution_iff_nonempty
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat} :
    FreshSourceLeftExecution certificate state fuel tags start trace reached
        partner linkIndex ↔
      Nonempty
        (FreshSourceLeftRun certificate state fuel tags start trace
          reached partner linkIndex) := by
  constructor
  · exact ofExecution
  · rintro ⟨run⟩
    exact run.execution

/-- The exact trace carried by a run has no repeated occurrence. -/
theorem traceNodup
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate state fuel tags start
      trace reached partner linkIndex) :
    trace.Nodup := by
  rcases run.execution with
    ⟨result, equation, traceEquation, resultLinkEquation,
      orientedEquation⟩
  simpa [traceEquation] using result.traceNodup

/-- The named reached endpoint is exactly the last recursively visited
occurrence. -/
theorem traceLast
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate state fuel tags start
      trace reached partner linkIndex) :
    trace.getLast? = some reached := by
  rcases run.execution with
    ⟨result, equation, traceEquation, resultLinkEquation,
      orientedEquation⟩
  rcases nextAxiomWithFuel?_route equation with
    ⟨routeReached, routePartner, route⟩
  have pairEquation :
      (routeReached, routePartner) = (reached, partner) :=
    Option.some.inj
      (route.orientedEndpoints?_eq.symm.trans orientedEquation)
  have reachedEquation : routeReached = reached :=
    congrArg Prod.fst pairEquation
  simpa [traceEquation, reachedEquation] using route.traceLast

/-- The exact trace length is bounded by the supplied executable fuel. -/
theorem traceLength
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate state fuel tags start
      trace reached partner linkIndex) :
    trace.length ≤ fuel := by
  rcases run.execution with
    ⟨result, equation, traceEquation, resultLinkEquation,
      orientedEquation⟩
  simpa [traceEquation] using result.traceLength

/-- The exact trace begins at the indexed run input occurrence. -/
theorem traceHead
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate state fuel tags start
      trace reached partner linkIndex) :
    trace.head? = some start := by
  cases run <;> simp

/-- The run's submitted producer slots form the exact stored source-left
chain represented by its trace. -/
theorem sourceLeftChain
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate state fuel tags start
      trace reached partner linkIndex) :
    SourceLeftChain certificate trace := by
  induction run with
  | axiomLeft => exact .singleton _
  | axiomRight => exact .singleton _
  | tensor _ _ _ _ exactLink _ _ tail induction =>
      exact SourceLeftChain.cons_of_head (.tensor exactLink) induction
        tail.traceHead
  | par _ _ _ _ exactLink _ _ tail induction =>
      exact SourceLeftChain.cons_of_head (.par exactLink) induction
        tail.traceHead

/-- The run reaches its named terminal occurrence along exact submitted
source-left steps. -/
theorem sourceLeftReachable
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate state fuel tags start
      trace reached partner linkIndex) :
    SourceLeftReachable certificate start reached :=
  run.sourceLeftChain.reachable_of_head_last run.traceHead run.traceLast

/-- Every visited occurrence was false in the original input tag carrier. -/
theorem traceFresh
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat} {vertex : Vertex}
    (run : FreshSourceLeftRun certificate state fuel tags start
      trace reached partner linkIndex)
    (membership : vertex ∈ trace) :
    tags[vertex]? = some false := by
  induction run with
  | axiomLeft _ _ _ _ _ _ leftFresh _ _ _ =>
      simp only [List.mem_singleton] at membership
      subst vertex
      exact leftFresh
  | axiomRight _ _ _ _ _ _ _ rightFresh _ _ =>
      simp only [List.mem_singleton] at membership
      subst vertex
      exact rightFresh
  | tensor _ _ _ _ _ currentFresh _ tail induction =>
      simp only [List.mem_cons] at membership
      rcases membership with current | tailMembership
      · subst vertex
        exact currentFresh
      · exact (setIfInBounds_false_reflection (by
          simpa [nextAxiomSetTag_eq] using
            induction tailMembership)).1
  | par _ _ _ _ _ currentFresh _ tail induction =>
      simp only [List.mem_cons] at membership
      rcases membership with current | tailMembership
      · subst vertex
        exact currentFresh
      · exact (setIfInBounds_false_reflection (by
          simpa [nextAxiomSetTag_eq] using
            induction tailMembership)).1

/-- Every visited occurrence is unmarked in the fixed production state. -/
theorem traceReady
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat} {vertex : Vertex}
    (run : FreshSourceLeftRun certificate state fuel tags start
      trace reached partner linkIndex)
    (membership : vertex ∈ trace) :
    state.marks[vertex]? = some none := by
  induction run with
  | axiomLeft _ _ _ _ _ _ _ _ leftReady _ =>
      simp only [List.mem_singleton] at membership
      subst vertex
      exact leftReady
  | axiomRight _ _ _ _ _ _ _ _ _ rightReady =>
      simp only [List.mem_singleton] at membership
      subst vertex
      exact rightReady
  | tensor _ _ _ _ _ _ currentReady _ induction =>
      simp only [List.mem_cons] at membership
      rcases membership with current | tailMembership
      · subst vertex
        exact currentReady
      · exact induction tailMembership
  | par _ _ _ _ _ _ currentReady _ induction =>
      simp only [List.mem_cons] at membership
      rcases membership with current | tailMembership
      · subst vertex
        exact currentReady
      · exact induction tailMembership

end FreshSourceLeftRun

end SequentialUnification

end ProofNetIR
