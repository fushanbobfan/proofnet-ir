import ProofNetIR.SequentialFigure7NewRegion

namespace ProofNetIR

/-!
# Exact blockers for fresh source-left runs

Structural well-formedness fixes the source-left search path but does not make
its dynamic tag and raw-mark guards true.  This module classifies an in-bounds
start: either the complete formula-budget path is an exact
`FreshSourceLeftRun`, or one visited occurrence (including the other endpoint
of the terminal axiom) is explicitly unavailable in the input carrier.

The result is local to one source-left search.  It assumes no scheduler
history, queue invariant, executor success, enabledness, reachability,
progress, worklist completeness, or complexity bound for a whole program.
-/

namespace SequentialUnification

/-- One occurrence in the structurally determined source-left region.

`visited` covers the recursively visited route. `terminalPartner` additionally
includes the other endpoint of the terminal submitted axiom, which is checked
by `NEXTAXIOM` even though it is not a trace vertex. -/
inductive SourceLeftRegionVertex (certificate : Certificate)
    (start : Vertex) : Vertex → Prop
  | visited
      {vertex : Vertex}
      (reachable : SourceLeftReachable certificate start vertex) :
      SourceLeftRegionVertex certificate start vertex
  | terminalPartner
      {reached partner : Vertex} {linkIndex : Nat}
      (reachable : SourceLeftReachable certificate start reached)
      (exactAxiom :
        certificate.links[linkIndex]? = some (.axiom reached partner) ∨
          certificate.links[linkIndex]? = some (.axiom partner reached)) :
      SourceLeftRegionVertex certificate start partner

namespace SourceLeftRegionVertex

/-- Prepending one exact stored-left source step transports every region
vertex, including a terminal partner, to the enlarged source region. -/
theorem prepend
    {certificate : Certificate} {source next vertex : Vertex}
    (region : SourceLeftRegionVertex certificate next vertex)
    (step : SourceLeftStep certificate source next) :
    SourceLeftRegionVertex certificate source vertex := by
  cases region with
  | visited reachable =>
      exact .visited (.step step reachable)
  | terminalPartner reachable exactAxiom =>
      exact .terminalPartner (.step step reachable) exactAxiom

/-- Every vertex in a structurally well-formed source-left region belongs to
the certificate formula carrier. -/
theorem inBounds
    {certificate : Certificate} {start vertex : Vertex}
    (region : SourceLeftRegionVertex certificate start vertex)
    (structural : certificate.StructurallyWellFormed)
    (startBound : start < certificate.formulas.size) :
    vertex < certificate.formulas.size := by
  cases region with
  | visited reachable =>
      induction reachable with
      | refl =>
          exact startBound
      | step head tail induction =>
          apply induction
          cases head with
          | tensor exactLink =>
              have membership := List.mem_of_getElem? exactLink
              have wellFormed := structural.2.2.2.2.1 _ membership
              exact wellFormed.2.2.2.1
          | par exactLink =>
              have membership := List.mem_of_getElem? exactLink
              have wellFormed := structural.2.2.2.2.1 _ membership
              exact wellFormed.2.2.2.1
  | terminalPartner reachable exactAxiom =>
      rcases exactAxiom with exactAxiom | exactAxiom
      · have membership := List.mem_of_getElem? exactAxiom
        have wellFormed := structural.2.2.2.2.1 _ membership
        exact wellFormed.2.2.1
      · have membership := List.mem_of_getElem? exactAxiom
        have wellFormed := structural.2.2.2.2.1 _ membership
        exact wellFormed.2.1

end SourceLeftRegionVertex

/-- An exact source-region occurrence whose input tag or raw mark prevents a
fresh source-left run.  The disjunction is intentionally dynamic: structural
missing-source, source multiplicity, malformed incidence, and fuel exhaustion
are eliminated by `freshSourceLeftRun_or_blocker` rather than represented as
blockers. -/
structure FreshSourceBlocker (certificate : Certificate)
    (state : UnificationState) (tags : Array Bool)
    (start : Vertex) : Type where
  vertex : Vertex
  region : SourceLeftRegionVertex certificate start vertex
  unavailable :
    tags[vertex]? ≠ some false ∨ state.marks[vertex]? ≠ some none

namespace FreshSourceBlocker

/-- A blocker in the recursive region remains a blocker after one exact
stored-left source step is prepended. -/
def prepend
    {certificate : Certificate} {state : UnificationState}
    {tags : Array Bool} {source next : Vertex}
    (blocker : FreshSourceBlocker certificate state tags next)
    (step : SourceLeftStep certificate source next) :
    FreshSourceBlocker certificate state tags source where
  vertex := blocker.vertex
  region := blocker.region.prepend step
  unavailable := blocker.unavailable

end FreshSourceBlocker

/-- A duplicate-free finite list contained in an ambient list cannot be
longer than that ambient carrier. -/
private theorem distinct_values_length_le
    {values ambient : List Nat}
    (nodup : values.Nodup)
    (subset : ∀ value ∈ values, value ∈ ambient) :
    values.length ≤ ambient.length := by
  induction values generalizing ambient with
  | nil =>
      simp
  | cons head tail induction =>
      have headMembership : head ∈ ambient :=
        subset head (by simp)
      have tailSubset :
          ∀ value ∈ tail, value ∈ ambient.erase head := by
        intro value membership
        have valueMembership : value ∈ ambient :=
          subset value (by simp [membership])
        have different : value ≠ head := by
          intro same
          subst value
          exact (List.nodup_cons.mp nodup).1 membership
        exact (List.mem_erase_of_ne different).2 valueMembership
      have tailBound :=
        induction (List.nodup_cons.mp nodup).2 tailSubset
      rw [List.length_erase_of_mem headMembership] at tailBound
      have positive : 0 < ambient.length :=
        List.length_pos_of_mem headMembership
      simp only [List.length_cons]
      omega

/-- A duplicate-free list of in-bounds vertices fits inside the formula
carrier. -/
private theorem nodup_length_le_formula_carrier
    {certificate : Certificate} {vertices : List Vertex}
    (nodup : vertices.Nodup)
    (bounded : ∀ vertex ∈ vertices, vertex < certificate.formulas.size) :
    vertices.length ≤ certificate.formulas.size := by
  have subset :
      ∀ vertex ∈ vertices, vertex ∈ List.range certificate.formulas.size := by
    intro vertex membership
    exact List.mem_range.mpr (bounded vertex membership)
  simpa using distinct_values_length_le nodup subset

/-- A route paired with the structural formula-carrier bound for each of its
trace vertices.  The public route stores the final aggregate length bound;
this private refinement is convenient for recursive construction. -/
private structure BoundedFreshSourceLeftRoute
    (certificate : Certificate) (state : UnificationState)
    (tags : Array Bool) (start : Vertex) : Type where
  route :
    SequentialFigure7.FreshSourceLeftRoute certificate state tags start
  traceBound :
    ∀ vertex ∈ route.trace, vertex < certificate.formulas.size
  traceRank :
    ∀ vertex ∈ route.trace,
      certificate.formulaComplexityAt vertex ≤
        certificate.formulaComplexityAt start

namespace BoundedFreshSourceLeftRoute

/-- Prepend one fresh, ready source occurrence to a bounded recursive route. -/
private def prepend
    {certificate : Certificate} {state : UnificationState}
    {tags : Array Bool} {source next : Vertex}
    (bounded :
      BoundedFreshSourceLeftRoute certificate state tags next)
    (step : SourceLeftStep certificate source next)
    (sourceBound : source < certificate.formulas.size)
    (strict :
      certificate.formulaComplexityAt next <
        certificate.formulaComplexityAt source)
    (sourceFresh : tags[source]? = some false)
    (sourceReady : state.marks[source]? = some none) :
    BoundedFreshSourceLeftRoute certificate state tags source := by
  let route := bounded.route
  have sourceNotTrace : source ∉ route.trace := by
    intro membership
    have rankBound := bounded.traceRank source membership
    omega
  have traceNodup : (source :: route.trace).Nodup :=
    List.nodup_cons.mpr ⟨sourceNotTrace, route.traceNodup⟩
  have traceBound :
      ∀ vertex ∈ source :: route.trace,
        vertex < certificate.formulas.size := by
    intro vertex membership
    simp only [List.mem_cons] at membership
    rcases membership with rfl | membership
    · exact sourceBound
    · exact bounded.traceBound vertex membership
  have traceRank :
      ∀ vertex ∈ source :: route.trace,
        certificate.formulaComplexityAt vertex ≤
          certificate.formulaComplexityAt source := by
    intro vertex membership
    simp only [List.mem_cons] at membership
    rcases membership with rfl | membership
    · exact Nat.le_refl _
    · exact Nat.le_trans (bounded.traceRank vertex membership)
        (Nat.le_of_lt strict)
  have traceFresh :
      ∀ {vertex : Vertex}, vertex ∈ source :: route.trace →
        tags[vertex]? = some false := by
    intro vertex membership
    simp only [List.mem_cons] at membership
    rcases membership with rfl | membership
    · exact sourceFresh
    · exact route.traceFresh membership
  have traceReady :
      ∀ {vertex : Vertex}, vertex ∈ source :: route.trace →
        state.marks[vertex]? = some none := by
    intro vertex membership
    simp only [List.mem_cons] at membership
    rcases membership with rfl | membership
    · exact sourceReady
    · exact route.traceReady membership
  refine {
    route := {
      trace := source :: route.trace
      reached := route.reached
      partner := route.partner
      linkIndex := route.linkIndex
      traceNonempty := by simp
      traceHead := by simp
      traceLast := by
        simpa [List.getLast?_cons_of_ne_nil route.traceNonempty] using
          route.traceLast
      chain := route.chain.cons_of_head step route.traceHead
      reachable := .step step route.reachable
      exactAxiom := route.exactAxiom
      traceLength :=
        nodup_length_le_formula_carrier traceNodup traceBound
      traceNodup := traceNodup
      traceFresh := traceFresh
      traceReady := traceReady
      reachedReady := route.reachedReady
      partnerReady := route.partnerReady
      partnerFresh := route.partnerFresh
    }
    traceBound := traceBound
    traceRank := traceRank
  }

end BoundedFreshSourceLeftRoute

/-- Structural source-left classification before conversion to the exact
fuel-indexed run. -/
private theorem route_or_blocker
    {certificate : Certificate} {state : UnificationState}
    {tags : Array Bool} {start : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (startBound : start < certificate.formulas.size) :
    Nonempty
        (BoundedFreshSourceLeftRoute certificate state tags start) ∨
      Nonempty (FreshSourceBlocker certificate state tags start) := by
  have general :
      ∀ rank, ∀ (candidate : Vertex) (candidateTags : Array Bool),
        certificate.formulaComplexityAt candidate = rank →
          candidate < certificate.formulas.size →
            Nonempty
                (BoundedFreshSourceLeftRoute certificate state candidateTags
                  candidate) ∨
              Nonempty
                (FreshSourceBlocker certificate state candidateTags
                  candidate) := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank induction =>
        intro candidate candidateTags candidateRank candidateBound
        by_cases currentFresh : candidateTags[candidate]? = some false
        · by_cases currentReady : state.marks[candidate]? = some none
          · rcases
                StructurallyWellFormed.sourceIndex_lookup_eq_singleton
                  structural candidateBound with
              ⟨source, sourceLookup⟩
            have sourceMembership :
                source ∈
                  (((sourceIndex certificate)[candidate]?).getD []) := by
              simp [sourceLookup]
            have sourceOrigin :=
              sourceIndex_sound certificate sourceMembership
            have linkMembership : source.link ∈ certificate.links :=
              List.mem_of_getElem? sourceOrigin.1
            have sourceWellFormed :
                certificate.LinkWellFormed source.link :=
              structural.2.2.2.2.1 source.link linkMembership
            cases linkEquation : source.link with
            | «axiom» left right =>
                have axiomWellFormed :
                    certificate.LinkWellFormed (.axiom left right) := by
                  simpa [linkEquation] using sourceWellFormed
                have exactStored :
                    certificate.links[source.linkIndex]? =
                      some (.axiom left right) := by
                  simpa [linkEquation] using sourceOrigin.1
                have endpoint : candidate = left ∨ candidate = right := by
                  have incident := sourceOrigin.2
                  simp [linkEquation, Link.containsAxiomEndpoint,
                    Link.produces] at incident
                  rcases incident with incident | incident
                  · exact .inl incident.symm
                  · exact .inr incident.symm
                rcases endpoint with candidateEq | candidateEq
                · subst candidate
                  by_cases partnerFresh : candidateTags[right]? = some false
                  · by_cases partnerReady : state.marks[right]? = some none
                    · have traceBound :
                          ∀ vertex ∈ ([left] : List Vertex),
                            vertex < certificate.formulas.size := by
                        intro vertex membership
                        simp only [List.mem_singleton] at membership
                        subst vertex
                        exact candidateBound
                      have traceRank :
                          ∀ vertex ∈ ([left] : List Vertex),
                            certificate.formulaComplexityAt vertex ≤
                              certificate.formulaComplexityAt left := by
                        intro vertex membership
                        simp only [List.mem_singleton] at membership
                        subst vertex
                        exact Nat.le_refl _
                      exact Or.inl ⟨{
                        route := {
                          trace := [left]
                          reached := left
                          partner := right
                          linkIndex := source.linkIndex
                          traceNonempty := by simp
                          traceHead := by simp
                          traceLast := by simp
                          chain := .singleton left
                          reachable := .refl left
                          exactAxiom := .inl exactStored
                          traceLength :=
                            nodup_length_le_formula_carrier (by simp)
                              traceBound
                          traceNodup := by simp
                          traceFresh := by
                            intro vertex membership
                            simp only [List.mem_singleton] at membership
                            subst vertex
                            exact currentFresh
                          traceReady := by
                            intro vertex membership
                            simp only [List.mem_singleton] at membership
                            subst vertex
                            exact currentReady
                          reachedReady := currentReady
                          partnerReady := partnerReady
                          partnerFresh := partnerFresh
                        }
                        traceBound := traceBound
                        traceRank := traceRank
                      }⟩
                    · exact Or.inr ⟨{
                        vertex := right
                        region := .terminalPartner (.refl left)
                          (.inl exactStored)
                        unavailable := .inr partnerReady
                      }⟩
                  · exact Or.inr ⟨{
                      vertex := right
                      region := .terminalPartner (.refl left)
                        (.inl exactStored)
                      unavailable := .inl partnerFresh
                    }⟩
                · subst candidate
                  by_cases partnerFresh : candidateTags[left]? = some false
                  · by_cases partnerReady : state.marks[left]? = some none
                    · have traceBound :
                          ∀ vertex ∈ ([right] : List Vertex),
                            vertex < certificate.formulas.size := by
                        intro vertex membership
                        simp only [List.mem_singleton] at membership
                        subst vertex
                        exact candidateBound
                      have traceRank :
                          ∀ vertex ∈ ([right] : List Vertex),
                            certificate.formulaComplexityAt vertex ≤
                              certificate.formulaComplexityAt right := by
                        intro vertex membership
                        simp only [List.mem_singleton] at membership
                        subst vertex
                        exact Nat.le_refl _
                      exact Or.inl ⟨{
                        route := {
                          trace := [right]
                          reached := right
                          partner := left
                          linkIndex := source.linkIndex
                          traceNonempty := by simp
                          traceHead := by simp
                          traceLast := by simp
                          chain := .singleton right
                          reachable := .refl right
                          exactAxiom := .inr exactStored
                          traceLength :=
                            nodup_length_le_formula_carrier (by simp)
                              traceBound
                          traceNodup := by simp
                          traceFresh := by
                            intro vertex membership
                            simp only [List.mem_singleton] at membership
                            subst vertex
                            exact currentFresh
                          traceReady := by
                            intro vertex membership
                            simp only [List.mem_singleton] at membership
                            subst vertex
                            exact currentReady
                          reachedReady := currentReady
                          partnerReady := partnerReady
                          partnerFresh := partnerFresh
                        }
                        traceBound := traceBound
                        traceRank := traceRank
                      }⟩
                    · exact Or.inr ⟨{
                        vertex := left
                        region := .terminalPartner (.refl right)
                          (.inr exactStored)
                        unavailable := .inr partnerReady
                      }⟩
                  · exact Or.inr ⟨{
                      vertex := left
                      region := .terminalPartner (.refl right)
                        (.inr exactStored)
                      unavailable := .inl partnerFresh
                    }⟩
            | tensor left right conclusion =>
                have tensorWellFormed :
                    certificate.LinkWellFormed
                      (.tensor left right conclusion) := by
                  simpa [linkEquation] using sourceWellFormed
                have produced : conclusion = candidate := by
                  have incident := sourceOrigin.2
                  simpa [linkEquation, Link.containsAxiomEndpoint,
                    Link.produces] using incident
                subst conclusion
                have exactStored :
                    certificate.links[source.linkIndex]? =
                      some (.tensor left right candidate) := by
                  simpa [linkEquation] using sourceOrigin.1
                have leftBound : left < certificate.formulas.size :=
                  tensorWellFormed.2.2.2.1
                have strict :
                    certificate.formulaComplexityAt left <
                      certificate.formulaComplexityAt candidate := by
                  simpa [Certificate.linkConclusionComplexity] using
                    tensorWellFormed.premise_complexity_lt_conclusion
                      (premise := left) (by simp [Link.premises])
                have strictRank :
                    certificate.formulaComplexityAt left < rank := by
                  simpa [candidateRank] using strict
                have step : SourceLeftStep certificate candidate left :=
                  .tensor exactStored
                rcases induction
                    (certificate.formulaComplexityAt left) strictRank left
                    candidateTags rfl leftBound with
                  recursive | blocker
                · rcases recursive with ⟨bounded⟩
                  exact Or.inl ⟨bounded.prepend step candidateBound
                    strict currentFresh currentReady⟩
                · rcases blocker with ⟨blocker⟩
                  exact Or.inr ⟨blocker.prepend step⟩
            | «par» left right conclusion =>
                have parWellFormed :
                    certificate.LinkWellFormed
                      (.par left right conclusion) := by
                  simpa [linkEquation] using sourceWellFormed
                have produced : conclusion = candidate := by
                  have incident := sourceOrigin.2
                  simpa [linkEquation, Link.containsAxiomEndpoint,
                    Link.produces] using incident
                subst conclusion
                have exactStored :
                    certificate.links[source.linkIndex]? =
                      some (.par left right candidate) := by
                  simpa [linkEquation] using sourceOrigin.1
                have leftBound : left < certificate.formulas.size :=
                  parWellFormed.2.2.2.1
                have strict :
                    certificate.formulaComplexityAt left <
                      certificate.formulaComplexityAt candidate := by
                  simpa [Certificate.linkConclusionComplexity] using
                    parWellFormed.premise_complexity_lt_conclusion
                      (premise := left) (by simp [Link.premises])
                have strictRank :
                    certificate.formulaComplexityAt left < rank := by
                  simpa [candidateRank] using strict
                have step : SourceLeftStep certificate candidate left :=
                  .par exactStored
                rcases induction
                    (certificate.formulaComplexityAt left) strictRank left
                    candidateTags rfl leftBound with
                  recursive | blocker
                · rcases recursive with ⟨bounded⟩
                  exact Or.inl ⟨bounded.prepend step candidateBound
                    strict currentFresh currentReady⟩
                · rcases blocker with ⟨blocker⟩
                  exact Or.inr ⟨blocker.prepend step⟩
          · exact Or.inr ⟨{
              vertex := candidate
              region := .visited (.refl candidate)
              unavailable := .inr currentReady
            }⟩
        · exact Or.inr ⟨{
            vertex := candidate
            region := .visited (.refl candidate)
            unavailable := .inl currentFresh
          }⟩
  exact general (certificate.formulaComplexityAt start) start tags rfl
    startBound

end SequentialUnification

open SequentialUnification

/-- An in-bounds source-left start is classified exactly at the dynamic
boundary: either the formula-budget proof-relevant run exists, or an explicit
visited/terminal-partner region occurrence fails its input tag or raw-mark
guard.

This theorem does not assert that blockers are absent in scheduler-reachable
states, and therefore is not a progress, totality, or worklist-completeness
theorem. -/
theorem Certificate.StructurallyWellFormed.freshSourceLeftRun_or_blocker
    {certificate : Certificate} {state : UnificationState}
    {tags : Array Bool} {start : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (startBound : start < certificate.formulas.size) :
    (∃ trace reached partner linkIndex,
      Nonempty
        (FreshSourceLeftRun certificate state certificate.formulas.size tags
          start trace reached partner linkIndex)) ∨
      Nonempty (FreshSourceBlocker certificate state tags start) := by
  rcases route_or_blocker structural startBound with bounded | blocker
  · rcases bounded with ⟨bounded⟩
    left
    exact ⟨bounded.route.trace, bounded.route.reached,
      bounded.route.partner, bounded.route.linkIndex,
      bounded.route.toFreshSourceLeftRun structural⟩
  · exact Or.inr blocker

/-- If every structurally determined source-region occurrence is fresh and
raw-unmarked in the input carrier, the blocker branch is impossible and the
formula-budget exact run exists.  Later scheduler work may use this theorem by
proving region availability from authentic history; no such history fact is
assumed here. -/
theorem Certificate.StructurallyWellFormed.freshSourceLeftRun_of_regionAvailable
    {certificate : Certificate} {state : UnificationState}
    {tags : Array Bool} {start : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (startBound : start < certificate.formulas.size)
    (available :
      ∀ {vertex : Vertex},
        SourceLeftRegionVertex certificate start vertex →
          tags[vertex]? = some false ∧
            state.marks[vertex]? = some none) :
    ∃ trace reached partner linkIndex,
      Nonempty
        (FreshSourceLeftRun certificate state certificate.formulas.size tags
          start trace reached partner linkIndex) := by
  rcases
      Certificate.StructurallyWellFormed.freshSourceLeftRun_or_blocker
        structural startBound with run | blocker
  · exact run
  · rcases blocker with ⟨blocker⟩
    rcases available blocker.region with ⟨fresh, ready⟩
    rcases blocker.unavailable with blocked | blocked
    · exact False.elim (blocked fresh)
    · exact False.elim (blocked ready)

namespace SequentialFigure7

open SequentialSchedulerBridge

namespace NewGuard

/-- On a structurally well-formed certificate, the source-left route launched
from the opposite premise of the selected tensor cannot return to the selected
ready head.

This is the `visited`-region separation fact.  It uses neither scheduler
history nor proof-net switching correctness: unique consumer provenance and
strict formula-complexity descent already exclude the return.  The distinct
`terminalPartner` region case is intentionally not covered here. -/
theorem not_sourceLeftReachable_mate_head
    {certificate : Certificate}
    {before : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (guard : NewGuard certificate before) :
    ¬ SourceLeftReachable certificate guard.tensor.mate
        guard.head.vertex := by
  intro reachable
  have tensorWellFormed := guard.tensor_valid.2.2.1
  have premiseEquation := guard.tensor_valid.2.2.2
  have headBound : guard.head.vertex < certificate.formulas.size := by
    rw [premiseEquation]
    cases sideEquation : guard.tensor.side with
    | storedLeft =>
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using tensorWellFormed.2.2.2.1
    | storedRight =>
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using tensorWellFormed.2.2.2.2.1
  rcases reachable.eq_or_exists_lastStep with
      same | ⟨previous, pathPrefix, last⟩
  · exact guard.mate_ne same
  · cases last with
    | @tensor linkIndex _ right _ exactLink =>
        have lastConsumer :
            certificate.consumerIndex.uniqueConsumer? guard.head.vertex =
              some linkIndex := by
          apply ConsumerIndex.build_uniqueConsumer?_eq_some structural
            exactLink headBound
          simp [Link.premises]
        have indexEquation : linkIndex = guard.tensor.linkIndex := by
          rw [guard.tensor_valid.1] at lastConsumer
          exact Option.some.inj lastConsumer.symm
        have linkEquation :
            Link.tensor guard.head.vertex right previous =
              Link.tensor guard.tensor.storedLeft guard.tensor.storedRight
                guard.tensor.conclusion := by
          apply Option.some.inj
          rw [← exactLink, indexEquation, guard.tensor_valid.2.1]
        have fields :
            guard.head.vertex = guard.tensor.storedLeft ∧
            right = guard.tensor.storedRight ∧
            previous = guard.tensor.conclusion := by
          simpa using Link.tensor.inj linkEquation
        cases sideEquation : guard.tensor.side with
        | storedLeft =>
            have mateStrict :
                certificate.formulaComplexityAt guard.tensor.mate <
                  certificate.formulaComplexityAt
                    guard.tensor.conclusion := by
              have strict :=
                tensorWellFormed.premise_complexity_lt_conclusion
                  (premise := guard.tensor.mate)
                  (by
                    simp [Link.premises, TensorBelow.mate,
                      TensorPremiseSide.mate, sideEquation])
              simpa [Certificate.linkConclusionComplexity] using strict
            have pathLe :=
              pathPrefix.formulaComplexity_le structural
            rw [fields.2.2] at pathLe
            omega
        | storedRight =>
            have headIsRight :
                guard.head.vertex = guard.tensor.storedRight := by
              simpa [TensorBelow.premise, TensorPremiseSide.premise,
                sideEquation] using premiseEquation
            exact tensorWellFormed.1
              (fields.1.symm.trans headIsRight)
    | @par linkIndex _ right _ exactLink =>
        have lastConsumer :
            certificate.consumerIndex.uniqueConsumer? guard.head.vertex =
              some linkIndex := by
          apply ConsumerIndex.build_uniqueConsumer?_eq_some structural
            exactLink headBound
          simp [Link.premises]
        have indexEquation : linkIndex = guard.tensor.linkIndex := by
          rw [guard.tensor_valid.1] at lastConsumer
          exact Option.some.inj lastConsumer.symm
        have impossible :
            Link.par guard.head.vertex right previous =
              Link.tensor guard.tensor.storedLeft guard.tensor.storedRight
                guard.tensor.conclusion := by
          apply Option.some.inj
          rw [← exactLink, indexEquation, guard.tensor_valid.2.1]
        cases impossible

end NewGuard

end SequentialFigure7

end ProofNetIR
