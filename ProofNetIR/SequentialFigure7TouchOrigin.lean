import ProofNetIR.SequentialFigure7BlockerHistory

namespace ProofNetIR

/-!
# Canonical Figure-7 touch origins

This module turns global canonical tag-history membership back into one exact
historical initialization or `new` search.  The recovered event retains its
submitted axiom slot, oriented source-left route, and the complete touched
source-left region, including the terminal partner outside the stored trace.

The result is historical provenance only.  It does not identify a touched
vertex with a current live-component owner, attach raw token ages to search
events, or establish final ownership, scheduler progress, totality, worklist
completeness, fallback removal, or a complexity bound.
-/

namespace SequentialUnification

/-- Every member of a named source-left chain is reachable from its head. -/
theorem SourceLeftChain.reachable_of_head_mem
    {certificate : Certificate} {trace : List Vertex}
    {source vertex : Vertex}
    (chain : SourceLeftChain certificate trace)
    (head : trace.head? = some source)
    (membership : vertex ∈ trace) :
    SourceLeftReachable certificate source vertex := by
  induction chain generalizing source with
  | singleton current =>
      simp only [List.head?_cons, Option.some.injEq] at head
      subst source
      simp only [List.mem_singleton] at membership
      subst vertex
      exact .refl _
  | @cons current next tail step rest induction =>
      simp only [List.head?_cons, Option.some.injEq] at head
      subst source
      rcases List.mem_cons.mp membership with rfl | membership
      · exact .refl _
      · exact .step step (induction (by simp) membership)

/-- Every vertex touched by one exact search lies in that search's complete
source-left region, including the terminal partner outside the trace. -/
theorem NextAxiomRoute.touched_sourceLeftRegion
    {certificate : Certificate} {state : UnificationState} {fuel : Nat}
    {inputTags : Array Bool} {start reached partner vertex : Vertex}
    {result : NextAxiomResult certificate state fuel inputTags}
    (route : NextAxiomRoute start result reached partner)
    (touched : result.Touched vertex) :
    SourceLeftRegionVertex certificate start vertex := by
  rcases touched with inTrace | left | right
  · exact .visited
      (route.chain.reachable_of_head_mem route.traceHead inTrace)
  · subst vertex
    rcases route.storedEndpoints with
      ⟨reachedEq, partnerEq⟩ | ⟨reachedEq, partnerEq⟩
    · subst reached
      exact .visited route.reachable
    · subst partner
      exact .terminalPartner route.reachable route.exactAxiom
  · subst vertex
    rcases route.storedEndpoints with
      ⟨reachedEq, partnerEq⟩ | ⟨reachedEq, partnerEq⟩
    · subst partner
      exact .terminalPartner route.reachable route.exactAxiom
    · subst reached
      exact .visited route.reachable

end SequentialUnification

namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialUnification

/-- Exact originating search event for one globally touched vertex. -/
inductive CanonicalTouchOrigin (certificate : Certificate) :
    {state : ReservationState} →
    {history : ExecutedHistory certificate state} →
    (tagHistory : CanonicalTagHistory certificate history) →
    Vertex → Type where
  | init
      {after : ReservationState} {start vertex : Vertex}
      (step : InitialReservationStep certificate after start)
      (touched : step.result.Touched vertex) :
      CanonicalTouchOrigin certificate
        (CanonicalTagHistory.init step) vertex
  | earlier
      {before : ReservationState} {result : Figure7DispatchResult}
      {history : ExecutedHistory certificate before}
      {invariant : SchedulerInvariant certificate before}
      {dispatch : DispatchStep certificate before invariant result}
      {prior : CanonicalTagHistory certificate history}
      {evidence : DispatchTagEvidence certificate before result}
      {vertex : Vertex}
      (origin : CanonicalTouchOrigin certificate prior vertex) :
      CanonicalTouchOrigin certificate
        (CanonicalTagHistory.later
          (invariant := invariant) (dispatch := dispatch) prior evidence)
        vertex
  | current
      {before after : ReservationState}
      {history : ExecutedHistory certificate before}
      {invariant : SchedulerInvariant certificate before}
      {dispatch :
        DispatchStep certificate before invariant ⟨.new, after⟩}
      {prior : CanonicalTagHistory certificate history}
      (step : NewStep certificate before after)
      {vertex : Vertex}
      (touched : step.search.Touched vertex) :
      CanonicalTouchOrigin certificate
        (CanonicalTagHistory.later
          (invariant := invariant) (dispatch := dispatch) prior
          (.new step))
        vertex

namespace CanonicalTagHistory

/-- Global touch membership recovers one exact initialization or `new` search
origin. -/
theorem touched_nonempty_origin
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {vertex : Vertex}
    (touched : tagHistory.Touched vertex) :
    Nonempty (CanonicalTouchOrigin certificate tagHistory vertex) := by
  induction tagHistory with
  | empty =>
      exact False.elim touched
  | init step =>
      exact ⟨.init step touched⟩
  | @later before result history invariant dispatch prior evidence induction =>
      rcases touched with oldTouched | currentTouched
      · rcases induction oldTouched with ⟨origin⟩
        exact ⟨.earlier origin⟩
      · cases evidence with
        | concl _ => exact False.elim currentTouched
        | nop _ => exact False.elim currentTouched
        | new step => exact ⟨.current step currentTouched⟩
        | wait _ => exact False.elim currentTouched
        | forward _ => exact False.elim currentTouched
        | unifyPayload _ => exact False.elim currentTouched

end CanonicalTagHistory

namespace CanonicalTouchOrigin

/-- An exact touch origin recovers the historical reservation slot, its
oriented route, and the touched vertex's complete historical source-left
region. -/
theorem reservationRegion
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {vertex : Vertex}
    (origin : CanonicalTouchOrigin certificate tagHistory vertex) :
    ∃ start reached partner linkIndex,
      linkIndex ∈ tagHistory.linkIndices ∧
        SourceLeftRegionVertex certificate start vertex ∧
        SourceLeftReachable certificate start reached ∧
        (certificate.links[linkIndex]? =
            some (.axiom reached partner) ∨
          certificate.links[linkIndex]? =
            some (.axiom partner reached)) := by
  induction origin with
  | init step touched =>
      let route := step.route
      exact ⟨_, step.reached, step.partner, step.result.linkIndex, by
        simp [CanonicalTagHistory.linkIndices],
        route.touched_sourceLeftRegion touched,
        route.reachable, route.exactAxiom⟩
  | @earlier before result history invariant dispatch prior evidence
      vertex origin induction =>
      rcases induction with
        ⟨start, reached, partner, linkIndex, membership, region,
          reachable, exactAxiom⟩
      exact ⟨start, reached, partner, linkIndex, by
        simp only [CanonicalTagHistory.linkIndices, List.mem_append]
        exact Or.inr membership,
        region, reachable, exactAxiom⟩
  | @current before after history invariant dispatch prior step vertex
      touched =>
      let route := step.route
      exact ⟨step.tensor.mate, step.reached, step.partner,
        step.search.linkIndex, by
          simp [CanonicalTagHistory.linkIndices,
            DispatchTagEvidence.linkIndices],
        route.touched_sourceLeftRegion touched,
        route.reachable, route.exactAxiom⟩

end CanonicalTouchOrigin

end SequentialFigure7

end ProofNetIR
