/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopMarkedNonconclusionDebt
import ProofNetIR.SequentialFigure7ContinuationCredit

/-!
# Finite and endpoint-localized continuation exits

Continuation credit cannot follow concretely marked non-global conclusions
forever: formula complexity strictly increases at every exact connective
consumer.  `ContinuationExit` records the resulting finite normalization.

At a drained active boundary, its open cases yield concrete facts: a raw mate is an
unmarked non-global occurrence, while scheduled conclusion work is unmarked
and attached to a strictly older boundary.  The third case is a concretely
marked global conclusion.

`LocalizedContinuationExit` is a separate strengthening receipt.  Its two
constructors bind the raw-mate or future-conclusion endpoint to one
specified component; there is deliberately no marked-global constructor.
`ActiveTopContinuationExitLocalized` requires such a receipt for every marked
nonconclusion on the active frontier.  Current continuation, scheduler, and
correctness APIs do not derive this ownership law.  The final marking theorem
is therefore conditional, with no unconditional progress or completion claim.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- A finite ascent through concretely marked, non-global connective
conclusions. -/
inductive MarkedConclusionChain (certificate : Certificate)
    (state : ReservationState) : Vertex → Vertex → Prop where
  | refl (vertex : Vertex) :
      MarkedConclusionChain certificate state vertex vertex
  | step {vertex terminal : Vertex} {rawAge : RawTokenAge}
      (consumer : ConnectiveBelow certificate vertex)
      (marked :
        state.core.marks[consumer.conclusion]? = some (some rawAge))
      (notConclusion : consumer.conclusion ∉ certificate.conclusions)
      (tail : MarkedConclusionChain certificate state
        consumer.conclusion terminal) :
      MarkedConclusionChain certificate state vertex terminal

/-- A normalized terminal receipt reached after zero or more marked,
non-global connective conclusions. -/
inductive ContinuationExit (certificate : Certificate)
    (state : ReservationState) (origin : Vertex) : Prop where
  | rawMate {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none) :
      ContinuationExit certificate state origin
  | futureConclusion {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (consumer : ConnectiveBelow certificate terminal)
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion) :
      ContinuationExit certificate state origin
  | markedGlobalConclusion {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (consumer : ConnectiveBelow certificate terminal)
      (rawAge : RawTokenAge)
      (marked :
        state.core.marks[consumer.conclusion]? = some (some rawAge))
      (global : consumer.conclusion ∈ certificate.conclusions) :
      ContinuationExit certificate state origin

/-- An endpoint-bound open continuation exit localized to one component.  The raw
constructor binds the endpoint to `consumer.mate`; the future constructor
binds it to `consumer.conclusion`.  There is no marked-global constructor. -/
inductive LocalizedContinuationExit (certificate : Certificate)
    (state : ReservationState) (origin : Vertex)
    (component : UnificationComponent) : Prop where
  | rawMate {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (consumer : ConnectiveBelow certificate terminal)
      (mateFrontier : consumer.mate ∈ component.frontier)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none) :
      LocalizedContinuationExit certificate state origin component
  | futureConclusion {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (consumer : ConnectiveBelow certificate terminal)
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion)
      (conclusionFrontier : consumer.conclusion ∈ component.frontier)
      (conclusionNotGlobal :
        consumer.conclusion ∉ certificate.conclusions) :
      LocalizedContinuationExit certificate state origin component

private theorem connectivePremiseMembership
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    vertex ∈ consumer.submittedLink.premises := by
  rcases consumer with
    ⟨linkIndex, kind, storedLeft, storedRight, conclusion, side,
      consumerEq, linkEq, wellFormed, premiseEq⟩
  subst vertex
  cases kind <;> cases side <;>
    simp [ConnectiveBelow.submittedLink,
      SequentialConnectiveKind.asLink, Link.premises,
      TensorPremiseSide.premise]

private theorem connectivePremiseComplexityLtConclusion
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    certificate.formulaComplexityAt vertex <
      certificate.formulaComplexityAt consumer.conclusion := by
  have strict :=
    consumer.wellFormed.premise_complexity_lt_conclusion
      (connectivePremiseMembership consumer)
  cases kindEquation : consumer.kind <;>
    simpa [Certificate.linkConclusionComplexity,
      SequentialConnectiveKind.asLink, kindEquation] using strict

private theorem connectiveConclusionBound
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    consumer.conclusion < certificate.formulas.size := by
  cases kindEquation : consumer.kind with
  | par =>
      have wellFormed :
          certificate.LinkWellFormed
            (.par consumer.storedLeft consumer.storedRight
              consumer.conclusion) := by
        simpa [SequentialConnectiveKind.asLink, kindEquation] using
          consumer.wellFormed
      exact wellFormed.2.2.2.2.2.1
  | tensor =>
      have wellFormed :
          certificate.LinkWellFormed
            (.tensor consumer.storedLeft consumer.storedRight
              consumer.conclusion) := by
        simpa [SequentialConnectiveKind.asLink, kindEquation] using
          consumer.wellFormed
      exact wellFormed.2.2.2.2.2.1

private theorem connectiveMateNotConclusion
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex)
    (structural : certificate.StructurallyWellFormed) :
    consumer.mate ∉ certificate.conclusions := by
  have mateMembership : consumer.mate ∈ consumer.submittedLink.premises := by
    cases kindEquation : consumer.kind <;>
      cases sideEquation : consumer.side <;>
        simp [ConnectiveBelow.submittedLink,
          SequentialConnectiveKind.asLink, Link.premises,
          ConnectiveBelow.mate, TensorPremiseSide.mate,
          kindEquation, sideEquation]
  have mateBound : consumer.mate < certificate.formulas.size :=
    consumer.mate_bound
  intro boundary
  have node := structural.2.2.2.2.2 consumer.mate mateBound
  have parentZero : certificate.parentUseCount consumer.mate = 0 := by
    simpa [boundary] using node.2
  have linkMembership : consumer.submittedLink ∈ certificate.links :=
    List.mem_of_getElem? consumer.link_eq
  have filtered :
      consumer.submittedLink ∈
        certificate.links.filter (·.usesAsPremise consumer.mate) := by
    apply List.mem_filter.mpr
    exact ⟨linkMembership, by
      simpa [Link.usesAsPremise] using mateMembership⟩
  have positive : 0 < certificate.parentUseCount consumer.mate := by
    unfold Certificate.parentUseCount
    exact List.length_pos_of_mem filtered
  omega

/-- Continuation credit cannot follow marked non-global conclusions forever.
It ends at one of the three normalized receipt forms. -/
theorem MarkedNonconclusionContinuation.continuationExit
    {certificate : Certificate} {state : ReservationState}
    (continuation : MarkedNonconclusionContinuation certificate state)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (marked : state.core.marks[vertex]? = some (some rawAge))
    (notConclusion : vertex ∉ certificate.conclusions) :
    ContinuationExit certificate state vertex := by
  cases continuation marked notConclusion with
  | rawMate consumer mateUnmarked =>
      exact .rawMate (.refl vertex) consumer mateUnmarked
  | futureConclusion consumer boundary work =>
      exact .futureConclusion (.refl vertex) consumer boundary work
  | markedConclusion consumer conclusionRawAge conclusionMarked =>
      by_cases global : consumer.conclusion ∈ certificate.conclusions
      · exact .markedGlobalConclusion (.refl vertex) consumer
          conclusionRawAge conclusionMarked global
      · have exit := continuation.continuationExit conclusionMarked global
        cases exit with
        | rawMate chain terminalConsumer mateUnmarked =>
            exact .rawMate
              (.step consumer conclusionMarked global chain)
              terminalConsumer mateUnmarked
        | futureConclusion chain terminalConsumer boundary work =>
            exact .futureConclusion
              (.step consumer conclusionMarked global chain)
              terminalConsumer boundary work
        | markedGlobalConclusion chain terminalConsumer terminalRawAge
            terminalMarked terminalGlobal =>
            exact .markedGlobalConclusion
              (.step consumer conclusionMarked global chain)
              terminalConsumer terminalRawAge terminalMarked terminalGlobal
termination_by
  certificate.intrinsicComplexityBudget -
    certificate.formulaComplexityAt vertex
decreasing_by
  have growth := connectivePremiseComplexityLtConclusion consumer
  have bounded :=
    certificate.formulaComplexityAt_le_intrinsicComplexityBudget
      (connectiveConclusionBound consumer)
  omega

private theorem futureWorkRawAgeNeActiveOfActiveTopDrained
    {certificate : Certificate} {state : ReservationState}
    {rawAge active : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt state rawAge vertex)
    (invariant : SchedulerInvariant certificate state)
    (drained : ActiveTopDrained state)
    (activeTop : state.stack.sigma.getLast? = some active) :
    rawAge ≠ active := by
  intro same
  subst rawAge
  rcases drained with
    ⟨drainedAge, drainedComponent, drainedTop,
      drainedLookup, frontierDrained⟩
  have activeEq : active = drainedAge :=
    Option.some.inj (activeTop.symm.trans drainedTop)
  subst drainedAge
  cases work with
  | ready sigmaAt readyAt member =>
      rcases invariant.ready_bucket_frontier_exact sigmaAt readyAt with
        ⟨component, componentLookup, exactMembership⟩
      have componentEq : component = drainedComponent :=
        Option.some.inj
          (Option.some.inj (componentLookup.symm.trans drainedLookup))
      subst component
      have facts := (exactMembership vertex).mp member
      exact frontierDrained vertex facts.1 facts.2
  | waiting waitingAt member =>
      have activeUndefined :
          state.stack.waiting[active]? = some .undefined :=
        invariant.stack_operationalWaitingDomain.active_undefined
          invariant.stack_wellShaped activeTop
      rw [activeUndefined] at waitingAt
      simp at waitingAt

/-- Future work in a drained invariant state belongs to a scheduler boundary
strictly older than the active top. -/
theorem FutureWorkAt.rawAge_lt_active_of_activeTopDrained
    {certificate : Certificate} {state : ReservationState}
    {rawAge active : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt state rawAge vertex)
    (invariant : SchedulerInvariant certificate state)
    (drained : ActiveTopDrained state)
    (activeTop : state.stack.sigma.getLast? = some active) :
    rawAge < active := by
  have rawAgeMembership : rawAge ∈ state.stack.sigma :=
    work.rawAge_mem_sigma invariant
  rcases List.getLast?_eq_some_iff.mp activeTop with
    ⟨sigmaPrefix, sigmaEquation⟩
  have increasing := invariant.stack_wellShaped.sigma_partition.strictIncreasing
  rw [sigmaEquation] at rawAgeMembership increasing
  simp only [List.mem_append, List.mem_singleton] at rawAgeMembership
  rcases rawAgeMembership with inPrefix | same
  · exact (List.pairwise_append.mp increasing).2.2
      rawAge inPrefix active (by simp)
  · exact False.elim
      (futureWorkRawAgeNeActiveOfActiveTopDrained
        work invariant drained activeTop same)

/-- Eliminate a normalized continuation at a drained active boundary.  The
raw-mate handler receives a structurally non-global unmarked mate; the future
handler receives an unmarked conclusion at a strictly older boundary. -/
theorem ContinuationExit.elim_of_activeTopDrained
    {certificate : Certificate} {state : ReservationState}
    {origin : Vertex} {active : RawTokenAge}
    (exit : ContinuationExit certificate state origin)
    (invariant : SchedulerInvariant certificate state)
    (drained : ActiveTopDrained state)
    (activeTop : state.stack.sigma.getLast? = some active)
    {motive : Prop}
    (rawMate :
      ∀ {terminal : Vertex},
        (chain : MarkedConclusionChain certificate state origin terminal) →
          (consumer : ConnectiveBelow certificate terminal) →
            consumer.mate ∉ certificate.conclusions →
              state.core.marks[consumer.mate]? = some none → motive)
    (olderFutureConclusion :
      ∀ {terminal : Vertex},
        (chain : MarkedConclusionChain certificate state origin terminal) →
          (consumer : ConnectiveBelow certificate terminal) →
            (boundary : RawTokenAge) →
              (work : FutureWorkAt state boundary consumer.conclusion) →
                boundary < active →
                  state.core.marks[consumer.conclusion]? = some none →
                    motive)
    (markedGlobalConclusion :
      ∀ {terminal : Vertex},
        (chain : MarkedConclusionChain certificate state origin terminal) →
          (consumer : ConnectiveBelow certificate terminal) →
            (rawAge : RawTokenAge) →
              state.core.marks[consumer.conclusion]? = some (some rawAge) →
                consumer.conclusion ∈ certificate.conclusions → motive) :
    motive := by
  cases exit with
  | rawMate chain consumer mateUnmarked =>
      exact rawMate chain consumer
        (connectiveMateNotConclusion consumer invariant.structural)
        mateUnmarked
  | futureConclusion chain consumer boundary work =>
      exact olderFutureConclusion chain consumer boundary work
        (work.rawAge_lt_active_of_activeTopDrained
          invariant drained activeTop)
        (invariant.queued_vertices_unmarked
          consumer.conclusion work.mem_queued)
  | markedGlobalConclusion chain consumer rawAge marked global =>
      exact markedGlobalConclusion chain consumer rawAge marked global

/-- Forget component-local ownership while retaining the continuation
branch receipt. -/
theorem LocalizedContinuationExit.continuationExit
    {certificate : Certificate} {state : ReservationState}
    {origin : Vertex} {component : UnificationComponent}
    (localized :
      LocalizedContinuationExit certificate state origin component) :
    ContinuationExit certificate state origin := by
  cases localized with
  | rawMate chain consumer _mateFrontier mateUnmarked =>
      exact .rawMate chain consumer mateUnmarked
  | futureConclusion chain consumer boundary work _frontier _notGlobal =>
      exact .futureConclusion chain consumer boundary work

/-- An endpoint-locality sufficient law: every active marked nonconclusion
has a raw-mate or future-conclusion exit localized to its active component.
This module does not derive the law or claim it is necessary. -/
def ActiveTopContinuationExitLocalized
    (certificate : Certificate) (state : ReservationState) : Prop :=
  ∀ {rawAge markedAge : RawTokenAge}
      {component : UnificationComponent} {markedVertex : Vertex},
    state.stack.sigma.getLast? = some rawAge →
      state.core.components[rawAge]? = some (some component) →
        markedVertex ∈ component.frontier →
          state.core.marks[markedVertex]? = some (some markedAge) →
            markedVertex ∉ certificate.conclusions →
              LocalizedContinuationExit certificate state
                markedVertex component

/-- Structural well-formedness, queued-vertex unmarkedness, and the
endpoint-locality sufficient law imply active-top marked-nonconclusion debt. -/
theorem activeTopMarkedNonconclusionDebt_of_continuationExitLocalized
    {certificate : Certificate} {state : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (queuedUnmarked : QueuedVerticesUnmarked state)
    (localized : ActiveTopContinuationExitLocalized certificate state) :
    ActiveTopMarkedNonconclusionDebt certificate state := by
  intro rawAge markedAge component markedVertex activeTop componentLookup
    markedFrontier marked notConclusion
  have exit := localized activeTop componentLookup markedFrontier marked
    notConclusion
  cases exit with
  | rawMate chain consumer mateFrontier mateUnmarked =>
      exact ⟨consumer.mate, mateFrontier,
        connectiveMateNotConclusion consumer structural,
        mateUnmarked⟩
  | futureConclusion chain consumer boundary work conclusionFrontier
      conclusionNotGlobal =>
      exact ⟨consumer.conclusion, conclusionFrontier,
        conclusionNotGlobal,
        queuedUnmarked consumer.conclusion work.mem_queued⟩

/-- If the endpoint-locality sufficient law holds, a declaratively correct
invariant state with a drained active top has a concrete mark at every
formula occurrence. -/
theorem SchedulerInvariant.allMarked_of_activeTopDrained_of_continuationExitLocalized
    {certificate : Certificate} {state : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (drained : ActiveTopDrained state)
    (localized : ActiveTopContinuationExitLocalized certificate state) :
    state.core.allMarked = true :=
  SchedulerInvariant.allMarked_of_activeTopDrained_of_nonconclusionDebt
    correct invariant drained
      (activeTopMarkedNonconclusionDebt_of_continuationExitLocalized
        invariant.structural invariant.queued_vertices_unmarked localized)

end SequentialFigure7
end ProofNetIR
