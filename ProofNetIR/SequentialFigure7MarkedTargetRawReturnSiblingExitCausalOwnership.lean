/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnSiblingExitScheduled
import ProofNetIR.SequentialFigure7MarkedTargetRawReturnSiblingExitCausalOrder

/-!
# Figure-7 sibling future-endpoint causal ownership

Exact scheduler locations expose two concrete marks below every future-work
endpoint.  This module authenticates both marks in the canonical history and
orders their events.  The terminal premise lies outside the active occurrence
carrier, so its representative is strictly older than the active boundary.
The mate is either outside with a strictly older representative or is owned by
the active carrier with representative exactly equal to the active boundary.

The active-owned mate case is further aligned with scheduler semantics.  Ready
work remains ready.  Waiting work must orient the terminal at the older span
boundary and the mate at the active younger boundary; the reverse orientation
would create a strict boundary cycle.

The resulting target and typed Wait theorem do not eliminate a future
endpoint, produce a non-global ready-tail witness, derive the history-tail law,
or prove completion, progress, termination, or dispatcher totality.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

/-- A concrete mark is either owned by the active occurrence carrier at that
exact representative or lies outside with a strictly older representative. -/
inductive MarkedVertexActiveCarrierStatus
    (state : ReservationState) (active : RawTokenAge)
    (owned : List Vertex) (vertex : Vertex) (rawAge : RawTokenAge) : Prop where
  | active
      (membership : vertex ∈ owned)
      (representative : state.core.representative rawAge = active) :
      MarkedVertexActiveCarrierStatus state active owned vertex rawAge
  | olderOutside
      (notMembership : vertex ∉ owned)
      (representativeOlder : state.core.representative rawAge < active) :
      MarkedVertexActiveCarrierStatus state active owned vertex rawAge

private theorem ReadyHeadInput.markedRepresentative_le_active
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (marked : state.core.marks[vertex]? = some (some rawAge)) :
    state.core.representative rawAge ≤ input.rawAge := by
  have stackMarked : state.stack.marks[vertex]? = some (some rawAge) := by
    rw [← invariant.realizesSigma.marks_eq]
    exact marked
  have rawAgeBound : rawAge < state.stack.nextAge :=
    invariant.stack_wellShaped.assigned_age_bound vertex rawAge stackMarked
  have realized := invariant.realizesSigma.representative_eq_boundary rawAgeBound
  by_cases rawLtActive : rawAge < input.rawAge
  · exact Nat.le_trans
      (UnificationState.OrderedParents.representative_le
        invariant.core_orderedParents rawAge)
      (Nat.le_of_lt rawLtActive)
  · have activeLeRaw : input.rawAge ≤ rawAge := Nat.le_of_not_gt rawLtActive
    have topLookup := invariant.stack_wellShaped.sigma_partition
      |>.sigmaBoundary?_eq_top_of_le input.sigma_top activeLeRaw rawAgeBound
    exact Nat.le_of_eq (Option.some.inj (realized.symm.trans topLookup))

private theorem markedOutsideActiveOwned_representative_lt
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (marked : state.core.marks[vertex]? = some (some rawAge))
    (notOwned : vertex ∉ owned) :
    state.core.representative rawAge < input.rawAge := by
  have representativeLe := input.markedRepresentative_le_active invariant marked
  have representativeNe : state.core.representative rawAge ≠ input.rawAge := by
    intro sameRepresentative
    rcases SchedulerInvariant.exactMarkedOccurrenceOwner invariant marked with
      ⟨ownerRawAge, ownerIndex, ownerComponent, ownerUsed, ownerOwned,
        ownerMarked, ownerRepresentative, ownerLookup, ownerOccurrence,
        _ownerAccounted, ownerMembership⟩
    have ownerRawAgeEq : ownerRawAge = rawAge := by
      exact Option.some.inj (Option.some.inj (ownerMarked.symm.trans marked))
    subst ownerRawAge
    have ownerIndexEq : ownerIndex = input.rawAge :=
      ownerRepresentative.symm.trans sameRepresentative
    have ownerLookupAtActive :
        state.core.components[input.rawAge]? = some (some ownerComponent) := by
      simpa [ownerIndexEq] using ownerLookup
    have componentEq : ownerComponent = component := by
      exact Option.some.inj
        (Option.some.inj (ownerLookupAtActive.symm.trans componentLookup))
    subst ownerComponent
    have ownedEq : ownerOwned = owned :=
      Certificate.OccurrenceDerivation.owned_unique invariant.structural
        ownerOccurrence.derivation occurrence.derivation
    exact notOwned (by simpa [ownedEq] using ownerMembership)
  exact Nat.lt_of_le_of_ne representativeLe representativeNe

private theorem markedActiveOwned_representative_eq
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (marked : state.core.marks[vertex]? = some (some rawAge))
    (vertexOwned : vertex ∈ owned) :
    state.core.representative rawAge = input.rawAge := by
  rcases invariant.component_forest_provenance with
    ⟨_usedAt, _ownedAt, live, _separated, _markedOwned⟩
  have activeFacts := live componentLookup
  have ownedEq :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      activeFacts.1.derivation occurrence.derivation
  have vertexOwnedAt : vertex ∈ _ownedAt input.rawAge := by
    simpa [ownedEq] using vertexOwned
  rcases activeFacts.2 vertex vertexOwnedAt with
    ⟨storedAge, storedMarked, representative⟩ |
      ⟨unmarked, _frontier⟩
  · have ageEq : storedAge = rawAge := by
      exact Option.some.inj (Option.some.inj (storedMarked.symm.trans marked))
    simpa [ageEq] using representative
  · have impossible : (some (some rawAge) : Option (Option RawTokenAge)) =
        some none := marked.symm.trans unmarked
    simp at impossible

private theorem markedVertex_activeCarrierStatus
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (marked : state.core.marks[vertex]? = some (some rawAge)) :
    MarkedVertexActiveCarrierStatus state input.rawAge owned vertex rawAge := by
  by_cases vertexOwned : vertex ∈ owned
  · exact .active vertexOwned
      (markedActiveOwned_representative_eq input invariant componentLookup
        occurrence marked vertexOwned)
  · exact .olderOutside vertexOwned
      (markedOutsideActiveOwned_representative_lt input invariant componentLookup
        occurrence marked vertexOwned)

/-- Authenticate and order the marked premises of a future-work endpoint,
while classifying its mate against the active occurrence carrier. -/
theorem ConnectiveBelow.futureWorkPremises_causalOwnership
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {terminal : Vertex}
    (consumer : ConnectiveBelow certificate terminal)
    {boundary : RawTokenAge}
    (work : FutureWorkAt state boundary consumer.conclusion)
    (terminalOutside : terminal ∉ owned) :
    ∃ terminalAge mateAge,
      state.core.marks[terminal]? = some (some terminalAge) ∧
        state.core.marks[consumer.mate]? = some (some mateAge) ∧
        tagHistory.RawMarked terminalAge terminal ∧
        tagHistory.RawMarked mateAge consumer.mate ∧
        state.core.representative terminalAge < input.rawAge ∧
        MarkedVertexActiveCarrierStatus state input.rawAge owned consumer.mate
          mateAge ∧
        (tagHistory.RawMarkedBefore terminalAge terminal mateAge consumer.mate ∨
          tagHistory.RawMarkedBefore mateAge consumer.mate terminalAge terminal) := by
  rcases ProofNetIR.SequentialFigure7.ConnectiveBelow.premisesMarked_of_futureWork
      consumer work invariant with
    ⟨⟨terminalAge, terminalMarked⟩, mateAge, mateMarked⟩
  have terminalEvent : tagHistory.RawMarked terminalAge terminal :=
    tagHistory.final_rawMarked_iff.mp terminalMarked
  have mateEvent : tagHistory.RawMarked mateAge consumer.mate :=
    tagHistory.final_rawMarked_iff.mp mateMarked
  refine ⟨terminalAge, mateAge, terminalMarked, mateMarked, terminalEvent,
    mateEvent, ?_, ?_, ?_⟩
  · exact markedOutsideActiveOwned_representative_lt input invariant
      componentLookup occurrence terminalMarked terminalOutside
  · exact markedVertex_activeCarrierStatus input invariant componentLookup
      occurrence mateMarked
  · exact CanonicalTagHistory.RawMarkedBefore.total_of_vertex_ne
      terminalEvent mateEvent consumer.mate_ne.symm

/-- Exact scheduler alternatives when the mate of a future-work endpoint is
owned by the active carrier.  A waiting endpoint must orient the terminal at
the older boundary and the mate at the active younger boundary. -/
inductive FutureWorkActiveMateSchedulerOutcome
    (certificate : Certificate) (state : ReservationState)
    (input : ReadyHeadInput state) (terminal : Vertex)
    (consumer : ConnectiveBelow certificate terminal)
    (boundary : RawTokenAge) : Prop where
  | ready {position : Nat} {bucket : List Vertex}
      {component : UnificationComponent}
      (sigmaAt : state.stack.sigma[position]? = some boundary)
      (readyAt : state.stack.ready[position]? = some bucket)
      (member : consumer.conclusion ∈ bucket)
      (componentLookup :
        state.core.components[boundary]? = some (some component))
      (frontier : consumer.conclusion ∈ component.frontier)
      (unmarked : state.core.marks[consumer.conclusion]? = some none) :
      FutureWorkActiveMateSchedulerOutcome certificate state input terminal
        consumer boundary
  | waitingReturn {payload : List Vertex} {linkIndex : Nat}
      {left right olderPremise youngerPremise : Vertex}
      {olderAge youngerAge : RawTokenAge}
      (waitingAt : state.stack.waiting[boundary]? =
        some (.initialized payload))
      (member : consumer.conclusion ∈ payload)
      (linkLookup :
        certificate.links[linkIndex]? =
          some (.par left right consumer.conclusion))
      (sourceLookup :
        (SequentialUnification.sourceIndex certificate)[consumer.conclusion]? =
          some [{ linkIndex := linkIndex, link := .par left right consumer.conclusion }])
      (unmarked : state.core.marks[consumer.conclusion]? = some none)
      (olderMarked :
        state.core.marks[olderPremise]? = some (some olderAge))
      (youngerMarked :
        state.core.marks[youngerPremise]? = some (some youngerAge))
      (olderBoundary :
        sigmaBoundary? state.stack.sigma olderAge = some boundary)
      (boundaryOlder : boundary < input.rawAge)
      (terminalOlder : terminal = olderPremise)
      (mateYounger : consumer.mate = youngerPremise)
      (youngerBoundaryActive :
        sigmaBoundary? state.stack.sigma youngerAge = some input.rawAge) :
      FutureWorkActiveMateSchedulerOutcome certificate state input terminal
        consumer boundary

private theorem marked_representative_eq_boundary
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {vertex : Vertex} {rawAge boundary : RawTokenAge}
    (marked : state.core.marks[vertex]? = some (some rawAge))
    (boundaryLookup :
      sigmaBoundary? state.stack.sigma rawAge = some boundary) :
    state.core.representative rawAge = boundary := by
  have stackMarked : state.stack.marks[vertex]? = some (some rawAge) := by
    rw [← invariant.realizesSigma.marks_eq]
    exact marked
  have rawAgeBound : rawAge < state.stack.nextAge :=
    invariant.stack_wellShaped.assigned_age_bound vertex rawAge stackMarked
  have realized := invariant.realizesSigma.representative_eq_boundary rawAgeBound
  exact Option.some.inj (realized.symm.trans boundaryLookup)

private theorem waiting_endpointOrientation
    {certificate : Certificate}
    {terminal : Vertex} (consumer : ConnectiveBelow certificate terminal)
    (structural : certificate.StructurallyWellFormed)
    {linkIndex : Nat} {left right olderPremise youngerPremise : Vertex}
    (linkLookup :
      certificate.links[linkIndex]? =
        some (.par left right consumer.conclusion))
    (premiseOrientation :
      (olderPremise = left ∧ youngerPremise = right) ∨
        (olderPremise = right ∧ youngerPremise = left)) :
    (terminal = olderPremise ∧ consumer.mate = youngerPremise) ∨
      (terminal = youngerPremise ∧ consumer.mate = olderPremise) := by
  have consumerMembership : consumer.submittedLink ∈ certificate.links :=
    List.mem_of_getElem? consumer.link_eq
  have consumerProduces :
      consumer.submittedLink.produces consumer.conclusion = true := by
    cases kindEq : consumer.kind <;>
      simp [ConnectiveBelow.submittedLink, SequentialConnectiveKind.asLink,
        kindEq, Link.produces]
  have sameLink :=
    UnificationState.StructurallyWellFormed.producerLink_unique
      structural consumerMembership consumerProduces
        (List.mem_of_getElem? linkLookup)
        (by simp [Link.produces])
  cases kindEq : consumer.kind <;> cases sideEq : consumer.side <;>
    simp [ConnectiveBelow.submittedLink, SequentialConnectiveKind.asLink,
      kindEq] at sameLink
  all_goals
    rcases premiseOrientation with orientation | orientation
    · rcases orientation with ⟨rfl, rfl⟩
      rcases sameLink with ⟨rfl, rfl, _⟩
      have premiseEq := consumer.premise_eq
      simp_all [TensorPremiseSide.premise, TensorPremiseSide.mate,
        ConnectiveBelow.mate]
    · rcases orientation with ⟨rfl, rfl⟩
      rcases sameLink with ⟨rfl, rfl, _⟩
      have premiseEq := consumer.premise_eq
      simp_all [TensorPremiseSide.premise, TensorPremiseSide.mate,
        ConnectiveBelow.mate]

/-- A future endpoint whose mate is active-owned is either ready work or an
exact waiting return from the older terminal to the active mate. -/
theorem FutureWorkAtExactSchedulerLocation.activeMateSchedulerOutcome
    {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {terminal : Vertex}
    {consumer : ConnectiveBelow certificate terminal}
    {boundary terminalAge mateAge : RawTokenAge}
    (location :
      FutureWorkAtExactSchedulerLocation certificate state boundary
        consumer.conclusion)
    (invariant : SchedulerInvariant certificate state)
    (terminalMarked :
      state.core.marks[terminal]? = some (some terminalAge))
    (mateMarked :
      state.core.marks[consumer.mate]? = some (some mateAge))
    (terminalRepresentativeOlder :
      state.core.representative terminalAge < input.rawAge)
    (mateRepresentativeActive :
      state.core.representative mateAge = input.rawAge) :
    FutureWorkActiveMateSchedulerOutcome certificate state input terminal
      consumer boundary := by
  cases location with
  | ready sigmaAt readyAt member componentLookup frontier unmarked =>
      exact .ready sigmaAt readyAt member componentLookup frontier unmarked
  | @waiting boundary' payload vertex linkIndex left right olderPremise
      youngerPremise olderAge youngerAge youngerBoundary waitingAt member
      linkLookup sourceLookup unmarked premiseOrientation olderMarked
      youngerMarked olderBoundary youngerBoundaryLookup boundaryLt =>
      have olderRepresentative :=
        marked_representative_eq_boundary invariant olderMarked olderBoundary
      have youngerRepresentative :=
        marked_representative_eq_boundary invariant youngerMarked
          youngerBoundaryLookup
      rcases waiting_endpointOrientation consumer invariant.structural linkLookup
          premiseOrientation with
        orientation | orientation
      · rcases orientation with ⟨terminalOlder, mateYounger⟩
        have terminalAgeEq : terminalAge = olderAge := by
          have marksEq := terminalMarked.symm.trans
            (by simpa [← terminalOlder] using olderMarked)
          exact Option.some.inj (Option.some.inj marksEq)
        have boundaryOlder : boundary < input.rawAge := by
          rw [← olderRepresentative, ← terminalAgeEq]
          exact terminalRepresentativeOlder
        have mateAgeEq : mateAge = youngerAge := by
          have marksEq := mateMarked.symm.trans (by simpa [← mateYounger] using youngerMarked)
          exact Option.some.inj (Option.some.inj marksEq)
        have youngerBoundaryActive : youngerBoundary = input.rawAge := by
          rw [← youngerRepresentative, ← mateAgeEq]
          exact mateRepresentativeActive
        exact .waitingReturn waitingAt member linkLookup sourceLookup unmarked
          olderMarked youngerMarked olderBoundary boundaryOlder terminalOlder mateYounger
          (by simpa [youngerBoundaryActive] using youngerBoundaryLookup)
      · rcases orientation with ⟨terminalYounger, mateOlder⟩
        have mateAgeEq : mateAge = olderAge := by
          have marksEq := mateMarked.symm.trans (by simpa [← mateOlder] using olderMarked)
          exact Option.some.inj (Option.some.inj marksEq)
        have boundaryActive : boundary = input.rawAge := by
          rw [← olderRepresentative, ← mateAgeEq]
          exact mateRepresentativeActive
        have terminalAgeEq : terminalAge = youngerAge := by
          have marksEq := terminalMarked.symm.trans
            (by simpa [← terminalYounger] using youngerMarked)
          exact Option.some.inj (Option.some.inj marksEq)
        have youngerBoundaryOlder : youngerBoundary < input.rawAge := by
          rw [← youngerRepresentative, ← terminalAgeEq]
          exact terminalRepresentativeOlder
        have activeLtYounger : input.rawAge < youngerBoundary := by
          simpa [boundaryActive] using boundaryLt
        exact False.elim
          ((Nat.not_lt_of_ge (Nat.le_of_lt activeLtYounger))
            youngerBoundaryOlder)

/-- The endpoint mate is either strictly older and outside the active carrier,
or active-owned with the ready/waiting-return scheduler classification. -/
inductive FutureWorkMateActiveCarrierScheduledStatus
    (certificate : Certificate) (state : ReservationState)
    (input : ReadyHeadInput state) (owned : List Vertex)
    (terminal : Vertex) (consumer : ConnectiveBelow certificate terminal)
    (boundary mateAge : RawTokenAge) : Prop where
  | olderOutside
      (notMembership : consumer.mate ∉ owned)
      (representativeOlder :
        state.core.representative mateAge < input.rawAge) :
      FutureWorkMateActiveCarrierScheduledStatus certificate state input owned
        terminal consumer boundary mateAge
  | active
      (membership : consumer.mate ∈ owned)
      (representative :
        state.core.representative mateAge = input.rawAge)
      (scheduler :
        FutureWorkActiveMateSchedulerOutcome certificate state input terminal
          consumer boundary) :
      FutureWorkMateActiveCarrierScheduledStatus certificate state input owned
        terminal consumer boundary mateAge

/-- A scheduled sibling exit whose older future endpoint also carries exact
canonical raw-mark events, strict terminal age, mate ownership, and premise
chronology. -/
inductive ContinuationExitRawOrFutureActiveCarrierCausalOwnershipOutcome
    (certificate : Certificate) (state : ReservationState)
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (owned : List Vertex)
    (current : ConnectiveBelow certificate input.vertex)
    (origin : Vertex) : Prop where
  | rawOutside {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none)
      (mateOutside : consumer.mate ∉ owned) :
      ContinuationExitRawOrFutureActiveCarrierCausalOwnershipOutcome
        certificate state tagHistory input owned current origin
  | rawSelectedReturn {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none)
      (mateSelected : consumer.mate = input.vertex)
      (terminalCurrentMate : terminal = current.mate)
      (conclusionCurrent : consumer.conclusion = current.conclusion) :
      ContinuationExitRawOrFutureActiveCarrierCausalOwnershipOutcome
        certificate state tagHistory input owned current origin
  | futureOlder {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion)
      (conclusionOutside : consumer.conclusion ∉ owned)
      (boundaryOlder : boundary < input.rawAge)
      (terminalAge mateAge : RawTokenAge)
      (terminalMarked : state.core.marks[terminal]? = some (some terminalAge))
      (mateMarked :
        state.core.marks[consumer.mate]? = some (some mateAge))
      (terminalEvent : tagHistory.RawMarked terminalAge terminal)
      (mateEvent : tagHistory.RawMarked mateAge consumer.mate)
      (terminalRepresentativeOlder :
        state.core.representative terminalAge < input.rawAge)
      (mateStatus :
        FutureWorkMateActiveCarrierScheduledStatus certificate state input owned
          terminal consumer boundary mateAge)
      (premiseOrder :
        tagHistory.RawMarkedBefore terminalAge terminal mateAge consumer.mate ∨
          tagHistory.RawMarkedBefore mateAge consumer.mate terminalAge terminal)
      (location : FutureWorkAtExactSchedulerLocation certificate state boundary
        consumer.conclusion) :
      ContinuationExitRawOrFutureActiveCarrierCausalOwnershipOutcome
        certificate state tagHistory input owned current origin

/-- Add exact raw-mark chronology and active-carrier ownership to a scheduled
sibling exit. -/
theorem ContinuationExitRawOrFutureActiveCarrierScheduledOutcome.causalOwnershipOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {current : ConnectiveBelow certificate input.vertex} {origin : Vertex}
    (outcome :
      ContinuationExitRawOrFutureActiveCarrierScheduledOutcome certificate
        state input owned current origin)
    (invariant : SchedulerInvariant certificate state) :
    ContinuationExitRawOrFutureActiveCarrierCausalOwnershipOutcome certificate
      state tagHistory input owned current origin := by
  cases outcome with
  | rawOutside chain terminalOutside consumer mateUnmarked mateOutside =>
      exact .rawOutside chain terminalOutside consumer mateUnmarked mateOutside
  | rawSelectedReturn chain terminalOutside consumer mateUnmarked mateSelected
      terminalCurrentMate conclusionCurrent =>
      exact .rawSelectedReturn chain terminalOutside consumer mateUnmarked
        mateSelected terminalCurrentMate conclusionCurrent
  | futureOlder chain terminalOutside consumer boundary work conclusionOutside
      boundaryOlder terminalMarked mateMarked location =>
      rcases ProofNetIR.SequentialFigure7.ConnectiveBelow.futureWorkPremises_causalOwnership
          tagHistory input invariant
            componentLookup occurrence consumer work terminalOutside with
        ⟨terminalAge, mateAge, terminalMarkedExact, mateMarkedExact,
          terminalEvent, mateEvent, terminalRepresentativeOlder, mateStatus,
          premiseOrder⟩
      have scheduledMateStatus :
          FutureWorkMateActiveCarrierScheduledStatus certificate state input owned
            _ consumer boundary mateAge := by
        cases mateStatus with
        | active membership representative =>
            exact .active membership representative
              (location.activeMateSchedulerOutcome invariant terminalMarkedExact
                mateMarkedExact terminalRepresentativeOlder representative)
        | olderOutside notMembership representativeOlder =>
            exact .olderOutside notMembership representativeOlder
      exact .futureOlder chain terminalOutside consumer boundary work
        conclusionOutside boundaryOlder terminalAge mateAge terminalMarkedExact
        mateMarkedExact terminalEvent mateEvent terminalRepresentativeOlder
        scheduledMateStatus premiseOrder location

/-- The marked re-entry target after authenticating and chronologically
ordering every older future sibling endpoint. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalOwnershipTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) (current : ConnectiveBelow certificate input.vertex) :
    Prop :=
  ∃ (outerAge : RawTokenAge),
    tagHistory.RawMarked outerAge current.mate ∧
      ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (directed : certificate.referenceSwitchingGraph.DirectedEdge)
          (markedAge : RawTokenAge),
        path.start = current.mate ∧
          path.finish ∈ owned ∧
          directed ∈ path.traversed ∧
          ActiveCarrierInboundParentEdge certificate component owned directed ∧
          directed.target ≠ input.vertex ∧
          directed.target ≠ current.mate ∧
          state.core.marks[directed.target]? = some (some markedAge) ∧
          tagHistory.RawMarked markedAge directed.target ∧
          state.core.representative markedAge = input.rawAge ∧
          ∃ targetConsumer : ConnectiveBelow certificate directed.target,
            targetConsumer.mate ≠ input.vertex ∧
            directed.source = targetConsumer.conclusion ∧
            targetConsumer.conclusion ∉ owned ∧
            ((∃ terminal,
                MarkedConclusionChain certificate state directed.target
                    terminal ∧
                  ∃ terminalConsumer : ConnectiveBelow certificate terminal,
                    state.core.marks[terminalConsumer.mate]? = some none ∧
                    terminalConsumer.mate ∉ owned) ∨
              (MarkedConclusionChainFirstCausalDescent certificate state
                  tagHistory directed.target current.mate input.rawAge ∧
                ∃ (consumer : ConnectiveBelow certificate directed.target)
                    (mateAge : RawTokenAge),
                  tagHistory.RawMarkedBefore mateAge consumer.mate outerAge
                      current.mate ∧
                    ContinuationExitRawOrFutureActiveCarrierCausalOwnershipOutcome
                        certificate state tagHistory input owned current
                          consumer.conclusion ∧
                      MarkedConclusionRawReturnCyclicJunctionCausalOutcome
                        certificate state tagHistory current.mate
                          consumer.conclusion outerAge) ∨
              (∃ terminal,
                MarkedConclusionChain certificate state directed.target
                    terminal ∧
                  ∃ terminalConsumer : ConnectiveBelow certificate terminal,
                    ∃ boundary,
                      FutureWorkAt state boundary terminalConsumer.conclusion ∧
                      terminalConsumer.conclusion ∉ owned ∧
                      boundary < input.rawAge) ∨
              ∃ terminal,
                MarkedConclusionChain certificate state directed.target terminal ∧
                  ∃ terminalConsumer : ConnectiveBelow certificate terminal,
                    ∃ conclusionAge,
                      state.core.marks[terminalConsumer.conclusion]? =
                          some (some conclusionAge) ∧
                        terminalConsumer.conclusion ∈ certificate.conclusions ∧
                        terminalConsumer.conclusion ∉ owned ∧
                        state.core.representative conclusionAge < input.rawAge)

namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitScheduledTarget

/-- Upgrade the scheduled sibling target to canonical raw-mark chronology and
active-carrier mate ownership. -/
theorem causalOwnershipTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    {current : ConnectiveBelow certificate input.vertex}
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitScheduledTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalOwnershipTarget
      tagHistory input component owned current := by
  rcases target with
    ⟨outerAge, outerEvent, path, directed, markedAge, pathStart, finishOwned,
      directedMembership, parentEdge, targetNeSelected, targetNeMate,
      targetMarked, targetEvent, representativeEq, targetConsumer,
      targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside,
      status⟩
  refine ⟨outerAge, outerEvent, path, directed, markedAge, pathStart,
    finishOwned, directedMembership, parentEdge, targetNeSelected,
    targetNeMate, targetMarked, targetEvent, representativeEq, targetConsumer,
    targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside, ?_⟩
  rcases status with raw | descent | future | marked
  · exact Or.inl raw
  · rcases descent with
      ⟨descent, consumer, mateAge, mateBeforeOuter, siblingOutcome,
        causalOutcome⟩
    exact Or.inr (Or.inl ⟨descent, consumer, mateAge, mateBeforeOuter,
      siblingOutcome.causalOwnershipOutcome componentLookup occurrence invariant,
      causalOutcome⟩)
  · exact Or.inr (Or.inr (Or.inl future))
  · exact Or.inr (Or.inr (Or.inr marked))

end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitScheduledTarget

namespace CanonicalTagHistory

private theorem CommitmentIntervalParTraceOutcome.mapCausalOwnershipStatus
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state}
    {consumer : ConnectiveBelow certificate input.vertex}
    {position edgeCount : Nat} {first : RawTokenAge}
    {beforeStatus afterStatus : Prop}
    (outcome : tagHistory.CommitmentIntervalParTraceOutcome input consumer
      position edgeCount first beforeStatus)
    (mapStatus : beforeStatus → afterStatus) :
    tagHistory.CommitmentIntervalParTraceOutcome input consumer position
      edgeCount first afterStatus := by
  cases outcome with
  | avoiding path => exact .avoiding path
  | equalSelected offset parent child event offsetLt parentAt childAt
      notAvoiding membership eventAge childEq side beforeTrace afterTrace trace =>
      exact .equalSelected offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childEq side beforeTrace afterTrace trace
  | equalMate offset parent child event offsetLt parentAt childAt notAvoiding
      membership eventAge childEq side beforeTrace afterTrace trace =>
      exact .equalMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childEq side beforeTrace afterTrace trace
  | olderMate offset parent child event offsetLt parentAt childAt notAvoiding
      membership eventAge childEq side beforeTrace afterTrace trace status =>
      exact .olderMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childEq side beforeTrace afterTrace trace
        (mapStatus status)

end CanonicalTagHistory

namespace WaitStep

/-- In the strictly older Wait branch, authenticate and order both premises of
every scheduled future sibling endpoint and classify its mate by active-carrier
ownership. -/
theorem commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalOwnershipOutcome
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (correct : certificate.DeclarativelyCorrect)
    (connected : certificate.ReferenceSwitchingConnected)
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (step : WaitStep certificate before after)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      before.core.components[step.prepared.stackResult.rawAge]? =
        some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {position edgeCount : Nat} {first : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : before.stack.sigma[position]? = some first)
    (lastAt :
      before.stack.sigma[position + edgeCount]? =
        some step.prepared.stackResult.rawAge)
    (noTail :
      ¬ ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) :
    tagHistory.CommitmentIntervalParTraceOutcome
      step.prepared.readyHeadInput step.consumer position edgeCount first
        (step.consumer.mate ∉ owned ∧
          before.core.marks[step.consumer.mate]? =
            some (some step.mateRawAge) ∧
          before.core.representative step.mateRawAge <
            step.prepared.stackResult.rawAge ∧
        ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalOwnershipTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply CanonicalTagHistory.CommitmentIntervalParTraceOutcome.mapCausalOwnershipStatus
    (step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitScheduledOutcome
      correct connected tagHistory invariant componentLookup occurrence positive
        firstAt lastAt noTail)
  intro status
  rcases status with ⟨mateOutside, mateMarked, representativeOlder, target⟩
  exact ⟨mateOutside, mateMarked, representativeOlder,
    target.causalOwnershipTarget invariant componentLookup occurrence⟩

end WaitStep

end SequentialFigure7
end ProofNetIR
