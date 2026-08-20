/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParGuardReentryMarkedTargetTemporal
import ProofNetIR.SequentialFigure7ContinuationExit

/-!
# Figure-7 marked re-entry target continuation exit

The exact parent of a mate-separated marked re-entry target can itself have a
marked non-global conclusion. Canonical continuation credit follows that chain
only finitely. Its terminal receipt is raw work outside the active carrier, a
raw return to the current selected/mate pair, future work at a strictly older
boundary, or a marked global conclusion at a strictly older representative.

The raw-return case retains the full marked-conclusion chain, identifies the
terminal consumer with the current conclusion, and records strict formula
complexity growth from the re-entry target to the current mate. This module
does not eliminate that return or any other exit, derive a ready-tail witness
or the history-tail law, or prove progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- Finite continuation normalization of the exact mate-separated marked
re-entry target. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex)
    (current : ConnectiveBelow certificate input.vertex) : Prop :=
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
              MarkedConclusionChain certificate state directed.target terminal ∧
                ∃ terminalConsumer : ConnectiveBelow certificate terminal,
                  state.core.marks[terminalConsumer.mate]? = some none ∧
                    (terminalConsumer.mate ∉ owned ∨
                      (terminalConsumer.mate = input.vertex ∧
                        terminal = current.mate ∧
                        terminalConsumer.conclusion = current.conclusion ∧
                        certificate.formulaComplexityAt directed.target <
                          certificate.formulaComplexityAt terminal))) ∨
            (∃ terminal,
              MarkedConclusionChain certificate state directed.target terminal ∧
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

private theorem connectiveMateMembership
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    consumer.mate ∈ consumer.submittedLink.premises := by
  cases kindEq : consumer.kind <;> cases sideEq : consumer.side <;>
    simp [ConnectiveBelow.mate, ConnectiveBelow.submittedLink,
      SequentialConnectiveKind.asLink, Link.premises,
      TensorPremiseSide.mate, kindEq, sideEq]

private theorem connectiveSubmitted
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    certificate.links[consumer.linkIndex]? =
        some (.tensor consumer.storedLeft consumer.storedRight
          consumer.conclusion) ∨
      certificate.links[consumer.linkIndex]? =
        some (.par consumer.storedLeft consumer.storedRight
          consumer.conclusion) := by
  cases kindEq : consumer.kind with
  | tensor =>
      exact Or.inl (by
        simpa [ConnectiveBelow.submittedLink,
          SequentialConnectiveKind.asLink, kindEq] using consumer.link_eq)
  | par =>
      exact Or.inr (by
        simpa [ConnectiveBelow.submittedLink,
          SequentialConnectiveKind.asLink, kindEq] using consumer.link_eq)

private theorem connectiveVertexOwned_of_premisesOwned
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex)
    {owned : List Vertex}
    (premisesOwned :
      consumer.storedLeft ∈ owned ∧ consumer.storedRight ∈ owned) :
    vertex ∈ owned := by
  have premiseEq := consumer.premise_eq
  cases kindEq : consumer.kind <;> cases sideEq : consumer.side <;>
    simp_all [TensorPremiseSide.premise]

private theorem connectiveBelow_mate_and_conclusion_eq_of_mate_eq
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {leftVertex rightVertex : Vertex}
    (left : ConnectiveBelow certificate leftVertex)
    (right : ConnectiveBelow certificate rightVertex)
    (leftMate : left.mate = rightVertex) :
    right.mate = leftVertex ∧ right.conclusion = left.conclusion := by
  have mateIndex :
      certificate.consumerIndex.uniqueConsumer? left.mate =
        some left.linkIndex := by
    simpa [Certificate.consumerIndex] using
      ConsumerIndex.build_uniqueConsumer?_eq_some structural left.link_eq
        left.mate_bound (connectiveMateMembership left)
  have rightIndex :
      certificate.consumerIndex.uniqueConsumer? rightVertex =
        some left.linkIndex := by
    simpa [leftMate] using mateIndex
  have sameIndex : right.linkIndex = left.linkIndex :=
    Option.some.inj (right.consumer_eq.symm.trans rightIndex)
  have rightLookup := right.link_eq
  rw [sameIndex] at rightLookup
  have sameLink :
      right.kind.asLink right.storedLeft right.storedRight right.conclusion =
        left.kind.asLink left.storedLeft left.storedRight left.conclusion :=
    Option.some.inj (rightLookup.symm.trans left.link_eq)
  have leftPremise := left.premise_eq
  have rightPremise := right.premise_eq
  cases leftKind : left.kind <;> cases rightKind : right.kind <;>
    cases leftSide : left.side <;> cases rightSide : right.side <;>
      simp_all [SequentialConnectiveKind.asLink, ConnectiveBelow.mate,
        TensorPremiseSide.mate, TensorPremiseSide.premise]

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

private theorem MarkedConclusionChain.complexity_le
    {certificate : Certificate} {state : ReservationState}
    {origin terminal : Vertex}
    (chain : MarkedConclusionChain certificate state origin terminal) :
    certificate.formulaComplexityAt origin ≤
      certificate.formulaComplexityAt terminal := by
  induction chain with
  | refl => exact Nat.le_refl _
  | step consumer _marked _notConclusion _tail induction =>
      exact Nat.le_trans
        (Nat.le_of_lt (connectivePremiseComplexityLtConclusion consumer))
        induction

private theorem MarkedConclusionChain.complexity_lt_of_ne
    {certificate : Certificate} {state : ReservationState}
    {origin terminal : Vertex}
    (chain : MarkedConclusionChain certificate state origin terminal)
    (different : origin ≠ terminal) :
    certificate.formulaComplexityAt origin <
      certificate.formulaComplexityAt terminal := by
  cases chain with
  | refl => exact False.elim (different rfl)
  | step consumer _marked _notConclusion tail =>
      exact Nat.lt_of_lt_of_le
        (connectivePremiseComplexityLtConclusion consumer)
        tail.complexity_le

private theorem MarkedConclusionChain.terminalOutside
    {certificate : Certificate} {state : ReservationState}
    {origin terminal : Vertex}
    (structural : certificate.StructurallyWellFormed)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (chain : MarkedConclusionChain certificate state origin terminal)
    (originOutside : origin ∉ owned) :
    terminal ∉ owned := by
  induction chain with
  | refl => exact originOutside
  | step consumer _marked _notConclusion _tail induction =>
      apply induction
      intro conclusionOwned
      have premisesOwned :=
        occurrence.derivation.connectivePremises_owned_of_conclusion_owned
          structural conclusionOwned (connectiveSubmitted consumer)
      exact originOutside
        (connectiveVertexOwned_of_premisesOwned consumer premisesOwned)

private theorem consumerConclusionOutside
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {terminal : Vertex}
    (terminalOutside : terminal ∉ owned)
    (consumer : ConnectiveBelow certificate terminal) :
    consumer.conclusion ∉ owned := by
  intro conclusionOwned
  have premisesOwned :=
    occurrence.derivation.connectivePremises_owned_of_conclusion_owned
      structural conclusionOwned (connectiveSubmitted consumer)
  have terminalOwned : terminal ∈ owned :=
    connectiveVertexOwned_of_premisesOwned consumer premisesOwned
  exact terminalOutside terminalOwned

private theorem ReadyHeadInput.activeReadyExact
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component)) :
    ∀ pending,
      pending ∈ input.vertex :: input.readyTail ↔
        pending ∈ component.frontier ∧
          state.core.marks[pending]? = some none := by
  rcases List.getLast?_eq_some_iff.mp input.top_ready with
    ⟨readyPrefix, readyEquation⟩
  rcases List.getLast?_eq_some_iff.mp input.sigma_top with
    ⟨sigmaPrefix, sigmaEquation⟩
  have prefixLengths : readyPrefix.length = sigmaPrefix.length := by
    have aligned := invariant.stack_wellShaped.ready_aligned
    rw [readyEquation, sigmaEquation] at aligned
    simp at aligned
    omega
  have sigmaLookup :
      state.stack.sigma[readyPrefix.length]? = some input.rawAge := by
    rw [sigmaEquation, prefixLengths]
    simp
  have readyLookup :
      state.stack.ready[readyPrefix.length]? =
        some (input.vertex :: input.readyTail) := by
    rw [readyEquation]
    simp
  rcases invariant.ready_bucket_frontier_exact sigmaLookup readyLookup with
    ⟨actual, actualLookup, exactMembership⟩
  have actualEq : actual = component :=
    Option.some.inj
      (Option.some.inj (actualLookup.symm.trans componentLookup))
  subst actual
  exact exactMembership

private theorem ReadyHeadInput.activeOwnedAccounted
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned) :
    Certificate.OwnedOccurrenceAccounted state.core input.rawAge component
      owned := by
  rcases input.activeComponent invariant with
    ⟨actual, _actualUsed, actualOwned, actualLookup, actualOccurrence,
      actualAccounted, _selectedOwned, _activeRoot⟩
  have actualEq : actual = component :=
    Option.some.inj
      (Option.some.inj (actualLookup.symm.trans componentLookup))
  subst actual
  have ownedEq : actualOwned = owned :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      actualOccurrence.derivation occurrence.derivation
  simpa [ownedEq] using actualAccounted

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
    have ownerRawAgeEq : ownerRawAge = rawAge :=
      Option.some.inj (Option.some.inj (ownerMarked.symm.trans marked))
    subst ownerRawAge
    have ownerIndexEq : ownerIndex = input.rawAge :=
      ownerRepresentative.symm.trans sameRepresentative
    have ownerLookupAtActive :
        state.core.components[input.rawAge]? = some (some ownerComponent) := by
      simpa [ownerIndexEq] using ownerLookup
    have componentEq : ownerComponent = component :=
      Option.some.inj
        (Option.some.inj (ownerLookupAtActive.symm.trans componentLookup))
    subst ownerComponent
    have ownedEq : ownerOwned = owned :=
      Certificate.OccurrenceDerivation.owned_unique invariant.structural
        ownerOccurrence.derivation occurrence.derivation
    exact notOwned (by simpa [ownedEq] using ownerMembership)
  exact Nat.lt_of_le_of_ne representativeLe representativeNe

private theorem FutureWorkAt.boundary_lt_active_of_not_owned
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {boundary : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt state boundary vertex)
    (notOwned : vertex ∉ owned) :
    boundary < input.rawAge := by
  have boundaryNeActive : boundary ≠ input.rawAge := by
    intro sameBoundary
    subst boundary
    cases work with
    | ready sigmaAt readyAt member =>
        rcases invariant.ready_bucket_frontier_exact sigmaAt readyAt with
          ⟨readyComponent, readyLookup, exactMembership⟩
        have componentEq : readyComponent = component :=
          Option.some.inj
            (Option.some.inj (readyLookup.symm.trans componentLookup))
        subst readyComponent
        have vertexFrontier : vertex ∈ component.frontier :=
          ((exactMembership vertex).mp member).1
        exact notOwned
          (occurrence.derivation.frontier_subset_owned vertex vertexFrontier)
    | waiting waitingAt _member =>
        have activeUndefined :
            state.stack.waiting[input.rawAge]? = some .undefined :=
          invariant.stack_operationalWaitingDomain.active_undefined
            invariant.stack_wellShaped input.sigma_top
        rw [activeUndefined] at waitingAt
        simp at waitingAt
  have boundaryMembership : boundary ∈ state.stack.sigma :=
    work.rawAge_mem_sigma invariant
  rcases List.getLast?_eq_some_iff.mp input.sigma_top with
    ⟨sigmaPrefix, sigmaEq⟩
  have increasing := invariant.stack_wellShaped.sigma_partition.strictIncreasing
  rw [sigmaEq] at boundaryMembership increasing
  simp only [List.mem_append, List.mem_singleton] at boundaryMembership
  rcases boundaryMembership with inPrefix | same
  · exact (List.pairwise_append.mp increasing).2.2 boundary inPrefix
      input.rawAge (by simp)
  · exact False.elim (boundaryNeActive same)

namespace ActiveCarrierExternalReentryMarkedMateSeparatedTemporalTarget

/-- Normalize the target-bound marked-parent branch through its finite
continuation chain. A raw endpoint is outside the carrier or returns exactly
to the current selected/mate pair; future and marked-global endpoints remain
outside at a strictly older boundary or representative. -/
theorem continuationExitTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (invariant : SchedulerInvariant certificate state)
    (current : ConnectiveBelow certificate input.vertex)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedTemporalTarget tagHistory
        input component owned current)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget
      tagHistory input component owned current := by
  rcases target with
    ⟨path, directed, markedAge, pathStarts, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetNeMate, targetMarked, authentic,
      representativeEq, targetConsumer, targetConsumerMateNeSelected,
      sourceConsumer, targetConclusionOutside, status⟩
  refine ⟨path, directed, markedAge, pathStarts, finishOwned,
    directedMembership, parentEdge, targetNeSelected, targetNeMate,
    targetMarked, authentic, representativeEq, targetConsumer,
    targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside, ?_⟩
  rcases status with raw | future | marked
  · rcases raw with ⟨mateUnmarked, mateOutside⟩
    exact Or.inl ⟨directed.target,
      MarkedConclusionChain.refl directed.target, targetConsumer,
      mateUnmarked, Or.inl mateOutside⟩
  · rcases future with ⟨boundary, work, older⟩
    exact Or.inr (Or.inl ⟨directed.target,
      MarkedConclusionChain.refl directed.target, targetConsumer, boundary,
      work, targetConclusionOutside, older⟩)
  · rcases marked with ⟨firstAge, firstMarked, firstOlder⟩
    have continuation : MarkedNonconclusionContinuation certificate state :=
      tagHistory.markedNonconclusionContinuation
    by_cases firstGlobal :
        targetConsumer.conclusion ∈ certificate.conclusions
    · exact Or.inr (Or.inr ⟨directed.target,
        MarkedConclusionChain.refl directed.target, targetConsumer, firstAge,
        firstMarked, firstGlobal, targetConclusionOutside, firstOlder⟩)
    · have exit := continuation.continuationExit firstMarked firstGlobal
      cases exit with
      | @rawMate terminal chain terminalConsumer mateUnmarked =>
          let fullChain :
              MarkedConclusionChain certificate state directed.target
                terminal :=
            .step targetConsumer firstMarked firstGlobal chain
          have terminalOutside := chain.terminalOutside invariant.structural
            occurrence targetConclusionOutside
          by_cases mateOutside : terminalConsumer.mate ∉ owned
          · exact Or.inl ⟨_, fullChain, terminalConsumer, mateUnmarked,
              Or.inl mateOutside⟩
          · have mateOwned : terminalConsumer.mate ∈ owned := by
              simpa using mateOutside
            have accounted := input.activeOwnedAccounted invariant
              componentLookup occurrence
            rcases accounted terminalConsumer.mate mateOwned with
              markedCase | rawCase
            · rcases markedCase with ⟨mateAge, mateMarked, _mateRepresentative⟩
              have impossible := mateMarked.symm.trans mateUnmarked
              simp at impossible
            · have mateReady :
                  terminalConsumer.mate ∈ input.vertex :: input.readyTail :=
                (input.activeReadyExact invariant componentLookup
                  terminalConsumer.mate).mpr ⟨rawCase.2, rawCase.1⟩
              rcases List.mem_cons.mp mateReady with mateSelected | mateTail
              · have sameLink :=
                  connectiveBelow_mate_and_conclusion_eq_of_mate_eq
                    invariant.structural terminalConsumer current mateSelected
                have terminalEq := sameLink.1.symm
                have conclusionEq := sameLink.2.symm
                have targetNeTerminal : directed.target ≠ terminal := by
                  intro same
                  apply targetNeMate
                  exact same.trans terminalEq
                exact Or.inl ⟨_, fullChain, terminalConsumer, mateUnmarked,
                  Or.inr ⟨mateSelected, terminalEq, conclusionEq,
                    fullChain.complexity_lt_of_ne targetNeTerminal⟩⟩
              · exact False.elim (noTail ⟨terminalConsumer.mate, mateTail,
                  submittedPremise_not_conclusion invariant.structural
                    terminalConsumer.link_eq
                    (connectiveMateMembership terminalConsumer)⟩)
      | @futureConclusion terminal chain terminalConsumer boundary work =>
          let fullChain :
              MarkedConclusionChain certificate state directed.target
                terminal :=
            .step targetConsumer firstMarked firstGlobal chain
          have terminalOutside := chain.terminalOutside invariant.structural
            occurrence targetConclusionOutside
          have conclusionOutside := consumerConclusionOutside
            invariant.structural occurrence terminalOutside terminalConsumer
          have older := work.boundary_lt_active_of_not_owned input invariant
            componentLookup occurrence conclusionOutside
          exact Or.inr (Or.inl ⟨_, fullChain, terminalConsumer, boundary, work,
            conclusionOutside, older⟩)
      | @markedGlobalConclusion terminal chain terminalConsumer conclusionAge
          conclusionMarked conclusionGlobal =>
          let fullChain :
              MarkedConclusionChain certificate state directed.target
                terminal :=
            .step targetConsumer firstMarked firstGlobal chain
          have terminalOutside := chain.terminalOutside invariant.structural
            occurrence targetConclusionOutside
          have conclusionOutside := consumerConclusionOutside
            invariant.structural occurrence terminalOutside terminalConsumer
          have older := markedOutsideActiveOwned_representative_lt input
            invariant componentLookup occurrence conclusionMarked
            conclusionOutside
          exact Or.inr (Or.inr ⟨_, fullChain, terminalConsumer,
            conclusionAge, conclusionMarked, conclusionGlobal,
            conclusionOutside, older⟩)

end ActiveCarrierExternalReentryMarkedMateSeparatedTemporalTarget

namespace CanonicalTagHistory

private theorem CommitmentIntervalParTraceOutcome.mapOlderMateStatus
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
      membership eventAge childLt side beforeTrace afterTrace trace status =>
      exact .olderMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childLt side beforeTrace afterTrace trace
        (mapStatus status)

end CanonicalTagHistory

/-- In the strictly older Nop branch, normalize the marked target to a finite
continuation exit. -/
theorem NopStep.commitmentInterval_parTraceReentryMarkedContinuationExitOutcome
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (connected : certificate.ReferenceSwitchingConnected)
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (step : NopStep certificate before after)
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
          before.core.marks[step.consumer.mate]? = some none ∧
          ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply
    (step.commitmentInterval_parTraceReentryMarkedTemporalOutcome connected
      tagHistory invariant componentLookup occurrence positive firstAt lastAt
      noTail).mapOlderMateStatus
  intro status
  rcases status with ⟨mateOutside, mateUnmarked, target⟩
  exact ⟨mateOutside, mateUnmarked,
    ActiveCarrierExternalReentryMarkedMateSeparatedTemporalTarget.continuationExitTarget
        (tagHistory := tagHistory) (input := step.prepared.readyHeadInput)
        (component := component) (owned := owned) invariant step.consumer
        componentLookup occurrence target noTail⟩

/-- In the strictly older Wait branch, normalize the marked target to a finite
continuation exit. -/
theorem WaitStep.commitmentInterval_parTraceReentryMarkedContinuationExitOutcome
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
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
          ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply
    (step.commitmentInterval_parTraceReentryMarkedTemporalOutcome connected
      tagHistory invariant componentLookup occurrence positive firstAt lastAt
      noTail).mapOlderMateStatus
  intro status
  rcases status with
    ⟨mateOutside, mateMarked, representativeOlder, target⟩
  exact ⟨mateOutside, mateMarked, representativeOlder,
    ActiveCarrierExternalReentryMarkedMateSeparatedTemporalTarget.continuationExitTarget
        (tagHistory := tagHistory) (input := step.prepared.readyHeadInput)
        (component := component) (owned := owned) invariant step.consumer
        componentLookup occurrence target noTail⟩

end SequentialFigure7
end ProofNetIR
