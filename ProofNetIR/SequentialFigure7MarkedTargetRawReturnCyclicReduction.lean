/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParGuardReentryMarkedTargetContinuationExit

/-!
# Figure-7 marked-target raw-return cyclic reduction

An exact raw return splices a retained reference-switching prefix with the
strictly forward tail of its finite marked-conclusion chain. Cyclic immediate-
reverse normalization either removes the splice completely, exposing an exact
cyclic-segment junction when its two nonbacktracking parts were nonempty, or
leaves a nonbacktracking cycle.
Correctness forces every nonempty remainder to contain both premise-edge
occurrences of a par: the kept occurrence lies in the switching prefix, while
the omitted occurrence lies forward in the continuation tail and is sourced
at a concrete marked nonconclusion.

This module refines only the exact raw-return branch of the prior continuation
exit. It does not eliminate the empty/cancellation or par-pair residual, derive
a ready-tail witness or the history-tail law, or prove progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

private theorem connectiveForwardEdgeExists
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    ∃ directed : certificate.fullGraph.DirectedEdge,
      directed.source = vertex ∧
        directed.target = consumer.conclusion ∧
          directed.forward = true := by
  have linkMembership : consumer.submittedLink ∈ certificate.links :=
    List.mem_of_getElem? consumer.link_eq
  cases kindEq : consumer.kind with
  | par =>
      have parMembership :
          .par consumer.storedLeft consumer.storedRight
              consumer.conclusion ∈ certificate.links := by
        simpa [ConnectiveBelow.submittedLink,
          SequentialConnectiveKind.asLink, kindEq] using linkMembership
      rcases certificate.par_incidenceColors_exist parMembership with
        ⟨leftIncidence, rightIncidence, leftSource, leftTarget,
          rightSource, rightTarget, leftColor, rightColor⟩
      have leftForward : leftIncidence.forward = true :=
        (certificate.incidenceColor_eq_par_iff leftIncidence
          consumer.conclusion).mp leftColor |>.1
      have rightForward : rightIncidence.forward = true :=
        (certificate.incidenceColor_eq_par_iff rightIncidence
          consumer.conclusion).mp rightColor |>.1
      cases sideEq : consumer.side with
      | storedLeft =>
          have vertexEq : vertex = consumer.storedLeft := by
            simpa [TensorPremiseSide.premise, sideEq] using
              consumer.premise_eq
          exact ⟨leftIncidence, leftSource.trans vertexEq.symm,
            leftTarget, leftForward⟩
      | storedRight =>
          have vertexEq : vertex = consumer.storedRight := by
            simpa [TensorPremiseSide.premise, sideEq] using
              consumer.premise_eq
          exact ⟨rightIncidence, rightSource.trans vertexEq.symm,
            rightTarget, rightForward⟩

  | tensor =>
      have tensorMembership :
          .tensor consumer.storedLeft consumer.storedRight
              consumer.conclusion ∈ certificate.links := by
        simpa [ConnectiveBelow.submittedLink,
          SequentialConnectiveKind.asLink, kindEq] using linkMembership
      have tensorWellFormed :
          certificate.LinkWellFormed
            (.tensor consumer.storedLeft consumer.storedRight
              consumer.conclusion) := by
        simpa [SequentialConnectiveKind.asLink, kindEq] using
          consumer.wellFormed
      rcases certificate.tensor_incidenceColors_exist tensorMembership
          tensorWellFormed.1 with
        ⟨leftIncidence, rightIncidence, leftSource, leftTarget,
          rightSource, rightTarget, leftColor, rightColor, _different⟩
      have leftForward : leftIncidence.forward = true := by
        cases forwardEq : leftIncidence.forward with
        | false =>
            simp [Certificate.incidenceColor, forwardEq] at leftColor
        | true => rfl
      have rightForward : rightIncidence.forward = true := by
        cases forwardEq : rightIncidence.forward with
        | false =>
            simp [Certificate.incidenceColor, forwardEq] at rightColor
        | true => rfl
      cases sideEq : consumer.side with
      | storedLeft =>
          have vertexEq : vertex = consumer.storedLeft := by
            simpa [TensorPremiseSide.premise, sideEq] using
              consumer.premise_eq
          exact ⟨leftIncidence, leftSource.trans vertexEq.symm,
            leftTarget, leftForward⟩
      | storedRight =>
          have vertexEq : vertex = consumer.storedRight := by
            simpa [TensorPremiseSide.premise, sideEq] using
              consumer.premise_eq
          exact ⟨rightIncidence, rightSource.trans vertexEq.symm,
            rightTarget, rightForward⟩

private theorem connectivePremiseComplexityLtConclusion
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    certificate.formulaComplexityAt vertex <
      certificate.formulaComplexityAt consumer.conclusion := by
  have premiseMembership : vertex ∈ consumer.submittedLink.premises := by
    rcases consumer with
      ⟨linkIndex, kind, storedLeft, storedRight, conclusion, side,
        consumerEq, linkEq, wellFormed, premiseEq⟩
    subst vertex
    cases kind <;> cases side <;>
      simp [ConnectiveBelow.submittedLink,
        SequentialConnectiveKind.asLink, Link.premises,
        TensorPremiseSide.premise]
  have strict :=
    consumer.wellFormed.premise_complexity_lt_conclusion premiseMembership
  cases kindEquation : consumer.kind <;>
    simpa [Certificate.linkConclusionComplexity,
      SequentialConnectiveKind.asLink, kindEquation] using strict

private theorem MarkedConclusionChain.forwardWalk_exists
    {certificate : Certificate} {state : ReservationState}
    {origin terminal : Vertex} {originAge : RawTokenAge}
    (chain : MarkedConclusionChain certificate state origin terminal)
    (originMarked : state.core.marks[origin]? = some (some originAge))
    (originNotConclusion : origin ∉ certificate.conclusions) :
    ∃ traversed : List certificate.fullGraph.DirectedEdge,
      certificate.fullGraph.EdgeWalk origin traversed terminal ∧
        (∀ directed ∈ traversed, directed.forward = true) ∧
          (∀ directed ∈ traversed,
            certificate.formulaComplexityAt origin <
              certificate.formulaComplexityAt directed.target) ∧
            (traversed.map Graph.DirectedEdge.target).Nodup ∧
              ∀ directed ∈ traversed,
                ∃ rawAge,
                  state.core.marks[directed.source]? =
                      some (some rawAge) ∧
                    directed.source ∉ certificate.conclusions := by
  induction chain generalizing originAge with
  | refl vertex =>
      exact ⟨[], .refl vertex, by simp, by simp, by simp, by simp⟩
  | @step vertex terminal rawAge consumer marked notConclusion tail ih =>
      rcases connectiveForwardEdgeExists consumer with
        ⟨directed, starts, finishes, forward⟩
      rcases ih marked notConclusion with
        ⟨rest, restWalk, restForward, restGreater, restTargetNodup,
          restSources⟩
      have firstStrict := connectivePremiseComplexityLtConclusion consumer
      have firstWalk :
          certificate.fullGraph.EdgeWalk vertex [directed]
            consumer.conclusion := by
        exact Graph.EdgeWalk.step (.refl vertex) directed starts finishes
      refine ⟨directed :: rest, ?_, ?_, ?_, ?_, ?_⟩
      · simpa using firstWalk.trans restWalk
      · intro candidate membership
        simp only [List.mem_cons] at membership
        rcases membership with rfl | inRest
        · exact forward
        · exact restForward candidate inRest
      · intro candidate membership
        simp only [List.mem_cons] at membership
        rcases membership with rfl | inRest
        · simpa [finishes] using firstStrict
        · exact Nat.lt_trans firstStrict (restGreater candidate inRest)
      · simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, restTargetNodup⟩
        intro firstInRest
        rcases List.mem_map.mp firstInRest with
          ⟨candidate, candidateMembership, sameTarget⟩
        have strict := restGreater candidate candidateMembership
        rw [sameTarget, finishes] at strict
        omega
      · intro candidate membership
        simp only [List.mem_cons] at membership
        rcases membership with rfl | inRest
        · exact ⟨originAge, by simpa [starts] using originMarked,
            by simpa [starts] using originNotConclusion⟩
        · exact restSources candidate inRest

private theorem connectiveBelowConclusionEq
    {certificate : Certificate} {vertex : Vertex}
    (left right : ConnectiveBelow certificate vertex) :
    left.conclusion = right.conclusion := by
  have sameIndex : left.linkIndex = right.linkIndex :=
    Option.some.inj (left.consumer_eq.symm.trans right.consumer_eq)
  have leftLookup := left.link_eq
  rw [sameIndex] at leftLookup
  have sameLink :
      left.kind.asLink left.storedLeft left.storedRight left.conclusion =
        right.kind.asLink right.storedLeft right.storedRight right.conclusion :=
    Option.some.inj (leftLookup.symm.trans right.link_eq)
  cases leftKind : left.kind <;> cases rightKind : right.kind <;>
    simp [SequentialConnectiveKind.asLink, leftKind, rightKind] at sameLink
  · exact sameLink.2.2
  · exact sameLink.2.2

private theorem MarkedConclusionChain.rawReturnClosedWalk_exists
    {certificate : Certificate} {state : ReservationState}
    {base origin : Vertex}
    (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (pathStart : path.start = base)
    (directed : certificate.referenceSwitchingGraph.DirectedEdge)
    (directedMembership : directed ∈ path.traversed)
    (targetConsumer : ConnectiveBelow certificate origin)
    (sourceConsumer : directed.source = targetConsumer.conclusion)
    (originNeBase : origin ≠ base)
    (chain : MarkedConclusionChain certificate state origin base) :
    ∃ (retainedPrefix continuationTail :
        List certificate.fullGraph.DirectedEdge),
      certificate.fullGraph.EdgeWalk base retainedPrefix
          targetConsumer.conclusion ∧
        certificate.fullGraph.EdgeWalk targetConsumer.conclusion
          continuationTail base ∧
          certificate.fullGraph.EdgeWalk base
            (retainedPrefix ++ continuationTail) base ∧
          (∀ candidate ∈ retainedPrefix,
            certificate.referenceSwitchingMask[candidate.index]? = some true) ∧
            (∀ candidate ∈ continuationTail, candidate.forward = true) ∧
              (continuationTail.map Graph.DirectedEdge.target).Nodup ∧
                (∀ candidate ∈ continuationTail,
                  ∃ rawAge,
                    state.core.marks[candidate.source]? =
                        some (some rawAge) ∧
                      candidate.source ∉ certificate.conclusions) ∧
                Graph.EdgeWalk.NoImmediateReverse retainedPrefix ∧
                  Graph.EdgeWalk.NoImmediateReverse continuationTail ∧
                    (retainedPrefix = [] ↔
                      base = targetConsumer.conclusion) ∧
                      (continuationTail = [] ↔
                        targetConsumer.conclusion = base) := by
  rcases List.mem_iff_append.mp directedMembership with
    ⟨before, after, traversalEq⟩
  rcases path.prefixBefore traversalEq with
    ⟨initialPath, prefixStart, prefixFinish, prefixTraversed⟩
  have aligned :
      certificate.fullGraph.edges.length =
        certificate.referenceSwitchingMask.length := by
    change (Certificate.linkFullEdges certificate.links).length =
      certificate.referenceSwitchingMask.length
    exact certificate.referenceFullSwitchingSelection.mask_length.symm
  have retainedPrefixWalk :
      (certificate.fullGraph.retainEdges
        certificate.referenceSwitchingMask).EdgeWalk
          base before directed.source := by
    have prefixWalk := initialPath.walk
    rw [pathStart] at prefixStart
    rw [prefixStart, prefixFinish, prefixTraversed] at prefixWalk
    simpa [Certificate.referenceSwitchingGraph] using prefixWalk
  rcases retainedPrefixWalk.inflateRetained aligned with
    ⟨fullPrefix, fullPrefixWalk, indexEquation, _targets, allKept⟩
  have fullPrefixReduced :
      Graph.EdgeWalk.NoImmediateReverse fullPrefix := by
    have compactNodup :
        (fullPrefix.map (fun candidate =>
          Graph.retainedIndex certificate.referenceSwitchingMask
            candidate.index)).Nodup := by
      rw [indexEquation]
      rw [← prefixTraversed]
      exact initialPath.edgeIndicesNodup
    exact Graph.EdgeWalk.NoImmediateReverse.of_map_nodup
      (fun candidate =>
        Graph.retainedIndex certificate.referenceSwitchingMask
          candidate.index)
      (by
        intro candidate
        simp [Graph.DirectedEdge.reverse]) compactNodup
  cases chain with
  | refl vertex =>
      exact False.elim (originNeBase rfl)
  | @step vertex terminal rawAge first marked notConclusion tail =>
      have firstConclusion : first.conclusion = directed.source := by
        exact (connectiveBelowConclusionEq first targetConsumer).trans
          sourceConsumer.symm
      rcases tail.forwardWalk_exists marked notConclusion with
        ⟨fullTail, fullTailWalk, allForward, tailGreater, tailTargetNodup,
          tailSources⟩
      have fullTailWalk' :
          certificate.fullGraph.EdgeWalk targetConsumer.conclusion
            fullTail base := by
        simpa [firstConclusion, sourceConsumer] using fullTailWalk
      have fullPrefixWalk' :
          certificate.fullGraph.EdgeWalk base fullPrefix
            targetConsumer.conclusion := by
        simpa [sourceConsumer] using fullPrefixWalk
      have fullTailGreater :
          ∀ candidate ∈ fullTail,
            certificate.formulaComplexityAt targetConsumer.conclusion <
              certificate.formulaComplexityAt candidate.target := by
        simpa [firstConclusion, sourceConsumer] using tailGreater
      have fullTailReduced :
          Graph.EdgeWalk.NoImmediateReverse fullTail :=
        Graph.EdgeWalk.NoImmediateReverse.of_constant_forward allForward
      have fullPrefixEmpty :
          fullPrefix = [] ↔ base = targetConsumer.conclusion := by
        constructor
        · intro empty
          have prefixChain := fullPrefixWalk'.toChain
          rw [empty] at prefixChain
          cases prefixChain
          rfl
        · intro endpoints
          have beforeEmpty : before = [] := by
            by_cases empty : before = []
            · exact empty
            · have initialNonempty : initialPath.traversed ≠ [] := by
                simpa [prefixTraversed] using empty
              have different :=
                initialPath.start_ne_finish_of_nonempty initialNonempty
              have sameEndpoints :
                  initialPath.start = initialPath.finish := by
                calc
                  initialPath.start = path.start := prefixStart
                  _ = base := pathStart
                  _ = targetConsumer.conclusion := endpoints
                  _ = directed.source := sourceConsumer.symm
                  _ = initialPath.finish := prefixFinish.symm
              exact False.elim (different sameEndpoints)
          have lengthEquation := congrArg List.length indexEquation
          simp [beforeEmpty] at lengthEquation
          exact List.eq_nil_of_length_eq_zero lengthEquation
      have fullTailEmpty :
          fullTail = [] ↔ targetConsumer.conclusion = base := by
        constructor
        · intro empty
          have tailChain := fullTailWalk'.toChain
          rw [empty] at tailChain
          cases tailChain
          rfl
        · intro endpoints
          by_cases empty : fullTail = []
          · exact empty
          · have lastMembership : fullTail.getLast empty ∈ fullTail :=
              List.getLast_mem empty
            have lastTarget := fullTailWalk'.getLast_target empty
            have strict := fullTailGreater (fullTail.getLast empty)
              lastMembership
            rw [endpoints, lastTarget] at strict
            exact False.elim (Nat.lt_irrefl _ strict)
      exact ⟨fullPrefix, fullTail, fullPrefixWalk', fullTailWalk',
        fullPrefixWalk'.trans fullTailWalk', allKept, allForward,
        tailTargetNodup, tailSources, fullPrefixReduced, fullTailReduced,
        fullPrefixEmpty, fullTailEmpty⟩

/-- Cyclic normalization of one raw-return continuation splice. The retained
prefix comes from the reference switching; the continuation tail is forward
and has no repeated target. Complete cancellation records either the genuinely
empty splice or a concrete cancellation site. Otherwise, correctness exposes
the kept and omitted premise occurrences of a par, with the omitted occurrence
forced into the continuation tail. -/
def MarkedConclusionRawReturnCyclicOutcome
    (certificate : Certificate) (base source : Vertex) : Prop :=
    ∃ (retainedPrefix continuationTail :
          List certificate.fullGraph.DirectedEdge)
        (normalizedBase : Vertex)
        (reduced : List certificate.fullGraph.DirectedEdge),
      certificate.fullGraph.EdgeWalk base
          retainedPrefix source ∧
        certificate.fullGraph.EdgeWalk source
          continuationTail base ∧
          certificate.fullGraph.EdgeWalk base
            (retainedPrefix ++ continuationTail) base ∧
          (∀ candidate ∈ retainedPrefix,
            certificate.referenceSwitchingMask[candidate.index]? = some true) ∧
            (∀ candidate ∈ continuationTail, candidate.forward = true) ∧
              (continuationTail.map Graph.DirectedEdge.target).Nodup ∧
              certificate.fullGraph.EdgeWalk normalizedBase reduced normalizedBase ∧
              Graph.EdgeWalk.CyclicImmediateReverseNormalization
                (retainedPrefix ++ continuationTail) reduced ∧
              ((reduced = [] ∧
                  ((retainedPrefix = [] ∧ continuationTail = []) ∨
                    Graph.EdgeWalk.CyclicImmediateReverseSite
                      (retainedPrefix ++ continuationTail))) ∨
            ∃ (before : List Link) (left right conclusion : Vertex)
                (after : List Link)
                (leftOccurrence rightOccurrence :
                  certificate.fullGraph.DirectedEdge),
              certificate.links =
                  before ++ .par left right conclusion :: after ∧
                leftOccurrence ∈ reduced ∧
                  leftOccurrence.index =
                    (Certificate.linkFullEdges before).length ∧
                    leftOccurrence.edge =
                      { first := left, second := conclusion } ∧
                      certificate.referenceSwitchingMask[
                        leftOccurrence.index]? = some true ∧
                        rightOccurrence ∈ reduced ∧
                          rightOccurrence.index =
                            (Certificate.linkFullEdges before).length + 1 ∧
                            rightOccurrence.edge =
                              { first := right, second := conclusion } ∧
                              certificate.referenceSwitchingMask[
                                rightOccurrence.index]? = some false ∧
                                leftOccurrence ∈ retainedPrefix ∧
                                rightOccurrence ∈ continuationTail ∧
                                  rightOccurrence.forward = true)

/-- Splice the retained prefix before an inbound re-entry edge with the
continuation chain after its first parent edge, then normalize the resulting
closed full-graph walk. -/
theorem MarkedConclusionChain.rawReturnCyclicReduction
    {certificate : Certificate} {state : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    {base origin : Vertex}
    (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (pathStart : path.start = base)
    (directed : certificate.referenceSwitchingGraph.DirectedEdge)
    (directedMembership : directed ∈ path.traversed)
    (targetConsumer : ConnectiveBelow certificate origin)
    (sourceConsumer : directed.source = targetConsumer.conclusion)
    (originNeBase : origin ≠ base)
    (chain : MarkedConclusionChain certificate state origin base) :
    MarkedConclusionRawReturnCyclicOutcome certificate base
      targetConsumer.conclusion := by
  rcases chain.rawReturnClosedWalk_exists path pathStart directed
      directedMembership targetConsumer sourceConsumer originNeBase with
    ⟨retainedPrefix, continuationTail, prefixWalk, tailWalk, closedWalk,
      allKept, allForward, tailTargetNodup, _tailSources,
      _prefixReduced, _tailReduced,
      _prefixEmpty, _tailEmpty⟩
  let traversed := retainedPrefix ++ continuationTail
  rcases closedWalk.normalizeCyclicImmediateReversalsTraced traversed with
    ⟨normalizedBase, reduced, reducedWalk, normalization, reducedShape⟩
  refine ⟨retainedPrefix, continuationTail, normalizedBase, reduced,
    prefixWalk, tailWalk, closedWalk, allKept, allForward, tailTargetNodup,
    reducedWalk, normalization, ?_⟩
  by_cases reducedEmpty : reduced = []
  · refine Or.inl ⟨reducedEmpty, ?_⟩
    by_cases traversedEmpty : retainedPrefix ++ continuationTail = []
    · exact Or.inl (List.append_eq_nil_iff.mp traversedEmpty)
    · exact Or.inr
        (normalization.site_of_nonempty_normalizes_to_nil
          traversedEmpty reducedEmpty)
  · rcases correct.cyclicNoImmediateReverse_uses_bothParOccurrences
        reducedEmpty reducedWalk (reducedShape.resolve_left reducedEmpty) with
      ⟨before, left, right, conclusion, after,
        leftOccurrence, rightOccurrence, linksEq,
        leftMembership, leftIndex, leftEdge, leftKept,
        rightMembership, rightIndex, rightEdge, rightOmitted⟩
    have rightInTraversal :
        rightOccurrence ∈ retainedPrefix ++ continuationTail := by
      exact normalization.membership_subset rightOccurrence rightMembership
    have rightInTail : rightOccurrence ∈ continuationTail := by
      rcases List.mem_append.mp rightInTraversal with inPrefix | inTail
      · have kept := allKept rightOccurrence inPrefix
        rw [rightOmitted] at kept
        contradiction
      · exact inTail
    have leftInTraversal :
        leftOccurrence ∈ retainedPrefix ++ continuationTail := by
      exact normalization.membership_subset leftOccurrence leftMembership
    have leftInPrefix : leftOccurrence ∈ retainedPrefix := by
      rcases List.mem_append.mp leftInTraversal with inPrefix | inTail
      · exact inPrefix
      · have leftForward := allForward leftOccurrence inTail
        have rightForward := allForward rightOccurrence rightInTail
        have sameTarget : leftOccurrence.target = rightOccurrence.target := by
          simp [Graph.DirectedEdge.target, leftEdge, rightEdge,
            leftForward, rightForward]
        have sameOccurrence :=
          Graph.eq_of_map_eq_of_mem_of_nodup tailTargetNodup inTail rightInTail
            sameTarget
        have sameIndex := congrArg Graph.DirectedEdge.index sameOccurrence
        rw [leftIndex, rightIndex] at sameIndex
        omega
    exact Or.inr ⟨before, left, right, conclusion, after,
      leftOccurrence, rightOccurrence, linksEq,
      leftMembership, leftIndex, leftEdge, leftKept,
      rightMembership, rightIndex, rightEdge, rightOmitted,
      leftInPrefix, rightInTail, allForward rightOccurrence rightInTail⟩

/-- Cyclic normalization with the complete-cancellation branch localized to
the exact junction of the retained prefix and forward continuation tail. -/
def MarkedConclusionRawReturnCyclicJunctionOutcome
    (certificate : Certificate) (state : ReservationState)
    (base source : Vertex) : Prop :=
    ∃ (retainedPrefix continuationTail :
          List certificate.fullGraph.DirectedEdge)
        (normalizedBase : Vertex)
        (reduced : List certificate.fullGraph.DirectedEdge),
      certificate.fullGraph.EdgeWalk base
          retainedPrefix source ∧
        certificate.fullGraph.EdgeWalk source
          continuationTail base ∧
          certificate.fullGraph.EdgeWalk base
            (retainedPrefix ++ continuationTail) base ∧
          (∀ candidate ∈ retainedPrefix,
            certificate.referenceSwitchingMask[candidate.index]? = some true) ∧
            (∀ candidate ∈ continuationTail, candidate.forward = true) ∧
              (continuationTail.map Graph.DirectedEdge.target).Nodup ∧
              Graph.EdgeWalk.NoImmediateReverse retainedPrefix ∧
              Graph.EdgeWalk.NoImmediateReverse continuationTail ∧
                certificate.fullGraph.EdgeWalk normalizedBase reduced normalizedBase ∧
                Graph.EdgeWalk.CyclicImmediateReverseNormalization
                  (retainedPrefix ++ continuationTail) reduced ∧
              ((reduced = [] ∧
                  ((retainedPrefix = [] ∧ continuationTail = []) ∨
                    (retainedPrefix ≠ [] ∧
                      continuationTail ≠ [] ∧
                      Graph.EdgeWalk.CyclicSegmentJunctionReverse
                        [retainedPrefix, continuationTail]))) ∨
            ∃ (before : List Link) (left right conclusion : Vertex)
                (after : List Link)
                (leftOccurrence rightOccurrence :
                  certificate.fullGraph.DirectedEdge),
              certificate.links =
                  before ++ .par left right conclusion :: after ∧
                leftOccurrence ∈ reduced ∧
                  leftOccurrence.index =
                    (Certificate.linkFullEdges before).length ∧
                    leftOccurrence.edge =
                      { first := left, second := conclusion } ∧
                      certificate.referenceSwitchingMask[
                        leftOccurrence.index]? = some true ∧
                        rightOccurrence ∈ reduced ∧
                          rightOccurrence.index =
                            (Certificate.linkFullEdges before).length + 1 ∧
                            rightOccurrence.edge =
                              { first := right, second := conclusion } ∧
                              certificate.referenceSwitchingMask[
                                rightOccurrence.index]? = some false ∧
                                leftOccurrence ∈ retainedPrefix ∧
                                rightOccurrence ∈ continuationTail ∧
                                  rightOccurrence.forward = true ∧
                                    ∃ rightRawAge,
                                      state.core.marks[right]? =
                                          some (some rightRawAge) ∧
                                        right ∉ certificate.conclusions)

/-- Refine complete raw-return cancellation to an exact cyclic junction
between the two individually nonbacktracking splice segments. -/
theorem MarkedConclusionChain.rawReturnCyclicJunctionReduction
    {certificate : Certificate} {state : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    {base origin : Vertex}
    (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (pathStart : path.start = base)
    (directed : certificate.referenceSwitchingGraph.DirectedEdge)
    (directedMembership : directed ∈ path.traversed)
    (targetConsumer : ConnectiveBelow certificate origin)
    (sourceConsumer : directed.source = targetConsumer.conclusion)
    (originNeBase : origin ≠ base)
    (chain : MarkedConclusionChain certificate state origin base) :
    MarkedConclusionRawReturnCyclicJunctionOutcome certificate state base
      targetConsumer.conclusion := by
  rcases chain.rawReturnClosedWalk_exists path pathStart directed
      directedMembership targetConsumer sourceConsumer originNeBase with
    ⟨retainedPrefix, continuationTail, prefixWalk, tailWalk, closedWalk,
      allKept, allForward, tailTargetNodup, tailSources,
      prefixReduced, tailReduced,
      prefixEmpty, tailEmpty⟩
  let traversed := retainedPrefix ++ continuationTail
  rcases closedWalk.normalizeCyclicImmediateReversalsTraced traversed with
    ⟨normalizedBase, reduced, reducedWalk, normalization, reducedShape⟩
  refine ⟨retainedPrefix, continuationTail, normalizedBase, reduced,
    prefixWalk, tailWalk, closedWalk, allKept, allForward, tailTargetNodup,
    prefixReduced, tailReduced, reducedWalk, normalization, ?_⟩
  by_cases reducedEmpty : reduced = []
  · refine Or.inl ⟨reducedEmpty, ?_⟩
    by_cases prefixIsEmpty : retainedPrefix = []
    · have tailIsEmpty : continuationTail = [] := by
        apply tailEmpty.mpr
        exact (prefixEmpty.mp prefixIsEmpty).symm
      exact Or.inl ⟨prefixIsEmpty, tailIsEmpty⟩
    · have tailNonempty : continuationTail ≠ [] := by
        intro tailIsEmpty
        apply prefixIsEmpty
        apply prefixEmpty.mpr
        exact (tailEmpty.mp tailIsEmpty).symm
      have site :
          Graph.EdgeWalk.CyclicImmediateReverseSite
            (retainedPrefix ++ continuationTail) :=
        normalization.site_of_nonempty_normalizes_to_nil
          (by
            intro empty
            exact prefixIsEmpty (List.append_eq_nil_iff.mp empty).1)
          reducedEmpty
      have junction :
          Graph.EdgeWalk.CyclicSegmentJunctionReverse
            [retainedPrefix, continuationTail] := by
        apply Graph.EdgeWalk.CyclicImmediateReverseSite.segmentJunction_of_flatten
          (segments := [retainedPrefix, continuationTail])
        · simp
        · intro segment membership
          simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
          rcases membership with rfl | rfl
          · exact prefixIsEmpty
          · exact tailNonempty
        · intro segment membership
          simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
          rcases membership with rfl | rfl
          · exact prefixReduced
          · exact tailReduced
        · simpa using site
      exact Or.inr ⟨prefixIsEmpty, tailNonempty, junction⟩
  · rcases correct.cyclicNoImmediateReverse_uses_bothParOccurrences
        reducedEmpty reducedWalk (reducedShape.resolve_left reducedEmpty) with
      ⟨before, left, right, conclusion, after,
        leftOccurrence, rightOccurrence, linksEq,
        leftMembership, leftIndex, leftEdge, leftKept,
        rightMembership, rightIndex, rightEdge, rightOmitted⟩
    have rightInTraversal :
        rightOccurrence ∈ retainedPrefix ++ continuationTail :=
      normalization.membership_subset rightOccurrence rightMembership
    have rightInTail : rightOccurrence ∈ continuationTail := by
      rcases List.mem_append.mp rightInTraversal with inPrefix | inTail
      · have kept := allKept rightOccurrence inPrefix
        rw [rightOmitted] at kept
        contradiction
      · exact inTail
    have leftInTraversal :
        leftOccurrence ∈ retainedPrefix ++ continuationTail :=
      normalization.membership_subset leftOccurrence leftMembership
    have leftInPrefix : leftOccurrence ∈ retainedPrefix := by
      rcases List.mem_append.mp leftInTraversal with inPrefix | inTail
      · exact inPrefix
      · have leftForward := allForward leftOccurrence inTail
        have rightForward := allForward rightOccurrence rightInTail
        have sameTarget : leftOccurrence.target = rightOccurrence.target := by
          simp [Graph.DirectedEdge.target, leftEdge, rightEdge,
            leftForward, rightForward]
        have sameOccurrence :=
          Graph.eq_of_map_eq_of_mem_of_nodup tailTargetNodup inTail rightInTail
            sameTarget
        have sameIndex := congrArg Graph.DirectedEdge.index sameOccurrence
        rw [leftIndex, rightIndex] at sameIndex
        omega
    have rightForward := allForward rightOccurrence rightInTail
    rcases tailSources rightOccurrence rightInTail with
      ⟨rightRawAge, rightSourceMarked, rightSourceNotConclusion⟩
    have rightSource : rightOccurrence.source = right := by
      simp [Graph.DirectedEdge.source, rightEdge, rightForward]
    have rightMarked :
        state.core.marks[right]? = some (some rightRawAge) := by
      simpa [rightSource] using rightSourceMarked
    have rightNotConclusion : right ∉ certificate.conclusions := by
      simpa [rightSource] using rightSourceNotConclusion
    exact Or.inr ⟨before, left, right, conclusion, after,
      leftOccurrence, rightOccurrence, linksEq,
      leftMembership, leftIndex, leftEdge, leftKept,
      rightMembership, rightIndex, rightEdge, rightOmitted,
      leftInPrefix, rightInTail, rightForward,
      rightRawAge, rightMarked, rightNotConclusion⟩

/-- Refine only the exact raw-return branch of the marked target continuation
exit. Raw work outside the carrier and the older future or marked-global exits
are retained unchanged. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCyclicReductionTarget
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
                    certificate.formulaComplexityAt terminal ∧
                  MarkedConclusionRawReturnCyclicOutcome certificate
                    current.mate targetConsumer.conclusion))) ∨
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

/-- Refine the exact raw-return branch through the two nonbacktracking splice
segments. Complete cancellation is localized to their cyclic junction, while
a surviving omitted-right par occurrence is a concrete marked nonconclusion
source in the continuation tail. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCyclicJunctionTarget
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
                    certificate.formulaComplexityAt terminal ∧
                  MarkedConclusionRawReturnCyclicJunctionOutcome certificate
                    state current.mate targetConsumer.conclusion))) ∨
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

namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget

/-- Refine the exact raw-return branch into its cyclic cancellation/par-pair
normal form. -/
theorem continuationCyclicReductionTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (correct : certificate.DeclarativelyCorrect)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCyclicReductionTarget
      tagHistory input component owned current := by
  rcases target with
    ⟨path, directed, markedAge, pathStart, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetNeMate, targetMarked, authentic,
      representativeEq, targetConsumer, targetConsumerMateNeSelected,
      sourceConsumer, targetConclusionOutside, status⟩
  refine ⟨path, directed, markedAge, pathStart, finishOwned,
    directedMembership, parentEdge, targetNeSelected, targetNeMate,
    targetMarked, authentic, representativeEq, targetConsumer,
    targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside, ?_⟩
  rcases status with raw | future | marked
  · rcases raw with
      ⟨terminal, chain, terminalConsumer, mateUnmarked,
        mateOutside | exactReturn⟩
    · exact Or.inl ⟨terminal, chain, terminalConsumer, mateUnmarked,
        Or.inl mateOutside⟩
    · rcases exactReturn with
        ⟨mateSelected, terminalEq, conclusionEq, complexityLt⟩
      subst terminal
      have cycleOutcome := chain.rawReturnCyclicReduction correct path
        pathStart directed directedMembership targetConsumer sourceConsumer
        targetNeMate
      exact Or.inl ⟨current.mate, chain, terminalConsumer, mateUnmarked,
        Or.inr ⟨mateSelected, rfl, conclusionEq, complexityLt,
          cycleOutcome⟩⟩
  · exact Or.inr (Or.inl future)
  · exact Or.inr (Or.inr marked)

end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget

namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCyclicReductionTarget

/-- Refine the exact raw-return branch to the cyclic-junction form and retain
the other three continuation exits unchanged. -/
theorem cyclicJunctionTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (correct : certificate.DeclarativelyCorrect)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCyclicReductionTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCyclicJunctionTarget
      tagHistory input component owned current := by
  rcases target with
    ⟨path, directed, markedAge, pathStart, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetNeMate, targetMarked, authentic,
      representativeEq, targetConsumer, targetConsumerMateNeSelected,
      sourceConsumer, targetConclusionOutside, status⟩
  refine ⟨path, directed, markedAge, pathStart, finishOwned,
    directedMembership, parentEdge, targetNeSelected, targetNeMate,
    targetMarked, authentic, representativeEq, targetConsumer,
    targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside, ?_⟩
  rcases status with raw | future | marked
  · rcases raw with
      ⟨terminal, chain, terminalConsumer, mateUnmarked,
        mateOutside | exactReturn⟩
    · exact Or.inl ⟨terminal, chain, terminalConsumer, mateUnmarked,
        Or.inl mateOutside⟩
    · rcases exactReturn with
        ⟨mateSelected, terminalEq, conclusionEq, complexityLt,
          _cyclicOutcome⟩
      subst terminal
      have junctionOutcome := chain.rawReturnCyclicJunctionReduction correct path
        pathStart directed directedMembership targetConsumer sourceConsumer
        targetNeMate
      exact Or.inl ⟨current.mate, chain, terminalConsumer, mateUnmarked,
        Or.inr ⟨mateSelected, rfl, conclusionEq, complexityLt,
          junctionOutcome⟩⟩
  · exact Or.inr (Or.inl future)
  · exact Or.inr (Or.inr marked)

end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCyclicReductionTarget

end SequentialFigure7
end ProofNetIR
