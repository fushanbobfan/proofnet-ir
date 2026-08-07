import ProofNetIR.SequentialFigure7ReservationLedger

namespace ProofNetIR

/-!
# Final realization of canonical Figure-7 reservations

This proof-only layer follows every chronological reservation event through
the already certified dispatcher history to the live component at the event's
current union-find representative.  Raw ages remain immutable allocation
identifiers; they are never identified with current representatives or live
component slots.
-/

namespace CutFreeDerivation

private theorem perm_of_nodup_subset_length [BEq α] [LawfulBEq α]
    {left right : List α}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (subset : left ⊆ right) (sameLength : left.length = right.length) :
    left.Perm right := by
  induction left generalizing right with
  | nil =>
      have : right = [] := List.eq_nil_of_length_eq_zero sameLength.symm
      subst right
      exact .refl []
  | cons head tail ih =>
      have headMembership : head ∈ right := subset (by simp)
      have tailNodup := (List.nodup_cons.mp leftNodup).2
      have headFresh := (List.nodup_cons.mp leftNodup).1
      have erasedNodup := rightNodup.erase head
      have tailSubset : tail ⊆ right.erase head := by
        intro value membership
        apply (List.mem_erase_of_ne (b := head) (by
          intro same
          subst value
          exact headFresh membership)).mpr
        exact subset (by simp [membership])
      have tailLength : tail.length = (right.erase head).length := by
        rw [List.length_erase_of_mem headMembership]
        have totalLength : tail.length + 1 = right.length := by
          simpa [Nat.add_comm] using sameLength
        omega
      exact (ih tailNodup erasedNodup tailSubset tailLength).cons head |>.trans
        (List.perm_cons_erase headMembership).symm

private theorem mapM_getElem?_result_at
    {values : List α} {indices : List Nat} {result : List α}
    (equation :
      indices.mapM (fun index => values[index]?) = some result) :
    ∀ position : Nat,
      result[position]? =
        (indices[position]?).bind (fun index => values[index]?) := by
  induction indices generalizing result with
  | nil =>
      simp at equation
      subst result
      simp
  | cons index tail induction =>
      simp only [List.mapM_cons] at equation
      cases headLookup : values[index]? with
      | none => simp [headLookup] at equation
      | some head =>
          cases tailMap : tail.mapM (fun candidate => values[candidate]?) with
          | none => simp [headLookup, tailMap] at equation
          | some rest =>
              simp [headLookup, tailMap] at equation
              subst result
              intro position
              cases position with
              | zero => simp [headLookup]
              | succ prior =>
                  simp only [List.getElem?_cons_succ]
                  exact induction tailMap prior

/-- Removing the same occurrence at the same position with the same remainder
determines the original list, including when values are duplicated. -/
theorem pick?_source_unique
    {first second remaining : List α}
    {index : Nat} {selected : α}
    (firstPick : pick? first index = some (selected, remaining))
    (secondPick : pick? second index = some (selected, remaining)) :
    first = second := by
  induction index generalizing first second remaining with
  | zero =>
      cases first with
      | nil => simp [pick?] at firstPick
      | cons firstHead firstTail =>
          cases second with
          | nil => simp [pick?] at secondPick
          | cons secondHead secondTail =>
              simp [pick?] at firstPick secondPick
              rcases firstPick with ⟨rfl, rfl⟩
              rcases secondPick with ⟨rfl, rfl⟩
              rfl
  | succ prior induction =>
      cases first with
      | nil => simp [pick?] at firstPick
      | cons firstHead firstTail =>
          cases second with
          | nil => simp [pick?] at secondPick
          | cons secondHead secondTail =>
              simp only [pick?] at firstPick secondPick
              cases firstTailPick : pick? firstTail prior with
              | none => simp [firstTailPick] at firstPick
              | some firstResult =>
                  rcases firstResult with ⟨firstSelected, firstRemaining⟩
                  simp [firstTailPick] at firstPick
                  rcases firstPick with ⟨rfl, rfl⟩
                  cases secondTailPick : pick? secondTail prior with
                  | none => simp [secondTailPick] at secondPick
                  | some secondResult =>
                      rcases secondResult with
                        ⟨secondSelected, secondRemaining⟩
                      simp [secondTailPick] at secondPick
                      rcases secondPick with ⟨rfl, headEq, tailEq⟩
                      subst secondHead
                      subst secondRemaining
                      have tailSame := induction firstTailPick secondTailPick
                      simp [tailSame]

/-- A successful explicit occurrence permutation is injective in its source
when the order and result are fixed. -/
theorem reorder?_source_unique [DecidableEq α]
    {first second reordered : List α} {order : List Nat}
    (firstEquation : reorder? first order = some reordered)
    (secondEquation : reorder? second order = some reordered) :
    first = second := by
  have firstPerm := reorder?_perm firstEquation
  have secondPerm := reorder?_perm secondEquation
  have lengthEq : first.length = second.length := by
    calc
      first.length = reordered.length := firstPerm.length_eq
      _ = second.length := secondPerm.length_eq.symm
  have firstCandidate :
      reorderCandidate? first order = some reordered := by
    rw [← reorder?_eq_reorderCandidate?]
    exact firstEquation
  have secondCandidate :
      reorderCandidate? second order = some reordered := by
    rw [← reorder?_eq_reorderCandidate?]
    exact secondEquation
  unfold reorderCandidate? at firstCandidate secondCandidate
  split at firstCandidate
  next firstGuard =>
    split at secondCandidate
    next secondGuard =>
      have firstAt := mapM_getElem?_result_at firstCandidate
      have secondAt := mapM_getElem?_result_at secondCandidate
      apply List.ext_get
      · exact lengthEq
      · intro position firstBound secondBound
        have firstOrderParts :
            (order.length = first.length ∧
              order.eraseDups.length = order.length) ∧
              ∀ index ∈ order, index < first.length := by
          simpa [Bool.and_eq_true, List.all_eq_true] using firstGuard
        have orderNodup : order.Nodup :=
          nodup_of_eraseDups_length_eq firstOrderParts.1.2
        have orderSubset : order ⊆ List.range first.length := by
          intro index membership
          simp only [List.mem_range]
          exact firstOrderParts.2 index membership
        have orderPerm : order.Perm (List.range first.length) :=
          perm_of_nodup_subset_length orderNodup List.nodup_range
            orderSubset (by simpa using firstOrderParts.1.1)
        have positionInRange : position ∈ List.range first.length := by
          simp [firstBound]
        have positionInOrder : position ∈ order :=
          orderPerm.mem_iff.mpr positionInRange
        rcases List.mem_iff_getElem?.mp positionInOrder with
          ⟨outputPosition, orderAt⟩
        have firstResultAt := firstAt outputPosition
        have secondResultAt := secondAt outputPosition
        rw [orderAt] at firstResultAt secondResultAt
        simp only [Option.bind_some] at firstResultAt secondResultAt
        have lookups : first[position]? = second[position]? :=
          firstResultAt.symm.trans secondResultAt
        rw [List.getElem?_eq_getElem firstBound,
          List.getElem?_eq_getElem secondBound] at lookups
        exact Option.some.inj lookups
    next secondGuard => simp at secondCandidate
  next firstGuard => simp at firstCandidate

end CutFreeDerivation

namespace Certificate
namespace OccurrenceDerivation

private theorem mapM_result_length
    {values : List α} {result : List β} {function : α → Option β}
    (equation : values.mapM function = some result) :
    result.length = values.length := by
  induction values generalizing result with
  | nil =>
      simp at equation
      subst result
      rfl
  | cons head tail induction =>
      simp only [List.mapM_cons] at equation
      cases headResult : function head with
      | none => simp [headResult] at equation
      | some mappedHead =>
          cases tailResult : tail.mapM function with
          | none => simp [headResult, tailResult] at equation
          | some mappedTail =>
              simp [headResult, tailResult] at equation
              subst result
              simp [induction tailResult]

private theorem frontier_length_unique
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation}
    {firstFrontier secondFrontier
      firstUsed firstOwned secondUsed secondOwned : List Nat}
    (first :
      OccurrenceDerivation certificate tree firstFrontier firstUsed firstOwned)
    (second :
      OccurrenceDerivation certificate tree secondFrontier secondUsed secondOwned) :
    firstFrontier.length = secondFrontier.length := by
  rcases first.formulaConsistent structural with
    ⟨firstSequent, firstInference, firstMapping⟩
  rcases second.formulaConsistent structural with
    ⟨secondSequent, secondInference, secondMapping⟩
  have sequentEq : firstSequent = secondSequent :=
    Option.some.inj (firstInference.symm.trans secondInference)
  calc
    firstFrontier.length = firstSequent.length :=
      (mapM_result_length firstMapping).symm
    _ = secondSequent.length := by rw [sequentEq]
    _ = secondFrontier.length := mapM_result_length secondMapping

/-- Under structural resource ownership, the exact owned-occurrence list is
determined by a component's derivation tree and exact frontier.  Submitted
link lists need not be identified. -/
theorem owned_unique
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation}
    {frontier usedLinks₁ owned₁ usedLinks₂ owned₂ : List Nat}
    (first :
      OccurrenceDerivation certificate tree frontier usedLinks₁ owned₁)
    (second :
      OccurrenceDerivation certificate tree frontier usedLinks₂ owned₂) :
    owned₁ = owned₂ := by
  induction first generalizing usedLinks₂ owned₂ with
  | «axiom» =>
      cases second
      rfl
  | par premiseWitness linkIndex left right conclusion leftFocus rightFocus
      afterLeft context linkLookup leftPick rightPick induction =>
      generalize frontierEq : context ++ [conclusion] = target at second
      cases second with
      | par secondPremise secondIndex secondLeft secondRight secondConclusion
          secondLeftFocus secondRightFocus secondAfterLeft secondContext
          secondLookup secondLeftPick secondRightPick =>
          have totalLength := congrArg List.length frontierEq
          have contextLength : context.length = secondContext.length := by
            simp only [List.length_append, List.length_singleton] at totalLength
            omega
          have frontierParts := List.append_inj frontierEq contextLength
          have contextEq : context = secondContext := frontierParts.1
          have conclusionEq : conclusion = secondConclusion := by
            simpa using frontierParts.2
          have sameLink :
              Link.par left right conclusion =
                Link.par secondLeft secondRight secondConclusion :=
            UnificationState.StructurallyWellFormed.producerLink_unique
              (conclusion := conclusion) structural
              (List.mem_of_getElem? linkLookup) (by simp [Link.produces])
              (List.mem_of_getElem? secondLookup) (by
                simp [Link.produces, conclusionEq])
          injection sameLink with leftEq rightEq conclusionEq'
          subst secondLeft
          subst secondRight
          have secondRightPosition :
              CutFreeDerivation.pick? secondAfterLeft rightFocus =
                some (right, context) := by
            simpa [contextEq] using secondRightPick.positional
          have afterLeftEq : afterLeft = secondAfterLeft :=
            CutFreeDerivation.pick?_source_unique
              rightPick.positional secondRightPosition
          have secondLeftPosition := secondLeftPick.positional
          rw [← afterLeftEq] at secondLeftPosition
          have premiseFrontierEq : _ = _ :=
            CutFreeDerivation.pick?_source_unique
              leftPick.positional secondLeftPosition
          subst_vars
          simp [induction secondPremise]
      | _ => contradiction
  | tensor leftWitness rightWitness linkIndex left right conclusion
      leftFocus rightFocus leftContext rightContext linkLookup
      leftPick rightPick leftInduction rightInduction =>
      generalize frontierEq :
        conclusion :: (leftContext ++ rightContext) = target at second
      cases second with
      | tensor secondLeft secondRight secondIndex secondLeftVertex
          secondRightVertex secondConclusion secondLeftFocus secondRightFocus
          secondLeftContext secondRightContext secondLookup secondLeftPick
          secondRightPick =>
          have frontierParts := List.cons.inj frontierEq
          have conclusionEq : conclusion = secondConclusion := frontierParts.1
          have contextsEq :
              leftContext ++ rightContext =
                secondLeftContext ++ secondRightContext := frontierParts.2
          have sameLink :
              Link.tensor left right conclusion =
                Link.tensor secondLeftVertex secondRightVertex
                  secondConclusion :=
            UnificationState.StructurallyWellFormed.producerLink_unique
              (conclusion := conclusion) structural
              (List.mem_of_getElem? linkLookup) (by simp [Link.produces])
              (List.mem_of_getElem? secondLookup) (by
                simp [Link.produces, conclusionEq])
          injection sameLink with leftEq rightEq conclusionEq'
          subst secondLeftVertex
          subst secondRightVertex
          have leftFrontierLength :=
            frontier_length_unique structural leftWitness secondLeft
          have firstPickLength :=
            (CutFreeDerivation.pick?_perm leftPick.positional).length_eq
          have secondPickLength :=
            (CutFreeDerivation.pick?_perm
              secondLeftPick.positional).length_eq
          have leftContextLength :
              leftContext.length = secondLeftContext.length := by
            simp only [List.length_cons] at firstPickLength secondPickLength
            omega
          have contextParts :=
            List.append_inj contextsEq leftContextLength
          have secondLeftPosition := secondLeftPick.positional
          rw [← contextParts.1] at secondLeftPosition
          have secondRightPosition := secondRightPick.positional
          rw [← contextParts.2] at secondRightPosition
          have leftFrontierEq : _ = _ :=
            CutFreeDerivation.pick?_source_unique
              leftPick.positional secondLeftPosition
          have rightFrontierEq : _ = _ :=
            CutFreeDerivation.pick?_source_unique
              rightPick.positional secondRightPosition
          subst_vars
          simp [leftInduction secondLeft, rightInduction secondRight]
      | _ => contradiction
  | exchange premiseWitness order reordered reorderEquation induction =>
      generalize frontierEq : reordered = target at second
      cases second with
      | exchange secondPremise secondOrder secondReordered secondEquation =>
          have secondReorder := secondEquation
          rw [← frontierEq] at secondReorder
          have premiseFrontierEq : _ = _ :=
            CutFreeDerivation.reorder?_source_unique
              reorderEquation secondReorder
          subst_vars
          exact induction secondPremise
      | _ => contradiction

end OccurrenceDerivation
end Certificate

namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState
open SequentialUnification

namespace ReservationEvent

/-- Core-level form of chronological reservation realization. -/
private def RealizedInCore {certificate : Certificate}
    (event : ReservationEvent certificate)
    (core : UnificationState) : Prop :=
  ∃ component usedLinks owned,
    core.components[core.representative event.rawAge]? =
        some (some component) ∧
      certificate.OccurrenceDerivation component.tree component.frontier
        usedLinks owned ∧
      event.linkIndex ∈ usedLinks

/-- A chronological reservation is realized in a later scheduler state when
its exact submitted axiom slot occurs in an occurrence derivation for the
live component at the reservation's current union-find representative.

The derivation is event-specific proof data.  It deliberately carries no
local-linearity or cross-component forest witness; those are recovered from
the final `SchedulerInvariant` and aligned by `OccurrenceDerivation.owned_unique`.
-/
def RealizedIn {certificate : Certificate}
    (event : ReservationEvent certificate)
    (state : ReservationState) : Prop :=
  event.RealizedInCore state.core

/-- Transport an event realization across a production-state update that
preserves the parent forest and component carrier exactly. -/
private theorem realizedIn_of_core_observations_eq
    {certificate : Certificate} {event : ReservationEvent certificate}
    {before after : ReservationState}
    (realized : event.RealizedIn before)
    (parents : after.core.parents = before.core.parents)
    (components : after.core.components = before.core.components) :
    event.RealizedIn after := by
  rcases realized with ⟨component, usedLinks, owned,
    componentLookup, derivation, membership⟩
  refine ⟨component, usedLinks, owned, ?_, derivation, membership⟩
  unfold UnificationState.representative
  rw [parents, components]
  exact componentLookup

/-- The synchronized pop/raw-mark prefix preserves every earlier event's
realization exactly. -/
private theorem realizedIn_prepared
    {certificate : Certificate} {event : ReservationEvent certificate}
    {before : ReservationState}
    (realized : event.RealizedIn before)
    (prepared : PreparedStep before) :
    event.RealizedIn prepared.after := by
  have carriers :=
    UnificationState.markReadyRaw?_carriers prepared.core_mark_eq
  exact realizedIn_of_core_observations_eq realized carriers.1 carriers.2

/-- The exact initial reservation realizes its own chronological event. -/
private theorem initial_realized
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (step : InitialReservationStep certificate after start) :
    (ReservationEvent.initial step).RealizedIn after := by
  rcases certificate.reserveAxiomAt?_componentOccurrenceWitness
      structural step.core_eq with
    ⟨left, right, name, positive, exactLink, freshLookup, witness⟩
  have outputCore : after.core = step.coreAfter :=
    congrArg ReservationState.core step.output_eq
  have freshRepresentative :
      step.coreAfter.representative 0 = 0 := by
    simpa [ReservationState.empty, Certificate.initialUnificationState] using
      certificate.reserveAxiomAt?_fresh_representative step.core_eq
  refine ⟨{ tree := .axiom name positive, frontier := [left, right] },
    [step.result.linkIndex], [left, right], ?_, witness.derivation, ?_⟩
  · change after.core.components[
        after.core.representative
          (ReservationEvent.initial step).rawAge]? = _
    simp only [ReservationEvent.rawAge]
    rw [outputCore, freshRepresentative]
    simpa [ReservationState.empty, Certificate.initialUnificationState] using
      freshLookup
  · change step.result.linkIndex ∈ [step.result.linkIndex]
    simp

/-- Appending another axiom reservation preserves every already-realized
event through the unchanged old union-find class. -/
private theorem realizedIn_reserveAxiomAt
    {certificate : Certificate} {event : ReservationEvent certificate}
    {before after : ReservationState} {linkIndex : Nat}
    (realized : event.RealizedIn before)
    (ordered : before.core.OrderedParents)
    (equation :
      certificate.reserveAxiomAt? before.core linkIndex = some after.core) :
    event.RealizedIn after := by
  rcases realized with ⟨component, usedLinks, owned,
    componentLookup, derivation, membership⟩
  have beforeComponentAt :
      before.core.componentAt? event.rawAge = some component := by
    simp [UnificationState.componentAt?, componentLookup]
  have afterComponentAt :
      after.core.componentAt? event.rawAge = some component :=
    certificate.reserveAxiomAt?_componentAt?_of_some
      ordered equation beforeComponentAt
  refine ⟨component, usedLinks, owned,
    UnificationState.componentAt?_some_raw afterComponentAt,
    derivation, membership⟩

/-- A successful operational `new` realizes the fresh event allocated by
that exact transition. -/
private theorem new_realized
    {certificate : Certificate} {before after : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (step : NewStep certificate before after) :
    (ReservationEvent.new step).RealizedIn after := by
  rcases certificate.reserveAxiomAt?_componentOccurrenceWitness
      structural step.core_reserve_eq with
    ⟨left, right, name, positive, exactLink, freshLookup, witness⟩
  have outputCore : after.core = step.coreAfter :=
    congrArg ReservationState.core step.output_eq
  have carriers :=
    UnificationState.markReadyRaw?_carriers step.core_mark_eq
  have rawAgeEq :
      (ReservationEvent.new step).rawAge = step.coreMarked.parents.size := by
    change before.stack.nextAge = step.coreMarked.parents.size
    rw [← step.before_invariant.realizesSigma.horizon_eq, carriers.1]
  have markedInvariant := step.markedMiddle_reservationInvariant
  have markedAligned :
      step.coreMarked.components.size = step.coreMarked.parents.size := by
    simpa [NewStep.markedMiddle] using
      markedInvariant.core_carriers_aligned
  have componentAgeEq :
      step.coreMarked.components.size =
        (ReservationEvent.new step).rawAge := by
    rw [markedAligned, rawAgeEq]
  have freshRepresentative :
      step.coreAfter.representative (ReservationEvent.new step).rawAge =
        (ReservationEvent.new step).rawAge := by
    rw [rawAgeEq]
    exact certificate.reserveAxiomAt?_fresh_representative
      step.core_reserve_eq
  refine ⟨{ tree := .axiom name positive, frontier := [left, right] },
    [step.search.linkIndex], [left, right], ?_, witness.derivation, ?_⟩
  · rw [outputCore, freshRepresentative, ← componentAgeEq]
    exact freshLookup
  · change step.search.linkIndex ∈ [step.search.linkIndex]
    simp

/-- `concl` changes only the common prefix, so it preserves every earlier
reservation realization. -/
private theorem realizedIn_concl
    {certificate : Certificate} {event : ReservationEvent certificate}
    {before after : ReservationState}
    (realized : event.RealizedIn before)
    (step : ConclStep certificate before after) :
    event.RealizedIn after := by
  rw [step.output_eq]
  exact realizedIn_prepared realized step.prepared

/-- `nop` changes only the common prefix, so it preserves every earlier
reservation realization. -/
private theorem realizedIn_nop
    {certificate : Certificate} {event : ReservationEvent certificate}
    {before after : ReservationState}
    (realized : event.RealizedIn before)
    (step : NopStep certificate before after) :
    event.RealizedIn after := by
  rw [step.output_eq]
  exact realizedIn_prepared realized step.prepared

/-- `wait` changes only delayed waiting storage after the common prefix; its
production carrier therefore preserves every earlier realization. -/
private theorem realizedIn_wait
    {certificate : Certificate} {event : ReservationEvent certificate}
    {before after : ReservationState}
    (realized : event.RealizedIn before)
    (step : WaitStep certificate before after) :
    event.RealizedIn after := by
  have middle := realizedIn_prepared realized step.prepared
  rw [step.destination.output_eq]
  exact middle

/-- An operational `new` preserves every older event while appending its
fresh event. -/
private theorem realizedIn_new_old
    {certificate : Certificate} {event : ReservationEvent certificate}
    {before after : ReservationState}
    (realized : event.RealizedIn before)
    (step : NewStep certificate before after) :
    event.RealizedIn after := by
  have middle : event.RealizedIn step.markedMiddle := by
    exact realizedIn_prepared realized {
      stackResult := step.stackResult
      coreMarked := step.coreMarked
      stack_eq := step.stack_eq
      core_mark_eq := step.core_mark_eq }
  have reserveEquation :
      certificate.reserveAxiomAt? step.markedMiddle.core
          step.search.linkIndex = some after.core := by
    rw [show after.core = step.coreAfter from
      congrArg ReservationState.core step.output_eq]
    exact step.core_reserve_eq
  exact realizedIn_reserveAxiomAt middle
    step.markedMiddle_reservationInvariant.core_orderedParents
    reserveEquation

private theorem forward_active_root
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.coreMarked.representative step.queueStep.outputToken =
      step.queueStep.outputToken := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  rcases SequentialStackState.popReadyMark?_exact step.prepared.stack_eq with
    ⟨_, sigmaTop, _, _, _, sigmaEq, _, _, selectedMarked⟩
  have middleTop :
      step.prepared.after.stack.sigma.getLast? =
        some step.prepared.stackResult.rawAge := by
    change step.prepared.stackResult.after.sigma.getLast? = _
    rw [sigmaEq]
    exact sigmaTop
  have rawBound :
      step.prepared.stackResult.rawAge <
        step.prepared.after.stack.nextAge :=
    middleInvariant.stack_wellShaped.assigned_age_bound
      step.prepared.stackResult.vertex step.prepared.stackResult.rawAge
      selectedMarked
  have boundaryLookup :
      sigmaBoundary? step.prepared.after.stack.sigma
          step.prepared.stackResult.rawAge =
        some step.prepared.stackResult.rawAge :=
    middleInvariant.stack_wellShaped.sigma_partition
      |>.sigmaBoundary?_eq_top middleTop
  have representativeLookup :=
    middleInvariant.realizesSigma.representative_eq_boundary rawBound
  have rawRoot :
      step.prepared.coreMarked.representative
          step.prepared.stackResult.rawAge =
        step.prepared.stackResult.rawAge :=
    Option.some.inj (representativeLookup.symm.trans boundaryLookup)
  simpa [step.output_token_eq_active] using rawRoot

/-- A delayed `forward` par extension either leaves an event's live component
untouched or extends that exact event derivation by the submitted par link. -/
private theorem realizedIn_forward
    {certificate : Certificate} {event : ReservationEvent certificate}
    {before after : ReservationState}
    (realized : event.RealizedIn before)
    (invariant : SchedulerInvariant certificate before)
    (step : ForwardStep certificate before after) :
    event.RealizedIn after := by
  rcases realizedIn_prepared realized step.prepared with
    ⟨component, usedLinks, owned, componentLookup, derivation, membership⟩
  change step.prepared.coreMarked.components[
      step.prepared.coreMarked.representative event.rawAge]? =
        some (some component) at componentLookup
  have activeRoot := forward_active_root step invariant
  have activeLookup :
      step.prepared.coreMarked.components[step.queueStep.outputToken]? =
        some (some step.queueStep.component) := by
    have raw := UnificationState.componentAt?_some_raw
      step.queueStep.component_lookup
    simpa [activeRoot] using raw
  have activeBound :
      step.queueStep.outputToken < step.prepared.coreMarked.components.size :=
    (Array.getElem?_eq_some_iff.mp activeLookup).1
  have outputCore : after.core = step.coreAfter :=
    congrArg ReservationState.core step.output_eq
  let nextComponent : UnificationComponent := {
    tree := .par step.queueStep.leftFocus step.queueStep.rightFocus
      step.queueStep.component.tree
    frontier := step.queueStep.context ++ [step.consumer.conclusion] }
  have afterComponents :
      after.core.components =
        step.prepared.coreMarked.components.setIfInBounds
          step.queueStep.outputToken (some nextComponent) := by
    calc
      after.core.components = step.coreAfter.components :=
        congrArg UnificationState.components outputCore
      _ = step.prepared.coreMarked.components.setIfInBounds
            step.queueStep.outputToken (some nextComponent) := by
        simpa [nextComponent] using
          congrArg UnificationState.components step.queueStep.after_eq
  have outputParents :
      after.core.parents = step.prepared.coreMarked.parents := by
    calc
      after.core.parents = step.coreAfter.parents :=
        congrArg UnificationState.parents outputCore
      _ = step.prepared.coreMarked.parents := by
        simpa using congrArg UnificationState.parents step.queueStep.after_eq
  have representativeEq :
      after.core.representative event.rawAge =
        step.prepared.coreMarked.representative event.rawAge := by
    unfold UnificationState.representative
    rw [outputParents]
  by_cases active :
      step.prepared.coreMarked.representative event.rawAge =
        step.queueStep.outputToken
  · have componentEq : component = step.queueStep.component := by
      have same := componentLookup.symm.trans
        (by simpa [active] using activeLookup)
      exact Option.some.inj (Option.some.inj same)
    subst component
    refine ⟨nextComponent, step.consumer.linkIndex :: usedLinks,
      step.consumer.conclusion :: owned, ?_, ?_, by simp [membership]⟩
    · rw [representativeEq, active, afterComponents]
      simp [nextComponent, activeBound]
    · exact Certificate.OccurrenceDerivation.ofQueueParStep
        step.queueStep derivation step.consumer.linkIndex step.submitted_par
  · refine ⟨component, usedLinks, owned, ?_, derivation, membership⟩
    rw [representativeEq, afterComponents]
    simpa [Array.getElem?_setIfInBounds, Ne.symm active] using componentLookup

/-- Core-level delayed-par transport used by the arbitrary waiting-payload
fold.  The abstraction contract makes the executable output token a genuine
root, so the local component replacement is occurrence-exact. -/
private theorem realizedInCore_queuePar
    {certificate : Certificate} {event : ReservationEvent certificate}
    {before after : UnificationState} {left right conclusion : Vertex}
    (realized : event.RealizedInCore before)
    (abstractable : before.Abstractable certificate)
    (step : Certificate.QueueParStep before after left right conclusion)
    (linkIndex : Nat)
    (linkLookup :
      certificate.links[linkIndex]? = some (.par left right conclusion)) :
    event.RealizedInCore after := by
  rcases realized with
    ⟨component, usedLinks, owned, componentLookup, derivation, membership⟩
  have guards := UnificationState.forwardToken?_success step.token_guard
  have activeRoot : before.representative step.outputToken = step.outputToken :=
    abstractable.tokenAt?_root guards.2.1
  have activeLookup :
      before.components[step.outputToken]? = some (some step.component) := by
    have raw := UnificationState.componentAt?_some_raw step.component_lookup
    simpa [activeRoot] using raw
  have activeBound : step.outputToken < before.components.size :=
    (Array.getElem?_eq_some_iff.mp activeLookup).1
  let nextComponent : UnificationComponent := {
    tree := .par step.leftFocus step.rightFocus step.component.tree
    frontier := step.context ++ [conclusion] }
  have afterComponents :
      after.components = before.components.setIfInBounds
        step.outputToken (some nextComponent) := by
    simpa [nextComponent] using
      congrArg UnificationState.components step.after_eq
  have afterParents : after.parents = before.parents := by
    simpa using congrArg UnificationState.parents step.after_eq
  have representativeEq : ∀ rawAge,
      after.representative rawAge = before.representative rawAge := by
    intro rawAge
    unfold UnificationState.representative
    rw [afterParents]
  by_cases active : before.representative event.rawAge = step.outputToken
  · have componentEq : component = step.component := by
      have same := componentLookup.symm.trans
        (by simpa [active] using activeLookup)
      exact Option.some.inj (Option.some.inj same)
    subst component
    refine ⟨nextComponent, linkIndex :: usedLinks,
      conclusion :: owned, ?_, ?_, by simp [membership]⟩
    · rw [representativeEq, active, afterComponents]
      simp [nextComponent, activeBound]
    · exact Certificate.OccurrenceDerivation.ofQueueParStep
        step derivation linkIndex linkLookup
  · refine ⟨component, usedLinks, owned, ?_, derivation, membership⟩
    rw [representativeEq, afterComponents]
    simpa [Array.getElem?_setIfInBounds, Ne.symm active] using componentLookup

/-- Every exact waiting-par activation preserves an event realization. -/
private theorem realizedInCore_waitingParActivation
    {certificate : Certificate} {event : ReservationEvent certificate}
    {before after : UnificationState} {conclusion : Vertex}
    (realized : event.RealizedInCore before)
    (abstractable : before.Abstractable certificate)
    (step : WaitingParActivationStep certificate before after conclusion) :
    event.RealizedInCore after :=
  realizedInCore_queuePar realized abstractable step.queueStep
    step.producer.linkIndex step.submitted_par

/-- Threading the core through an arbitrary finite waiting payload preserves
every chronological event's exact axiom membership. -/
private theorem realizedInCore_waitingParActivationFold
    {certificate : Certificate} {event : ReservationEvent certificate}
    {before after : UnificationState} {payload : List Vertex}
    (realized : event.RealizedInCore before)
    (abstractable : before.Abstractable certificate)
    (step : WaitingParActivationFoldStep certificate before payload after) :
    event.RealizedInCore after := by
  induction step with
  | nil state => exact realized
  | cons head tail induction =>
      have middle := realizedInCore_waitingParActivation
        realized abstractable head
      have middleAbstractable :=
        Certificate.queuePar?_abstractable abstractable head.queue_eq
      exact induction middle middleAbstractable

/-- A tensor queue transports an event from either merged side into the one
surviving component, or leaves an unrelated component untouched.  The other
side's occurrence derivation is obtained from the supplied invariant forest;
no event-specific forest copy is introduced. -/
private theorem realizedInCore_queueTensor
    {certificate : Certificate} {event : ReservationEvent certificate}
    {before after : UnificationState} {left right conclusion : Vertex}
    (realized : event.RealizedInCore before)
    (ordered : before.OrderedParents)
    (abstractable : before.Abstractable certificate)
    (aligned : before.components.size = before.parents.size)
    (forest : certificate.ComponentForestProvenance before)
    (step : Certificate.QueueTensorStep before after left right conclusion)
    (linkIndex : Nat)
    (linkLookup :
      certificate.links[linkIndex]? = some (.tensor left right conclusion)) :
    event.RealizedInCore after := by
  rcases realized with
    ⟨component, usedLinks, owned, componentLookup, derivation, membership⟩
  rcases forest with ⟨usedAt, ownedAt, live, separated, covered⟩
  have guards := UnificationState.unifyTokens?_success step.token_guard
  have leftParentBound : step.leftToken < before.parents.size :=
    abstractable.tokenAt?_bound guards.2.1
  have rightParentBound : step.rightToken < before.parents.size :=
    abstractable.tokenAt?_bound guards.2.2.1
  have leftRoot : before.representative step.leftToken = step.leftToken :=
    abstractable.tokenAt?_root guards.2.1
  have rightRoot : before.representative step.rightToken = step.rightToken :=
    abstractable.tokenAt?_root guards.2.2.1
  have tokensDifferent : step.leftToken ≠ step.rightToken := guards.2.2.2
  have leftLookup :
      before.components[step.leftToken]? = some (some step.leftComponent) := by
    have raw := UnificationState.componentAt?_some_raw step.left_component
    simpa [leftRoot] using raw
  have rightLookup :
      before.components[step.rightToken]? = some (some step.rightComponent) := by
    have raw := UnificationState.componentAt?_some_raw step.right_component
    simpa [rightRoot] using raw
  have leftFacts := live leftLookup
  have rightFacts := live rightLookup
  have eventRepresentativeBound :
      before.representative event.rawAge < before.parents.size := by
    have componentBound := (Array.getElem?_eq_some_iff.mp componentLookup).1
    simpa [aligned] using componentBound
  have eventRawBound : event.rawAge < before.parents.size := by
    by_cases inside : event.rawAge < before.parents.size
    · exact inside
    · have sizeLe : before.parents.size ≤ event.rawAge :=
        Nat.le_of_not_gt inside
      have fixed :=
        UnificationState.representative_eq_of_size_le before sizeLe
      rw [fixed] at eventRepresentativeBound
      omega
  let survivor := min step.leftToken step.rightToken
  let retired := max step.leftToken step.rightToken
  have survivorLt : survivor < retired := by
    rcases Nat.lt_or_gt_of_ne tokensDifferent with leftLt | rightLt
    · simpa [survivor, retired, Nat.min_eq_left (Nat.le_of_lt leftLt),
        Nat.max_eq_right (Nat.le_of_lt leftLt)] using leftLt
    · simpa [survivor, retired, Nat.min_eq_right (Nat.le_of_lt rightLt),
        Nat.max_eq_left (Nat.le_of_lt rightLt)] using rightLt
  have survivorNeRetired : survivor ≠ retired := Nat.ne_of_lt survivorLt
  have retiredNeSurvivor : retired ≠ survivor := Ne.symm survivorNeRetired
  have survivorParentBound : survivor < before.parents.size := by
    rcases Nat.le_total step.leftToken step.rightToken with order | order
    · simpa [survivor, Nat.min_eq_left order] using leftParentBound
    · simpa [survivor, Nat.min_eq_right order] using rightParentBound
  have retiredParentBound : retired < before.parents.size := by
    rcases Nat.le_total step.leftToken step.rightToken with order | order
    · simpa [retired, Nat.max_eq_right order] using rightParentBound
    · simpa [retired, Nat.max_eq_left order] using leftParentBound
  have survivorRoot : before.representative survivor = survivor := by
    rcases Nat.le_total step.leftToken step.rightToken with order | order
    · simpa [survivor, Nat.min_eq_left order] using leftRoot
    · simpa [survivor, Nat.min_eq_right order] using rightRoot
  have retiredRoot : before.representative retired = retired := by
    rcases Nat.le_total step.leftToken step.rightToken with order | order
    · simpa [retired, Nat.max_eq_right order] using rightRoot
    · simpa [retired, Nat.max_eq_left order] using leftRoot
  have leftComponentBound : step.leftToken < before.components.size :=
    (Array.getElem?_eq_some_iff.mp leftLookup).1
  have rightComponentBound : step.rightToken < before.components.size :=
    (Array.getElem?_eq_some_iff.mp rightLookup).1
  have survivorComponentBound : survivor < before.components.size := by
    rcases Nat.le_total step.leftToken step.rightToken with order | order
    · simpa [survivor, Nat.min_eq_left order] using leftComponentBound
    · simpa [survivor, Nat.min_eq_right order] using rightComponentBound
  have retiredComponentBound : retired < before.components.size := by
    rcases Nat.le_total step.leftToken step.rightToken with order | order
    · simpa [retired, Nat.max_eq_right order] using rightComponentBound
    · simpa [retired, Nat.max_eq_left order] using leftComponentBound
  let nextComponent : UnificationComponent := {
    tree := .tensor step.leftFocus step.rightFocus
      step.leftComponent.tree step.rightComponent.tree
    frontier := conclusion :: (step.leftContext ++ step.rightContext) }
  have afterParents :
      after.parents = before.parents.setIfInBounds retired survivor := by
    simpa [survivor, retired] using
      congrArg UnificationState.parents step.after_eq
  have afterComponents :
      after.components =
        Array.setIfInBounds
          (before.components.setIfInBounds survivor (some nextComponent))
          retired none := by
    simpa [survivor, retired, nextComponent] using
      congrArg UnificationState.components step.after_eq
  have afterRepresentative :
      after.representative event.rawAge =
        if before.representative event.rawAge = retired then survivor
        else before.representative event.rawAge := by
    calc
      after.representative event.rawAge =
          (before.setParent retired survivor).representative event.rawAge := by
        unfold UnificationState.representative
        simp [UnificationState.setParent, afterParents]
      _ = if before.representative event.rawAge = retired then survivor
          else before.representative event.rawAge :=
        ordered.setParent_representative survivorParentBound
          retiredParentBound survivorLt survivorRoot retiredRoot eventRawBound
  have leftMerges :
      (if step.leftToken = retired then survivor else step.leftToken) =
        survivor := by
    rcases Nat.lt_or_gt_of_ne tokensDifferent with leftLt | rightLt
    · simp [survivor, retired, Nat.min_eq_left (Nat.le_of_lt leftLt),
        Nat.max_eq_right (Nat.le_of_lt leftLt)]
    · simp [survivor, retired, Nat.min_eq_right (Nat.le_of_lt rightLt),
        Nat.max_eq_left (Nat.le_of_lt rightLt)]
  have rightMerges :
      (if step.rightToken = retired then survivor else step.rightToken) =
        survivor := by
    rcases Nat.lt_or_gt_of_ne tokensDifferent with leftLt | rightLt
    · simp [survivor, retired, Nat.min_eq_left (Nat.le_of_lt leftLt),
        Nat.max_eq_right (Nat.le_of_lt leftLt)]
    · simp [survivor, retired, Nat.min_eq_right (Nat.le_of_lt rightLt),
        Nat.max_eq_left (Nat.le_of_lt rightLt)]
  by_cases eventLeft :
      before.representative event.rawAge = step.leftToken
  · have componentEq : component = step.leftComponent := by
      have same := componentLookup.symm.trans (by simpa [eventLeft] using leftLookup)
      exact Option.some.inj (Option.some.inj same)
    subst component
    refine ⟨nextComponent,
      linkIndex :: (usedLinks ++ usedAt step.rightToken),
      conclusion :: (owned ++ ownedAt step.rightToken), ?_, ?_, ?_⟩
    · rw [afterRepresentative, eventLeft, leftMerges, afterComponents]
      simp [nextComponent, survivorComponentBound, retiredNeSurvivor]
    · exact Certificate.OccurrenceDerivation.ofQueueTensorStep step
        derivation rightFacts.1.derivation linkIndex linkLookup
    · simp [membership]
  · by_cases eventRight :
        before.representative event.rawAge = step.rightToken
    · have componentEq : component = step.rightComponent := by
        have same := componentLookup.symm.trans
          (by simpa [eventRight] using rightLookup)
        exact Option.some.inj (Option.some.inj same)
      subst component
      refine ⟨nextComponent,
        linkIndex :: (usedAt step.leftToken ++ usedLinks),
        conclusion :: (ownedAt step.leftToken ++ owned), ?_, ?_, ?_⟩
      · rw [afterRepresentative, eventRight, rightMerges, afterComponents]
        simp [nextComponent, survivorComponentBound, retiredNeSurvivor]
      · exact Certificate.OccurrenceDerivation.ofQueueTensorStep step
          leftFacts.1.derivation derivation linkIndex linkLookup
      · simp [membership]
    · have eventNeSurvivor :
          before.representative event.rawAge ≠ survivor := by
        intro same
        rcases Nat.le_total step.leftToken step.rightToken with order | order
        · apply eventLeft
          simpa [survivor, Nat.min_eq_left order] using same
        · apply eventRight
          simpa [survivor, Nat.min_eq_right order] using same
      have eventNeRetired :
          before.representative event.rawAge ≠ retired := by
        intro same
        rcases Nat.le_total step.leftToken step.rightToken with order | order
        · apply eventRight
          simpa [retired, Nat.max_eq_right order] using same
        · apply eventLeft
          simpa [retired, Nat.max_eq_left order] using same
      refine ⟨component, usedLinks, owned, ?_, derivation, membership⟩
      rw [afterRepresentative, if_neg eventNeRetired, afterComponents]
      simp [Ne.symm eventNeSurvivor, Ne.symm eventNeRetired,
        componentLookup]

/-- Atomic arbitrary-payload `unify` transports an event through the tensor
merge and then through every stored waiting-par activation. -/
private theorem realizedIn_unifyPayload
    {certificate : Certificate} {event : ReservationEvent certificate}
    {before after : ReservationState}
    (realized : event.RealizedIn before)
    (invariant : SchedulerInvariant certificate before)
    (step : UnifyPayloadStep certificate before after) :
    event.RealizedIn after := by
  have middleRealized : event.RealizedInCore step.prepared.coreMarked := by
    simpa [RealizedIn, PreparedStep.after] using
      realizedIn_prepared realized step.prepared
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have tensorRealized : event.RealizedInCore step.coreTensor :=
    realizedInCore_queueTensor middleRealized
      middleInvariant.core_orderedParents
      middleInvariant.core_abstractable
      middleInvariant.core_carriers_aligned
      middleInvariant.component_forest_provenance
      step.tensorStep step.consumer.linkIndex step.submitted_tensor
  have tensorAbstractable : step.coreTensor.Abstractable certificate :=
    Certificate.queueTensor?_abstractable
      middleInvariant.core_abstractable middleInvariant.core_orderedParents
      step.tensor_queue_eq
  have finalCoreRealized : event.RealizedInCore step.coreAfter :=
    realizedInCore_waitingParActivationFold tensorRealized
      tensorAbstractable step.activationFold
  change event.RealizedInCore after.core
  rw [show after.core = step.coreAfter from
    congrArg ReservationState.core step.output_eq]
  exact finalCoreRealized

end ReservationEvent

namespace DispatchTagEvidence

/-- Every already-realized event survives one exact canonical dispatcher
step, independently of which priority branch was selected. -/
private theorem realizedIn
    {certificate : Certificate} {event : ReservationEvent certificate}
    {before : ReservationState} {result : Figure7DispatchResult}
    (invariant : SchedulerInvariant certificate before)
    (realized : event.RealizedIn before)
    (evidence : DispatchTagEvidence certificate before result) :
    event.RealizedIn result.after := by
  cases evidence with
  | concl step => exact ReservationEvent.realizedIn_concl realized step
  | nop step => exact ReservationEvent.realizedIn_nop realized step
  | new step => exact ReservationEvent.realizedIn_new_old realized step
  | wait step => exact ReservationEvent.realizedIn_wait realized step
  | forward step =>
      exact ReservationEvent.realizedIn_forward realized invariant step
  | unifyPayload step =>
      exact ReservationEvent.realizedIn_unifyPayload realized invariant step

end DispatchTagEvidence

namespace CanonicalTagHistory

/-- Every chronological ledger event is realized in the final live component
at its current representative.  Multiple raw ages may therefore select the
same final component after tensor unions. -/
theorem reservationLedger_realized
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger) :
    event.RealizedIn state := by
  induction tagHistory with
  | empty =>
      simp [reservationLedger] at membership
  | init step =>
      simp only [reservationLedger, List.mem_singleton] at membership
      subst event
      exact ReservationEvent.initial_realized structural step
  | @later before result priorHistory invariant dispatch prior evidence
      induction =>
      simp only [reservationLedger, List.mem_append] at membership
      rcases membership with earlier | current
      · exact evidence.realizedIn invariant (induction earlier)
      · cases evidence with
        | concl step => simp [DispatchTagEvidence.reservationEvents] at current
        | nop step => simp [DispatchTagEvidence.reservationEvents] at current
        | new step =>
            simp only [DispatchTagEvidence.reservationEvents,
              List.mem_singleton] at current
            subst event
            exact ReservationEvent.new_realized invariant.structural step
        | wait step => simp [DispatchTagEvidence.reservationEvents] at current
        | forward step =>
            simp [DispatchTagEvidence.reservationEvents] at current
        | unifyPayload step =>
            simp [DispatchTagEvidence.reservationEvents] at current

/-- Final forest alignment for one chronological reservation.

The event-specific derivation may use a different submitted-link list from
the invariant's chosen witness, but structural validity makes their exact
owned-occurrence lists equal.  Thus the event is attached to the current
accounted owner without duplicating a forest in every ledger entry. -/
theorem reservationLedger_finalComponent
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger) :
    ∃ component eventUsed forestUsed owned,
      state.core.components[state.core.representative event.rawAge]? =
          some (some component) ∧
        certificate.OccurrenceDerivation component.tree component.frontier
          eventUsed owned ∧
        event.linkIndex ∈ eventUsed ∧
        certificate.ComponentOccurrenceWitness component forestUsed owned ∧
        Certificate.OwnedOccurrenceAccounted state.core
          (state.core.representative event.rawAge) component owned := by
  rcases tagHistory.reservationLedger_realized structural membership with
    ⟨component, eventUsed, eventOwned, componentLookup,
      eventDerivation, eventLink⟩
  have finalInvariant := history.schedulerInvariant structural
  rcases finalInvariant.component_forest_provenance with
    ⟨usedAt, ownedAt, live, separated, covered⟩
  have finalFacts := live componentLookup
  have ownedEq :
      eventOwned = ownedAt (state.core.representative event.rawAge) :=
    Certificate.OccurrenceDerivation.owned_unique structural
      eventDerivation finalFacts.1.derivation
  refine ⟨component, eventUsed,
    usedAt (state.core.representative event.rawAge), eventOwned,
    componentLookup, eventDerivation, eventLink, ?_, ?_⟩
  · simpa [ownedEq] using finalFacts.1
  · simpa [ownedEq] using finalFacts.2

/-- Both exact endpoints of a ledger event's submitted axiom occur in the
same final owned list certified by the invariant forest and accounted at the
event raw age's current representative. -/
theorem reservationLedger_axiomEndpoints_accounted
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger) :
    ∃ component eventUsed forestUsed owned,
      state.core.components[state.core.representative event.rawAge]? =
          some (some component) ∧
        certificate.OccurrenceDerivation component.tree component.frontier
          eventUsed owned ∧
        event.linkIndex ∈ eventUsed ∧
        certificate.ComponentOccurrenceWitness component forestUsed owned ∧
        Certificate.OwnedOccurrenceAccounted state.core
          (state.core.representative event.rawAge) component owned ∧
        event.search.result.left ∈ owned ∧
        event.search.result.right ∈ owned := by
  rcases tagHistory.reservationLedger_finalComponent structural membership with
    ⟨component, eventUsed, forestUsed, owned, componentLookup,
      eventDerivation, eventLink, forestWitness, accounted⟩
  have endpoints := eventDerivation.usedAxiomEndpoints_owned
    eventLink event.search.result.exactLink
  exact ⟨component, eventUsed, forestUsed, owned, componentLookup,
    eventDerivation, eventLink, forestWitness, accounted,
    endpoints.1, endpoints.2⟩

end CanonicalTagHistory

end SequentialFigure7

end ProofNetIR
