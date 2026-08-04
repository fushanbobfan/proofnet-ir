import ProofNetIR.SequentialFigure7UnifyPayloadInvariant

namespace ProofNetIR

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

namespace Figure7UnifyPayloadInvariantTests

/-! A natural full-state regression for a two-element waiting payload. -/

private def payloadInvariantCertificate : Certificate where
  formulas := #[
    .atom "p" true, .atom "p" false,
    .atom "q" true, .atom "q" false,
    .atom "r" true, .atom "r" false,
    .atom "s" true, .atom "s" false,
    .tensor (.atom "p" true) (.atom "q" true),
    .tensor (.atom "r" true) (.atom "s" true),
    .tensor
      (.tensor (.atom "p" true) (.atom "q" true))
      (.tensor (.atom "r" true) (.atom "s" true)),
    .par (.atom "r" false) (.atom "p" false),
    .par (.atom "s" false) (.atom "q" false)]
  links := [
    .axiom 0 1, .axiom 2 3, .axiom 4 5, .axiom 6 7,
    .tensor 0 2 8, .tensor 4 6 9, .tensor 8 9 10,
    .par 5 1 11, .par 7 3 12]
  conclusions := [10, 11, 12]

private theorem payloadInvariantCertificate_structural :
    payloadInvariantCertificate.StructurallyWellFormed := by
  exact
    (Certificate.wellFormed_iff_structurallyWellFormed
      payloadInvariantCertificate).mp (by native_decide)

private def payloadInvariantBefore : ReservationState where
  stack := {
    marks := #[
      some 2, some 2, some 2, some 2,
      some 0, some 0, some 0, some 0,
      none, some 0, none, none, none]
    nextAge := 4
    sigma := [0, 2]
    ready := [[], [8]]
    waiting := #[
      .initialized [11, 12], .undefined, .undefined, .undefined,
      .undefined, .undefined, .undefined, .undefined,
      .undefined, .undefined, .undefined, .undefined, .undefined] }
  core := {
    marks := #[
      some 2, some 2, some 2, some 2,
      some 0, some 0, some 0, some 0,
      none, some 0, none, none, none]
    parents := #[0, 0, 2, 2]
    components := #[
      some {
        tree := .tensor 0 0 (.axiom "r" true) (.axiom "s" true)
        frontier := [9, 5, 7] },
      none,
      some {
        tree := .tensor 0 0 (.axiom "p" true) (.axiom "q" true)
        frontier := [8, 1, 3] },
      none]
    startedAxioms := 4
    firedConnectives := 2 }
  tags := Array.replicate 13 false

private theorem nat_cases_lt_four {value : Nat} (bound : value < 4) :
    value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 3 := by
  omega

private theorem nat_cases_lt_thirteen {value : Nat} (bound : value < 13) :
    value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 3 ∨
      value = 4 ∨ value = 5 ∨ value = 6 ∨ value = 7 ∨
        value = 8 ∨ value = 9 ∨ value = 10 ∨ value = 11 ∨
          value = 12 := by
  omega

private theorem payloadInvariantBefore_reservationInvariant :
    ReservationInvariant payloadInvariantCertificate payloadInvariantBefore := by
  exact {
    stack_wellShaped := {
      marks_size := rfl
      waiting_size := rfl
      assigned_age_bound := by
        intro vertex age assigned
        have bound : vertex < 13 := by
          simpa [payloadInvariantBefore] using
            (Array.getElem?_eq_some_iff.mp assigned).1
        rcases nat_cases_lt_thirteen bound with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl
        all_goals simp [payloadInvariantBefore] at assigned ⊢
        all_goals subst age <;> decide
      sigma_partition := {
        empty_iff := by simp [payloadInvariantBefore]
        head_zero := by simp [payloadInvariantBefore]
        strictIncreasing := by simp [payloadInvariantBefore]
        boundary_lt := by
          intro boundary membership
          simp [payloadInvariantBefore] at membership
          rcases membership with rfl | rfl <;> decide }
      ready_aligned := rfl
      ready_nodup := by
        intro bucket membership
        simp [payloadInvariantBefore] at membership
        rcases membership with rfl | rfl <;> simp
      ready_in_bounds := by
        intro bucket membership vertex vertexMembership
        simp [payloadInvariantBefore] at membership
        rcases membership with rfl | rfl
        · simp at vertexMembership
        · have same : vertex = 8 := by simpa using vertexMembership
          subst vertex
          native_decide
      nextAge_le_waiting := by native_decide }
    stack_operationalWaitingDomain := {
      initialized_iff_inactive := by
        intro age ageBound
        rcases nat_cases_lt_four ageBound with rfl | rfl | rfl | rfl <;>
          simp [SequentialStackState.WaitingInitializedAt,
            payloadInvariantBefore] }
    realizesSigma := {
      marks_eq := rfl
      horizon_eq := rfl
      representative_eq_boundary := by
        intro age ageBound
        rcases nat_cases_lt_four ageBound with rfl | rfl | rfl | rfl <;>
          native_decide }
    core_orderedParents := by
      intro token parent lookup
      have bound : token < 4 := by
        simpa [payloadInvariantBefore] using
          (Array.getElem?_eq_some_iff.mp lookup).1
      rcases nat_cases_lt_four bound with rfl | rfl | rfl | rfl <;>
        simp [payloadInvariantBefore] at lookup ⊢ <;> omega
    core_abstractable := {
      markArraySize := rfl
      markedVertexBound := by
        intro vertex token assigned
        simpa [payloadInvariantCertificate, payloadInvariantBefore] using
          (Array.getElem?_eq_some_iff.mp
            (UnificationState.assignedToken?_some_raw assigned)).1
      markedTokenBound := by
        intro vertex token assigned
        have raw := UnificationState.assignedToken?_some_raw assigned
        have bound : vertex < 13 := by
          simpa [payloadInvariantBefore] using
            (Array.getElem?_eq_some_iff.mp raw).1
        rcases nat_cases_lt_thirteen bound with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl
        all_goals simp [payloadInvariantBefore] at raw ⊢
        all_goals subst token <;> decide
      representativeBound := by
        intro token tokenBound
        rcases nat_cases_lt_four tokenBound with rfl | rfl | rfl | rfl <;>
          native_decide
      representativeIdempotent := by
        intro token tokenBound
        rcases nat_cases_lt_four tokenBound with rfl | rfl | rfl | rfl <;>
          native_decide }
    core_componentsFormulaConsistent := by
      intro index component lookup
      have bound : index < 4 := by
        simpa [payloadInvariantBefore] using
          (Array.getElem?_eq_some_iff.mp lookup).1
      rcases nat_cases_lt_four bound with rfl | rfl | rfl | rfl
      · simp [payloadInvariantBefore] at lookup
        subst component
        exact ⟨[
            .tensor (.atom "r" true) (.atom "s" true),
            .atom "r" false, .atom "s" false],
          by native_decide, by native_decide⟩
      · simp [payloadInvariantBefore] at lookup
      · simp [payloadInvariantBefore] at lookup
        subst component
        exact ⟨[
            .tensor (.atom "p" true) (.atom "q" true),
            .atom "p" false, .atom "q" false],
          by native_decide, by native_decide⟩
      · simp [payloadInvariantBefore] at lookup
    core_carriers_aligned := rfl
    core_counter_aligned := rfl
    tags_size := rfl }

private theorem payloadInvariantBefore_componentForestProvenance :
    payloadInvariantCertificate.ComponentForestProvenance
      payloadInvariantBefore.core := by
  let usedAt : Nat → List Nat := fun index =>
    if index = 0 then [5, 2, 3]
    else if index = 2 then [4, 0, 1]
    else []
  let ownedAt : Nat → List Nat := fun index =>
    if index = 0 then [9, 4, 5, 6, 7]
    else if index = 2 then [8, 0, 1, 2, 3]
    else []
  refine ⟨usedAt, ownedAt, ?_, ?_, ?_⟩
  · intro index component lookup
    have bound : index < 4 := by
      simpa [payloadInvariantBefore] using
        (Array.getElem?_eq_some_iff.mp lookup).1
    rcases nat_cases_lt_four bound with rfl | rfl | rfl | rfl
    · simp [payloadInvariantBefore] at lookup
      subst component
      constructor
      · refine ⟨?_, by decide, by decide⟩
        exact .tensor
          (.axiom 2 4 5 "r" true (by native_decide) (by native_decide))
          (.axiom 3 6 7 "s" true (by native_decide) (by native_decide))
          5 4 6 9 0 0 [5] [7] (by native_decide)
          ({ first := rfl, positional := rfl })
          ({ first := rfl, positional := rfl })
      · intro vertex membership
        simp [ownedAt] at membership
        rcases membership with rfl | rfl | rfl | rfl | rfl
        all_goals first
          | exact Or.inl ⟨0, by native_decide, by native_decide⟩
          | exact Or.inl ⟨1, by native_decide, by native_decide⟩
    · simp [payloadInvariantBefore] at lookup
    · simp [payloadInvariantBefore] at lookup
      subst component
      constructor
      · refine ⟨?_, by decide, by decide⟩
        exact .tensor
          (.axiom 0 0 1 "p" true (by native_decide) (by native_decide))
          (.axiom 1 2 3 "q" true (by native_decide) (by native_decide))
          4 0 2 8 0 0 [1] [3] (by native_decide)
          ({ first := rfl, positional := rfl })
          ({ first := rfl, positional := rfl })
      · intro vertex membership
        simp [ownedAt] at membership
        rcases membership with rfl | rfl | rfl | rfl | rfl
        all_goals first
          | exact Or.inr ⟨by native_decide, by simp⟩
          | exact Or.inl ⟨2, by native_decide, by native_decide⟩
          | exact Or.inl ⟨3, by native_decide, by native_decide⟩
    · simp [payloadInvariantBefore] at lookup
  · intro leftIndex rightIndex leftComponent rightComponent
      leftLookup rightLookup different
    have leftBound : leftIndex < 4 := by
      simpa [payloadInvariantBefore] using
        (Array.getElem?_eq_some_iff.mp leftLookup).1
    have rightBound : rightIndex < 4 := by
      simpa [payloadInvariantBefore] using
        (Array.getElem?_eq_some_iff.mp rightLookup).1
    rcases nat_cases_lt_four leftBound with rfl | rfl | rfl | rfl <;>
      rcases nat_cases_lt_four rightBound with rfl | rfl | rfl | rfl <;>
      simp [payloadInvariantBefore, usedAt, ownedAt] at *
  · intro vertex rawAge marked
    have bound : vertex < 13 := by
      simpa [payloadInvariantBefore] using
        (Array.getElem?_eq_some_iff.mp marked).1
    rcases nat_cases_lt_thirteen bound with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
    · have same : rawAge = 2 := by
        simpa [payloadInvariantBefore] using marked.symm
      subst rawAge
      refine ⟨2, ({
        tree := .tensor 0 0 (.axiom "p" true) (.axiom "q" true),
        frontier := [8, 1, 3] } : UnificationComponent),
        by native_decide, by native_decide, ?_⟩
      simp [ownedAt]
    · have same : rawAge = 2 := by
        simpa [payloadInvariantBefore] using marked.symm
      subst rawAge
      refine ⟨2, ({
        tree := .tensor 0 0 (.axiom "p" true) (.axiom "q" true),
        frontier := [8, 1, 3] } : UnificationComponent),
        by native_decide, by native_decide, ?_⟩
      simp [ownedAt]
    · have same : rawAge = 2 := by
        simpa [payloadInvariantBefore] using marked.symm
      subst rawAge
      refine ⟨2, ({
        tree := .tensor 0 0 (.axiom "p" true) (.axiom "q" true),
        frontier := [8, 1, 3] } : UnificationComponent),
        by native_decide, by native_decide, ?_⟩
      simp [ownedAt]
    · have same : rawAge = 2 := by
        simpa [payloadInvariantBefore] using marked.symm
      subst rawAge
      refine ⟨2, ({
        tree := .tensor 0 0 (.axiom "p" true) (.axiom "q" true),
        frontier := [8, 1, 3] } : UnificationComponent),
        by native_decide, by native_decide, ?_⟩
      simp [ownedAt]
    · have same : rawAge = 0 := by
        simpa [payloadInvariantBefore] using marked.symm
      subst rawAge
      refine ⟨0, ({
        tree := .tensor 0 0 (.axiom "r" true) (.axiom "s" true),
        frontier := [9, 5, 7] } : UnificationComponent),
        by native_decide, by native_decide, ?_⟩
      simp [ownedAt]
    · have same : rawAge = 0 := by
        simpa [payloadInvariantBefore] using marked.symm
      subst rawAge
      refine ⟨0, ({
        tree := .tensor 0 0 (.axiom "r" true) (.axiom "s" true),
        frontier := [9, 5, 7] } : UnificationComponent),
        by native_decide, by native_decide, ?_⟩
      simp [ownedAt]
    · have same : rawAge = 0 := by
        simpa [payloadInvariantBefore] using marked.symm
      subst rawAge
      refine ⟨0, ({
        tree := .tensor 0 0 (.axiom "r" true) (.axiom "s" true),
        frontier := [9, 5, 7] } : UnificationComponent),
        by native_decide, by native_decide, ?_⟩
      simp [ownedAt]
    · have same : rawAge = 0 := by
        simpa [payloadInvariantBefore] using marked.symm
      subst rawAge
      refine ⟨0, ({
        tree := .tensor 0 0 (.axiom "r" true) (.axiom "s" true),
        frontier := [9, 5, 7] } : UnificationComponent),
        by native_decide, by native_decide, ?_⟩
      simp [ownedAt]
    · simp [payloadInvariantBefore] at marked
    · have same : rawAge = 0 := by
        simpa [payloadInvariantBefore] using marked.symm
      subst rawAge
      refine ⟨0, ({
        tree := .tensor 0 0 (.axiom "r" true) (.axiom "s" true),
        frontier := [9, 5, 7] } : UnificationComponent),
        by native_decide, by native_decide, ?_⟩
      simp [ownedAt]
    · simp [payloadInvariantBefore] at marked
    · simp [payloadInvariantBefore] at marked
    · simp [payloadInvariantBefore] at marked

private theorem payloadInvariantBefore_componentDomainExact :
    ComponentDomainExact payloadInvariantBefore := by
  intro token
  constructor
  · rintro ⟨component, lookup⟩
    have bound : token < 4 := by
      simpa [payloadInvariantBefore] using
        (Array.getElem?_eq_some_iff.mp lookup).1
    rcases nat_cases_lt_four bound with rfl | rfl | rfl | rfl <;>
      simp [payloadInvariantBefore] at lookup ⊢
  · intro membership
    simp [payloadInvariantBefore] at membership
    rcases membership with rfl | rfl
    · exact ⟨{
        tree := .tensor 0 0 (.axiom "r" true) (.axiom "s" true),
        frontier := [9, 5, 7] }, rfl⟩
    · exact ⟨{
        tree := .tensor 0 0 (.axiom "p" true) (.axiom "q" true),
        frontier := [8, 1, 3] }, rfl⟩

private theorem payloadInvariantBefore_liveFrontiersNodup :
    LiveFrontiersNodup payloadInvariantBefore := by
  unfold LiveFrontiersNodup UnificationState.liveFrontierVertices
  native_decide

private theorem payloadInvariantBefore_readyBucketFrontierExact :
    ReadyBucketFrontierExact payloadInvariantBefore := by
  intro position boundary bucket sigmaLookup readyLookup
  have bound : position < 2 := by
    simpa [payloadInvariantBefore] using
      (List.getElem?_eq_some_iff.mp sigmaLookup).1
  have cases : position = 0 ∨ position = 1 := by omega
  rcases cases with rfl | rfl
  · simp [payloadInvariantBefore] at sigmaLookup readyLookup
    subst boundary
    subst bucket
    refine ⟨{
      tree := .tensor 0 0 (.axiom "r" true) (.axiom "s" true),
      frontier := [9, 5, 7] }, rfl, ?_⟩
    intro vertex
    constructor
    · simp
    · rintro ⟨frontier, unmarked⟩
      simp at frontier
      rcases frontier with rfl | rfl | rfl <;>
        simp [payloadInvariantBefore] at unmarked
  · simp [payloadInvariantBefore] at sigmaLookup readyLookup
    subst boundary
    subst bucket
    refine ⟨{
      tree := .tensor 0 0 (.axiom "p" true) (.axiom "q" true),
      frontier := [8, 1, 3] }, rfl, ?_⟩
    intro vertex
    constructor
    · intro membership
      have same : vertex = 8 := by simpa using membership
      subst vertex
      simp [payloadInvariantBefore]
    · rintro ⟨frontier, unmarked⟩
      simp at frontier
      rcases frontier with rfl | rfl | rfl
      · simp
      · simp [payloadInvariantBefore] at unmarked
      · simp [payloadInvariantBefore] at unmarked

private theorem payloadInvariantBefore_queuedVerticesNodup :
    QueuedVerticesNodup payloadInvariantBefore := by
  unfold QueuedVerticesNodup SequentialStackState.queuedVertices
    SequentialStackState.waitingVertices WaitingCell.vertices
  native_decide

private theorem payloadInvariantBefore_queuedVerticesUnmarked :
    QueuedVerticesUnmarked payloadInvariantBefore := by
  intro vertex membership
  have cases : vertex = 8 ∨ vertex = 11 ∨ vertex = 12 := by
    simpa [payloadInvariantBefore, SequentialStackState.queuedVertices,
      SequentialStackState.waitingVertices, WaitingCell.vertices] using membership
  rcases cases with rfl | rfl | rfl <;> rfl

private theorem payloadInvariantBefore_notProducedTen :
    ¬ Produced payloadInvariantBefore 10 := by
  rintro (⟨age, marked⟩ | frontier)
  · simp [payloadInvariantBefore] at marked
  · unfold UnificationState.liveFrontierVertices at frontier
    simp [payloadInvariantBefore] at frontier

private theorem payloadInvariantBefore_notProducedEleven :
    ¬ Produced payloadInvariantBefore 11 := by
  rintro (⟨age, marked⟩ | frontier)
  · simp [payloadInvariantBefore] at marked
  · unfold UnificationState.liveFrontierVertices at frontier
    simp [payloadInvariantBefore] at frontier

private theorem payloadInvariantBefore_notProducedTwelve :
    ¬ Produced payloadInvariantBefore 12 := by
  rintro (⟨age, marked⟩ | frontier)
  · simp [payloadInvariantBefore] at marked
  · unfold UnificationState.liveFrontierVertices at frontier
    simp [payloadInvariantBefore] at frontier

private theorem payloadInvariantBefore_producedPremisesMarked :
    ProducedPremisesMarked payloadInvariantCertificate payloadInvariantBefore := by
  intro link membership
  simp [payloadInvariantCertificate] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · trivial
  · trivial
  · trivial
  · trivial
  · intro _
    exact ⟨⟨2, by native_decide⟩, ⟨2, by native_decide⟩⟩
  · intro _
    exact ⟨⟨0, by native_decide⟩, ⟨0, by native_decide⟩⟩
  · intro produced
    exact False.elim (payloadInvariantBefore_notProducedTen produced)
  · intro produced
    exact False.elim (payloadInvariantBefore_notProducedEleven produced)
  · intro produced
    exact False.elim (payloadInvariantBefore_notProducedTwelve produced)

private theorem payloadInvariantBefore_waitingSpanExact :
    WaitingSpanExact payloadInvariantCertificate payloadInvariantBefore := by
  intro boundary payload conclusion waitingLookup conclusionMembership
  have bound : boundary < 13 := by
    simpa [payloadInvariantBefore] using
      (Array.getElem?_eq_some_iff.mp waitingLookup).1
  rcases nat_cases_lt_thirteen bound with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
  · simp [payloadInvariantBefore] at waitingLookup
    subst payload
    simp at conclusionMembership
    rcases conclusionMembership with rfl | rfl
    · refine ⟨7, 5, 1, 5, 1, 0, 2, 2, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩ <;> native_decide
    · refine ⟨8, 7, 3, 7, 3, 0, 2, 2, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩ <;> native_decide
  all_goals simp [payloadInvariantBefore] at waitingLookup

private theorem payloadInvariantBefore_pendingPremisesCoveredExceptReady :
    PendingPremisesCoveredExceptReady payloadInvariantCertificate
      payloadInvariantBefore := by
  intro link membership
  simp [payloadInvariantCertificate] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · trivial
  · trivial
  · trivial
  · trivial
  · intro _ notReady
    exfalso
    exact notReady (by simp [payloadInvariantBefore])
  · intro unmarked
    simp [payloadInvariantBefore] at unmarked
  · intro _ _ premise token premiseMembership tokenAt
    simp at premiseMembership
    rcases premiseMembership with rfl | rfl
    · simp [payloadInvariantBefore, UnificationState.tokenAt?] at tokenAt
    · have same : token = 0 := by
        change some (payloadInvariantBefore.core.representative 0) =
          some token at tokenAt
        have representative :
            payloadInvariantBefore.core.representative 0 = 0 := by
          native_decide
        rw [representative] at tokenAt
        exact (Option.some.inj tokenAt).symm
      subst token
      refine ⟨{
        tree := .tensor 0 0 (.axiom "r" true) (.axiom "s" true),
        frontier := [9, 5, 7] }, by native_decide, by simp⟩
  · intro _ _ premise token premiseMembership tokenAt
    simp at premiseMembership
    rcases premiseMembership with rfl | rfl
    · have same : token = 0 := by
        change some (payloadInvariantBefore.core.representative 0) =
          some token at tokenAt
        have representative :
            payloadInvariantBefore.core.representative 0 = 0 := by
          native_decide
        rw [representative] at tokenAt
        exact (Option.some.inj tokenAt).symm
      subst token
      refine ⟨{
        tree := .tensor 0 0 (.axiom "r" true) (.axiom "s" true),
        frontier := [9, 5, 7] }, by native_decide, by simp⟩
    · have same : token = 2 := by
        change some (payloadInvariantBefore.core.representative 2) =
          some token at tokenAt
        have representative :
            payloadInvariantBefore.core.representative 2 = 2 := by
          native_decide
        rw [representative] at tokenAt
        exact (Option.some.inj tokenAt).symm
      subst token
      refine ⟨{
        tree := .tensor 0 0 (.axiom "p" true) (.axiom "q" true),
        frontier := [8, 1, 3] }, by native_decide, by simp⟩
  · intro _ _ premise token premiseMembership tokenAt
    simp at premiseMembership
    rcases premiseMembership with rfl | rfl
    · have same : token = 0 := by
        change some (payloadInvariantBefore.core.representative 0) =
          some token at tokenAt
        have representative :
            payloadInvariantBefore.core.representative 0 = 0 := by
          native_decide
        rw [representative] at tokenAt
        exact (Option.some.inj tokenAt).symm
      subst token
      refine ⟨{
        tree := .tensor 0 0 (.axiom "r" true) (.axiom "s" true),
        frontier := [9, 5, 7] }, by native_decide, by simp⟩
    · have same : token = 2 := by
        change some (payloadInvariantBefore.core.representative 2) =
          some token at tokenAt
        have representative :
            payloadInvariantBefore.core.representative 2 = 2 := by
          native_decide
        rw [representative] at tokenAt
        exact (Option.some.inj tokenAt).symm
      subst token
      refine ⟨{
        tree := .tensor 0 0 (.axiom "p" true) (.axiom "q" true),
        frontier := [8, 1, 3] }, by native_decide, by simp⟩

private theorem payloadInvariantBefore_firedCounterExact :
    FiredCounterExact payloadInvariantBefore := by
  unfold FiredCounterExact UnificationState.liveConnectiveCount
  rfl

private theorem payloadInvariantBefore_schedulerInvariant :
    SchedulerInvariant payloadInvariantCertificate payloadInvariantBefore := by
  exact {
    toReservationInvariant := payloadInvariantBefore_reservationInvariant
    structural := payloadInvariantCertificate_structural
    component_domain_exact := payloadInvariantBefore_componentDomainExact
    component_forest_provenance :=
      payloadInvariantBefore_componentForestProvenance
    live_frontiers_nodup := payloadInvariantBefore_liveFrontiersNodup
    ready_bucket_frontier_exact :=
      payloadInvariantBefore_readyBucketFrontierExact
    queued_vertices_nodup := payloadInvariantBefore_queuedVerticesNodup
    queued_vertices_unmarked := payloadInvariantBefore_queuedVerticesUnmarked
    produced_premises_marked :=
      payloadInvariantBefore_producedPremisesMarked
    waiting_span_exact := payloadInvariantBefore_waitingSpanExact
    pending_premises_covered_except_ready :=
      payloadInvariantBefore_pendingPremisesCoveredExceptReady
    fired_counter_exact := payloadInvariantBefore_firedCounterExact }

private def payloadInvariantRun : Option ReservationState :=
  SequentialFigure7.unifyPayload? payloadInvariantCertificate
    payloadInvariantBefore
    payloadInvariantBefore_schedulerInvariant.toReservationInvariant

example :
    (match payloadInvariantRun with
    | none => false
    | some after =>
        after.stack.sigma == [0] &&
        after.stack.ready == [[10, 11, 12]] &&
        after.core.parents == #[0, 0, 0, 2] &&
        after.core.firedConnectives == 5) = true := by
  native_decide

example {after : ReservationState}
    (equation : payloadInvariantRun = some after) :
    Nonempty
      (SequentialFigure7.UnifyPayloadStep payloadInvariantCertificate
        payloadInvariantBefore after) := by
  exact
    (SequentialFigure7.unifyPayload?_some_iff
      payloadInvariantBefore_schedulerInvariant.toReservationInvariant).mp
        (by simpa [payloadInvariantRun] using equation)

example {after : ReservationState}
    (equation : payloadInvariantRun = some after) :
    SchedulerInvariant payloadInvariantCertificate after := by
  exact SequentialFigure7.unifyPayload?_schedulerInvariant
    payloadInvariantBefore_schedulerInvariant
    (by simpa [payloadInvariantRun] using equation)

end Figure7UnifyPayloadInvariantTests

end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 arbitrary-payload invariant tests passed"
