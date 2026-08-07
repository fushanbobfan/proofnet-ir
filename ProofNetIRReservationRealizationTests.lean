import ProofNetIR.SequentialFigure7ReservationRealization

namespace ProofNetIRReservationRealizationTests

open ProofNetIR
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialUnification

/- The positional helpers retain duplicated values because they identify the
exact removed/reordered occurrences, not merely a value-level permutation. -/
example {first second remaining : List α} {index : Nat} {selected : α}
    (firstPick : CutFreeDerivation.pick? first index =
      some (selected, remaining))
    (secondPick : CutFreeDerivation.pick? second index =
      some (selected, remaining)) :
    first = second :=
  CutFreeDerivation.pick?_source_unique firstPick secondPick

example [DecidableEq α] {first second reordered : List α}
    {order : List Nat}
    (firstEquation : CutFreeDerivation.reorder? first order = some reordered)
    (secondEquation : CutFreeDerivation.reorder? second order =
      some reordered) :
    first = second :=
  CutFreeDerivation.reorder?_source_unique firstEquation secondEquation

/- A small checker-shaped certificate whose two axiom components are joined
by the tensor after one authentic `new` allocation. -/
private def unionCertificate : Certificate where
  formulas := #[
    .atom "p" true,
    .atom "p" false,
    .atom "p" true,
    .atom "p" false,
    .tensor (.atom "p" true) (.atom "p" true)]
  links := [
    .axiom 0 1,
    .axiom 2 3,
    .tensor 0 2 4]
  conclusions := [4, 1, 3]

private theorem unionCertificate_structural :
    unionCertificate.StructurallyWellFormed := by
  exact
    (Certificate.wellFormed_iff_structurallyWellFormed
      unionCertificate).mp (by native_decide)

private theorem unionCertificate_accepted :
    unionCertificate.check = true := by
  native_decide

private theorem unionCertificate_declarativelyCorrect :
    unionCertificate.DeclarativelyCorrect :=
  unionCertificate.check_iff_declarativelyCorrect.mp
    unionCertificate_accepted

/- The union fixture is an accepted proof net, not merely a locally
well-shaped scheduler input. -/
example :
    unionCertificate.check = true ∧
      unionCertificate.DeclarativelyCorrect :=
  ⟨unionCertificate_accepted,
    unionCertificate_declarativelyCorrect⟩

private def unionInitial : ReservationState :=
  match initializeReservation? unionCertificate 0 with
  | some state => state
  | none => ReservationState.empty unionCertificate

private theorem unionInitial_eq :
    initializeReservation? unionCertificate 0 = some unionInitial := by
  native_decide

private theorem unionInitial_invariant :
    SchedulerInvariant unionCertificate unionInitial := by
  rcases initializeReservation?_some_iff.mp unionInitial_eq with
    ⟨step⟩
  exact step.schedulerInvariant unionCertificate_structural

private def unionAfterNew : ReservationState :=
  match dispatch? unionCertificate unionInitial unionInitial_invariant with
  | some result => result.after
  | none => ReservationState.empty unionCertificate

private theorem unionFirstDispatch_eq :
    dispatch? unionCertificate unionInitial unionInitial_invariant =
      some ⟨.new, unionAfterNew⟩ := by
  native_decide

private theorem unionAfterNew_invariant :
    SchedulerInvariant unionCertificate unionAfterNew :=
  dispatch?_schedulerInvariant unionInitial_invariant unionFirstDispatch_eq

private def unionFinal : ReservationState :=
  match dispatch? unionCertificate unionAfterNew unionAfterNew_invariant with
  | some result => result.after
  | none => ReservationState.empty unionCertificate

private theorem unionSecondDispatch_eq :
    dispatch? unionCertificate unionAfterNew unionAfterNew_invariant =
      some ⟨.unifyPayload, unionFinal⟩ := by
  native_decide

/- This is a real union, not a hand-written parent array: the canonical
dispatcher allocates raw ages zero and one, then its general unify branch
makes both resolve to the surviving live component at slot zero. -/
example :
    unionFinal.stack.nextAge = 2 ∧
      unionFinal.core.parents = #[0, 0] ∧
      unionFinal.core.representative 0 = 0 ∧
      unionFinal.core.representative 1 = 0 ∧
      unionFinal.core.components[0]?.isSome ∧
      unionFinal.core.components[1]? = some none := by
  native_decide

private def EventsShareFinalAccountedOwner
    (first second : ReservationEvent unionCertificate) : Prop :=
  ∃ component firstUsed secondUsed forestUsed owned,
    unionFinal.core.components[0]? = some (some component) ∧
      unionCertificate.OccurrenceDerivation component.tree component.frontier
        firstUsed owned ∧
      first.linkIndex ∈ firstUsed ∧
      unionCertificate.OccurrenceDerivation component.tree component.frontier
        secondUsed owned ∧
      second.linkIndex ∈ secondUsed ∧
      unionCertificate.ComponentOccurrenceWitness component forestUsed owned ∧
      Certificate.OwnedOccurrenceAccounted unionFinal.core 0 component owned ∧
      first.search.result.left ∈ owned ∧
      first.search.result.right ∈ owned ∧
      second.search.result.left ∈ owned ∧
      second.search.result.right ∈ owned

/- The chronological regression exercises the complete public realization
surface.  The two events retain distinct submitted axiom slots and distinct
event-specific derivations, but after tensor union both derivations align to
one current forest-owned occurrence list.  Consequently all four historical
axiom endpoints are accounted by that same current owner. -/
set_option maxHeartbeats 1200000 in
private theorem genuine_union_reservation_realization :
    ∃ (history : ExecutedHistory unionCertificate unionFinal)
      (tagHistory : CanonicalTagHistory unionCertificate history)
      (first second : ReservationEvent unionCertificate),
      unionCertificate.DeclarativelyCorrect ∧
        tagHistory.reservationLedger = [first, second] ∧
        first.rawAge = 0 ∧
        second.rawAge = 1 ∧
        first.linkIndex ≠ second.linkIndex ∧
        unionFinal.core.representative first.rawAge = 0 ∧
        unionFinal.core.representative second.rawAge = 0 ∧
        first.RealizedIn unionFinal ∧
        second.RealizedIn unionFinal ∧
        EventsShareFinalAccountedOwner first second := by
  rcases initializeReservation?_some_iff.mp unionInitial_eq with
    ⟨initialStep⟩
  rcases (dispatch?_some_iff unionInitial_invariant).mp
      unionFirstDispatch_eq with
    ⟨firstDispatch⟩
  rcases firstDispatch.tagEvidence with ⟨firstEvidence⟩
  cases firstEvidence with
  | new newStep =>
      rcases (dispatch?_some_iff unionAfterNew_invariant).mp
          unionSecondDispatch_eq with
        ⟨secondDispatch⟩
      rcases secondDispatch.tagEvidence with ⟨secondEvidence⟩
      cases secondEvidence with
      | unifyPayload unifyStep =>
          let firstHistory :=
            ExecutedHistory.later (ExecutedHistory.init initialStep)
              unionInitial_invariant firstDispatch
          let history :=
            ExecutedHistory.later firstHistory unionAfterNew_invariant
              secondDispatch
          let tagHistory : CanonicalTagHistory unionCertificate history :=
            CanonicalTagHistory.later
              (CanonicalTagHistory.later
                (CanonicalTagHistory.init initialStep) (.new newStep))
              (.unifyPayload unifyStep)
          let first : ReservationEvent unionCertificate :=
            .initial initialStep
          let second : ReservationEvent unionCertificate := .new newStep
          have ledger : tagHistory.reservationLedger = [first, second] := rfl
          have firstMembership : first ∈ tagHistory.reservationLedger := by
            rw [ledger]
            simp
          have secondMembership : second ∈ tagHistory.reservationLedger := by
            rw [ledger]
            simp
          have firstAge : first.rawAge = 0 := rfl
          have secondAge : second.rawAge = 1 := by
            change unionInitial.stack.nextAge = 1
            native_decide
          have firstRepresentative :
              unionFinal.core.representative first.rawAge = 0 := by
            rw [firstAge]
            native_decide
          have secondRepresentative :
              unionFinal.core.representative second.rawAge = 0 := by
            rw [secondAge]
            native_decide
          have ledgerLinksNodup :
              (tagHistory.reservationLedger.map
                ReservationEvent.linkIndex).Nodup := by
            rw [tagHistory.reservationLedger_linkIndices]
            exact ProofNetIR.Graph.nodup_reverse_of_nodup _
              tagHistory.linkIndices_nodup
          have distinctLinks : first.linkIndex ≠ second.linkIndex := by
            simpa [ledger] using ledgerLinksNodup
          have firstRealized : first.RealizedIn unionFinal :=
            tagHistory.reservationLedger_realized
              unionCertificate_structural firstMembership
          have secondRealized : second.RealizedIn unionFinal :=
            tagHistory.reservationLedger_realized
              unionCertificate_structural secondMembership
          rcases tagHistory.reservationLedger_axiomEndpoints_accounted
              unionCertificate_structural firstMembership with
            ⟨firstComponent, firstUsed, firstForestUsed, firstOwned,
              firstLookup, firstDerivation, firstLink, firstForest,
              firstAccounted, firstLeft, firstRight⟩
          rcases tagHistory.reservationLedger_axiomEndpoints_accounted
              unionCertificate_structural secondMembership with
            ⟨secondComponent, secondUsed, _secondForestUsed, secondOwned,
              secondLookup, secondDerivation, secondLink, _secondForest,
              _secondAccounted, secondLeft, secondRight⟩
          rw [firstRepresentative] at firstLookup firstAccounted
          rw [secondRepresentative] at secondLookup
          have componentEq : secondComponent = firstComponent := by
            have nested :
                some (some firstComponent) = some (some secondComponent) :=
              firstLookup.symm.trans secondLookup
            exact Option.some.inj (Option.some.inj nested.symm)
          subst secondComponent
          have ownedEq : secondOwned = firstOwned :=
            Certificate.OccurrenceDerivation.owned_unique
              unionCertificate_structural secondDerivation firstDerivation
          subst secondOwned
          refine ⟨history, tagHistory, first, second,
            unionCertificate_declarativelyCorrect, ledger, firstAge,
            secondAge, distinctLinks, firstRepresentative,
            secondRepresentative, firstRealized, secondRealized, ?_⟩
          exact ⟨firstComponent, firstUsed, secondUsed, firstForestUsed,
            firstOwned, firstLookup, firstDerivation, firstLink,
            secondDerivation, secondLink, firstForest, firstAccounted,
            firstLeft, firstRight, secondLeft, secondRight⟩

end ProofNetIRReservationRealizationTests

def main : IO Unit :=
  IO.println "Figure-7 final reservation realization consumers passed"
