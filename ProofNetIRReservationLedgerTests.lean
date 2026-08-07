import ProofNetIR.SequentialFigure7ReservationLedger

namespace ProofNetIRReservationLedgerTests

open ProofNetIR
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialUnification

/- A `new` step's selected active age is strictly older than the fresh raw
age recorded by its reservation event. -/
example {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    step.stackResult.rawAge < (ReservationEvent.new step).rawAge :=
  step.activeRawAge_lt_reservationRawAge

/- The chronological ledger has exactly one entry at every allocated raw
age. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history) :
    tagHistory.reservationLedger.map ReservationEvent.rawAge =
      List.range state.stack.nextAge :=
  tagHistory.reservationLedger_rawAges

/- The legacy newest-first submitted-slot list is exactly reversed by the
chronological ledger. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history) :
    tagHistory.reservationLedger.map ReservationEvent.linkIndex =
      tagHistory.linkIndices.reverse :=
  tagHistory.reservationLedger_linkIndices

/- An in-bounds raw age returns an exact event carrying that allocation-time
age. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (rawAge : RawTokenAge) (bound : rawAge < state.stack.nextAge) :
    ∃ event : ReservationEvent certificate,
      tagHistory.reservationLedger[rawAge]? = some event ∧
        event.rawAge = rawAge :=
  tagHistory.reservationLedger_eventAtRawAge rawAge bound

/- A global canonical touch is attributed to one exact event in the
chronological ledger, without selecting a current component owner. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {vertex : Vertex} (touched : tagHistory.Touched vertex) :
    ∃ event : ReservationEvent certificate,
      event ∈ tagHistory.reservationLedger ∧ event.Touched vertex :=
  tagHistory.touched_reservationLedger_event touched

private def repeatedLedgerCertificate : Certificate where
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

private theorem repeatedLedgerCertificate_structural :
    repeatedLedgerCertificate.StructurallyWellFormed := by
  exact
    (Certificate.wellFormed_iff_structurallyWellFormed
      repeatedLedgerCertificate).mp (by native_decide)

private def repeatedLedgerInitial : ReservationState :=
  match initializeReservation? repeatedLedgerCertificate 0 with
  | some state => state
  | none => ReservationState.empty repeatedLedgerCertificate

private theorem repeatedLedgerInitial_eq :
    initializeReservation? repeatedLedgerCertificate 0 =
      some repeatedLedgerInitial := by
  native_decide

private theorem repeatedLedgerInitial_invariant :
    SchedulerInvariant repeatedLedgerCertificate repeatedLedgerInitial := by
  rcases initializeReservation?_some_iff.mp repeatedLedgerInitial_eq with
    ⟨step⟩
  exact step.schedulerInvariant repeatedLedgerCertificate_structural

private def repeatedLedgerAfterNew : ReservationState :=
  match
      new? repeatedLedgerCertificate repeatedLedgerInitial
        repeatedLedgerInitial_invariant.toReservationInvariant with
  | some state => state
  | none => ReservationState.empty repeatedLedgerCertificate

private theorem repeatedLedgerDispatch_eq :
    dispatch? repeatedLedgerCertificate repeatedLedgerInitial
        repeatedLedgerInitial_invariant =
      some ⟨.new, repeatedLedgerAfterNew⟩ := by
  native_decide

private theorem repeatedLedgerAfterNew_nextAge :
    repeatedLedgerAfterNew.stack.nextAge = 2 := by
  native_decide

/- A closed, executable initialization followed by the canonical `new`
dispatcher branch builds one authentic canonical history.  Its reservation
ledger records ages `[0, 1]` and the two submitted axiom slots `[0, 1]` in
actual execution order.  The same concrete `NewStep` also consumes the
strict old-active-age versus fresh-reservation-age theorem. -/
set_option maxHeartbeats 800000 in
private theorem repeatedLedger_init_new_regression :
    ∃ (history : ExecutedHistory repeatedLedgerCertificate
          repeatedLedgerAfterNew)
      (tagHistory : CanonicalTagHistory repeatedLedgerCertificate history)
      (step : NewStep repeatedLedgerCertificate repeatedLedgerInitial
        repeatedLedgerAfterNew),
      tagHistory.reservationLedger.map ReservationEvent.rawAge = [0, 1] ∧
        tagHistory.reservationLedger.map ReservationEvent.linkIndex = [0, 1] ∧
        step.stackResult.rawAge < (ReservationEvent.new step).rawAge ∧
        ReservationEvent.new step ∈ tagHistory.reservationLedger := by
  rcases initializeReservation?_some_iff.mp repeatedLedgerInitial_eq with
    ⟨initialStep⟩
  rcases
      (dispatch?_some_iff repeatedLedgerInitial_invariant).mp
        repeatedLedgerDispatch_eq with
    ⟨dispatchStep⟩
  rcases dispatchStep.tagEvidence with ⟨evidence⟩
  cases evidence with
  | new newStep =>
      let history :=
        ExecutedHistory.later (ExecutedHistory.init initialStep)
          repeatedLedgerInitial_invariant dispatchStep
      let tagHistory :
          CanonicalTagHistory repeatedLedgerCertificate history :=
        CanonicalTagHistory.later (CanonicalTagHistory.init initialStep)
          (.new newStep)
      have initialSearchLink :
          Option.map (fun result => result.linkIndex)
              (nextAxiom? repeatedLedgerCertificate
                (ReservationState.empty repeatedLedgerCertificate).core
                (sourceIndex repeatedLedgerCertificate)
                (sourceIndex_sound repeatedLedgerCertificate)
                (ReservationState.empty repeatedLedgerCertificate).tags 0) =
            some 0 := by
        native_decide
      rw [initialStep.search_eq] at initialSearchLink
      have initialLink : initialStep.result.linkIndex = 0 := by
        simpa using Option.some.inj initialSearchLink
      have linkBound :
          newStep.search.linkIndex < repeatedLedgerCertificate.links.length := by
        rcases List.getElem?_eq_some_iff.mp newStep.search.exactLink with
          ⟨bound, _lookup⟩
        exact bound
      have newLinkNeInitial :
          newStep.search.linkIndex ≠ initialStep.result.linkIndex := by
        have nodup := tagHistory.linkIndices_nodup
        simpa [tagHistory, CanonicalTagHistory.linkIndices,
          DispatchTagEvidence.linkIndices] using nodup
      have newLinkNeTwo : newStep.search.linkIndex ≠ 2 := by
        intro linkEq
        have exactLink := newStep.search.exactLink
        rw [linkEq] at exactLink
        simp [repeatedLedgerCertificate] at exactLink
      have newLink : newStep.search.linkIndex = 1 := by
        rw [initialLink] at newLinkNeInitial
        simp [repeatedLedgerCertificate] at linkBound
        omega
      have rawAges := tagHistory.reservationLedger_rawAges
      rw [repeatedLedgerAfterNew_nextAge] at rawAges
      have links :
          tagHistory.reservationLedger.map ReservationEvent.linkIndex =
            [initialStep.result.linkIndex, newStep.search.linkIndex] := by
        rfl
      rw [initialLink, newLink] at links
      have rangeTwo : List.range 2 = [0, 1] := by native_decide
      have currentMembership :
          ReservationEvent.new newStep ∈
            (DispatchTagEvidence.new newStep).reservationEvents := by
        simp [DispatchTagEvidence.reservationEvents]
      have ledgerMembership :
          ReservationEvent.new newStep ∈ tagHistory.reservationLedger := by
        apply List.mem_append_right
        exact currentMembership
      exact ⟨history, tagHistory, newStep, rawAges.trans rangeTwo, links,
        newStep.activeRawAge_lt_reservationRawAge, ledgerMembership⟩

end ProofNetIRReservationLedgerTests

def main : IO Unit :=
  IO.println "Figure-7 raw-age reservation-ledger consumers passed"
