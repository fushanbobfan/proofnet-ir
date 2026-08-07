import ProofNetIR.SequentialFigure7RegionBoundaries
import ProofNetIR.SequentialFigure7ReservationLedger

namespace ProofNetIRRegionBoundariesTests

open ProofNetIR
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerState.SequentialStackState
open ProofNetIR.SequentialUnification

/- The positive API is intentionally conditional on an already existing exact
run.  It does not turn `NewGuard` into that run. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {runState : UnificationState} {fuel : Nat}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate runState fuel state.tags start
      trace reached partner linkIndex)
    {vertex : Vertex}
    (carrier : ExactFreshSourceLeftRunCarrier run vertex) :
    ¬ tagHistory.Touched vertex :=
  tagHistory.freshSourceLeftRun_carrier_not_touched run carrier

/- The raw-owner boundary likewise consumes the exact run in the selected
head's marked core; the theorem does not manufacture it from `guard`. -/
example {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {fuel : Nat} {reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate guard.head.markedCore fuel
      before.tags guard.tensor.mate trace reached partner linkIndex)
    {vertex : Vertex}
    (carrier : ExactFreshSourceLeftRunCarrier run vertex) :
    ¬ ExactMarkedOccurrenceOwner certificate before.core vertex :=
  carrier_not_exactMarkedOccurrenceOwner invariant guard run carrier

/-! ## Counterexample 1: historical touch and current owner can overlap -/

private def overlapAtom : Formula := .atom "p" true

private def overlapCertificate : Certificate where
  formulas := #[
    overlapAtom,
    overlapAtom.dual,
    overlapAtom,
    overlapAtom.dual,
    .tensor overlapAtom overlapAtom]
  links := [
    .axiom 0 1,
    .axiom 2 3,
    .tensor 0 2 4]
  conclusions := [4, 1, 3]

private theorem overlapCertificate_correct :
    overlapCertificate.DeclarativelyCorrect :=
  overlapCertificate.check_iff_declarativelyCorrect.mp (by native_decide)

private theorem overlapCertificate_structural :
    overlapCertificate.StructurallyWellFormed :=
  overlapCertificate_correct.1

private def overlapInitial : ReservationState :=
  match initializeReservation? overlapCertificate 0 with
  | some state => state
  | none => ReservationState.empty overlapCertificate

private theorem overlapInitial_eq :
    initializeReservation? overlapCertificate 0 = some overlapInitial := by
  native_decide

private theorem overlapInitial_invariant :
    SchedulerInvariant overlapCertificate overlapInitial :=
  initializeReservation?_schedulerInvariant overlapCertificate_structural
    overlapInitial_eq

private def overlapAfterNew : ReservationState :=
  match
      new? overlapCertificate overlapInitial
        overlapInitial_invariant.toReservationInvariant with
  | some state => state
  | none => ReservationState.empty overlapCertificate

private theorem overlapDispatch_eq :
    dispatch? overlapCertificate overlapInitial overlapInitial_invariant =
      some ⟨.new, overlapAfterNew⟩ := by
  native_decide

/- This is a checker-accepted certificate and a genuine canonical
initialization-then-`new` history.  Vertex `0` was touched by initialization
and, after the `new` step consumes it, is also raw-marked with an exact live
component owner.  Hence prior touch and `ExactMarkedOccurrenceOwner` are
overlapping provenance classes, not disjoint alternatives. -/
set_option maxHeartbeats 800000 in
private theorem canonical_touch_and_owner_overlap :
    overlapCertificate.DeclarativelyCorrect ∧
      ∃ (history : ExecutedHistory overlapCertificate overlapAfterNew)
        (tagHistory : CanonicalTagHistory overlapCertificate history),
        tagHistory.Touched 0 ∧
          ExactMarkedOccurrenceOwner overlapCertificate
            overlapAfterNew.core 0 := by
  refine ⟨overlapCertificate_correct, ?_⟩
  rcases initializeReservation?_some_iff.mp overlapInitial_eq with
    ⟨initialStep⟩
  rcases
      (dispatch?_some_iff overlapInitial_invariant).mp overlapDispatch_eq with
    ⟨dispatchStep⟩
  rcases dispatchStep.tagEvidence with ⟨evidence⟩
  cases evidence with
  | new newStep =>
      let history : ExecutedHistory overlapCertificate overlapAfterNew :=
        ExecutedHistory.later (ExecutedHistory.init initialStep)
          overlapInitial_invariant dispatchStep
      let tagHistory : CanonicalTagHistory overlapCertificate history :=
        CanonicalTagHistory.later (CanonicalTagHistory.init initialStep)
          (.new newStep)
      have invariant :
          SchedulerInvariant overlapCertificate overlapAfterNew :=
        history.schedulerInvariant overlapCertificate_structural
      have tagged : overlapAfterNew.tags[0]? = some true := by
        native_decide
      have marked : overlapAfterNew.core.marks[0]? = some (some 0) := by
        native_decide
      exact ⟨history, tagHistory,
        tagHistory.tagged_iff_touched.mp tagged,
        ProofNetIR.SequentialFigure7.SchedulerInvariant.exactMarkedOccurrenceOwner
          invariant marked⟩

/- Keep the counterexample theorem itself consumed by the test module. -/
example :
    overlapCertificate.DeclarativelyCorrect ∧
      ∃ (history : ExecutedHistory overlapCertificate overlapAfterNew)
        (tagHistory : CanonicalTagHistory overlapCertificate history),
        tagHistory.Touched 0 ∧
          ExactMarkedOccurrenceOwner overlapCertificate
            overlapAfterNew.core 0 :=
  canonical_touch_and_owner_overlap

/-! ## Counterexample 2: an event touch need not be final-component-owned -/

private def deepP : Formula := .atom "p" true
private def deepQ : Formula := .atom "q" true
private def deepR : Formula := .atom "r" true

private def deepTraceCertificate : Certificate where
  formulas := #[
    deepP,
    deepP.dual,
    deepQ,
    deepQ.dual,
    deepR,
    deepR.dual,
    .tensor deepP deepQ,
    .tensor (.tensor deepP deepQ) deepR]
  links := [
    .axiom 0 1,
    .axiom 2 3,
    .axiom 4 5,
    .tensor 0 2 6,
    .tensor 6 4 7]
  conclusions := [7, 1, 3, 5]

private theorem deepTraceCertificate_correct :
    deepTraceCertificate.DeclarativelyCorrect :=
  deepTraceCertificate.check_iff_declarativelyCorrect.mp (by native_decide)

private def deepTraceInitial : ReservationState :=
  match initializeReservation? deepTraceCertificate 7 with
  | some state => state
  | none => ReservationState.empty deepTraceCertificate

private theorem deepTraceInitial_eq :
    initializeReservation? deepTraceCertificate 7 = some deepTraceInitial := by
  native_decide

private def deepTraceInitialComponent : UnificationComponent where
  tree := .axiom "p" true
  frontier := [0, 1]

/- The initialization search starts at outer tensor conclusion `7`, follows
the exact source-left trace `7, 6, 0`, and reserves axiom `(0, 1)`.  Thus `7`
is an authentic event touch, but it remains raw-unmarked and is not owned by
the final component installed for this event's raw age.  Historical search
trace provenance therefore cannot be collapsed into current component
ownership. -/
set_option maxHeartbeats 800000 in
private theorem canonical_touch_without_final_component_ownership :
    deepTraceCertificate.DeclarativelyCorrect ∧
      ∃ (initialStep : InitialReservationStep deepTraceCertificate
          deepTraceInitial 7),
        let history : ExecutedHistory deepTraceCertificate deepTraceInitial :=
          ExecutedHistory.init initialStep
        let tagHistory : CanonicalTagHistory deepTraceCertificate history :=
          CanonicalTagHistory.init initialStep
        let event : ReservationEvent deepTraceCertificate :=
          .initial initialStep
        event ∈ tagHistory.reservationLedger ∧
          event.Touched 7 ∧
          tagHistory.Touched 7 ∧
          ¬ ExactMarkedOccurrenceOwner deepTraceCertificate
              deepTraceInitial.core 7 ∧
          ¬ ∃ (component : UnificationComponent)
              (usedLinks owned : List Nat),
              deepTraceInitial.core.components[
                  deepTraceInitial.core.representative event.rawAge]? =
                some (some component) ∧
              Certificate.ComponentOccurrenceWitness deepTraceCertificate
                component usedLinks owned ∧
              7 ∈ owned := by
  refine ⟨deepTraceCertificate_correct, ?_⟩
  rcases initializeReservation?_some_iff.mp deepTraceInitial_eq with
    ⟨initialStep⟩
  refine ⟨initialStep, ?_⟩
  dsimp only
  have startMembership : 7 ∈ initialStep.result.trace := by
    rcases List.head?_eq_some_iff.mp initialStep.route.traceHead with
      ⟨tail, traceEquation⟩
    rw [traceEquation]
    simp
  have eventTouched :
      (ReservationEvent.initial initialStep).Touched 7 :=
    Or.inl startMembership
  have tagTouched :
      (CanonicalTagHistory.init initialStep).Touched 7 :=
    eventTouched
  have unmarked : deepTraceInitial.core.marks[7]? = some none := by
    native_decide
  refine ⟨by simp [CanonicalTagHistory.reservationLedger], eventTouched,
    tagTouched, ?_, ?_⟩
  · intro owner
    rcases owner with
      ⟨rawAge, _index, _component, _usedLinks, _owned, marked,
        _representative, _componentLookup, _componentWitness, _accounted,
        _ownedMembership⟩
    rw [unmarked] at marked
    simp at marked
  · rintro ⟨component, usedLinks, owned, componentLookup, witness,
      ownedMembership⟩
    have exactLookup :
        deepTraceInitial.core.components[
            deepTraceInitial.core.representative
              (ReservationEvent.initial initialStep).rawAge]? =
          some (some deepTraceInitialComponent) := by
      change
        deepTraceInitial.core.components[
            deepTraceInitial.core.representative 0]? =
          some (some deepTraceInitialComponent)
      native_decide
    rw [exactLookup] at componentLookup
    have componentEquation : component = deepTraceInitialComponent := by
      simpa using Option.some.inj (Option.some.inj componentLookup.symm)
    subst component
    cases witness.derivation with
    | «axiom» => simp at ownedMembership

/- Consume the full second boundary, including the exact event-relative
representative statement. -/
example :
    deepTraceCertificate.DeclarativelyCorrect ∧
      ∃ (initialStep : InitialReservationStep deepTraceCertificate
          deepTraceInitial 7),
        let history : ExecutedHistory deepTraceCertificate deepTraceInitial :=
          ExecutedHistory.init initialStep
        let tagHistory : CanonicalTagHistory deepTraceCertificate history :=
          CanonicalTagHistory.init initialStep
        let event : ReservationEvent deepTraceCertificate :=
          .initial initialStep
        event ∈ tagHistory.reservationLedger ∧
          event.Touched 7 ∧
          tagHistory.Touched 7 ∧
          ¬ ExactMarkedOccurrenceOwner deepTraceCertificate
              deepTraceInitial.core 7 ∧
          ¬ ∃ (component : UnificationComponent)
              (usedLinks owned : List Nat),
              deepTraceInitial.core.components[
                  deepTraceInitial.core.representative event.rawAge]? =
                some (some component) ∧
              Certificate.ComponentOccurrenceWitness deepTraceCertificate
                component usedLinks owned ∧
              7 ∈ owned :=
  canonical_touch_without_final_component_ownership

end ProofNetIRRegionBoundariesTests

def main : IO Unit :=
  IO.println "Figure-7 exact-run region boundaries passed"
