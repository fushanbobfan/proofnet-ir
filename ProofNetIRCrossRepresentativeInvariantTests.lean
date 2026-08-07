import ProofNetIR.SequentialFigure7CrossRepresentativeInvariant

namespace ProofNetIRCrossRepresentativeInvariantTests

open ProofNetIR
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialUnification

/-! ## Public future-work and candidate consumers -/

example {state : ReservationState} {position : Nat}
    {rawAge : RawTokenAge} {bucket : List Vertex} {vertex : Vertex}
    (sigmaAt : state.stack.sigma[position]? = some rawAge)
    (readyAt : state.stack.ready[position]? = some bucket)
    (member : vertex ∈ bucket) :
    FutureWorkAt state rawAge vertex :=
  .ready sigmaAt readyAt member

example {state : ReservationState} {rawAge : RawTokenAge}
    {payload : List Vertex} {vertex : Vertex}
    (waitingAt : state.stack.waiting[rawAge]? =
      some (.initialized payload))
    (member : vertex ∈ payload) :
    FutureWorkAt state rawAge vertex :=
  .waiting waitingAt member

example {state : ReservationState} {rawAge : RawTokenAge}
    {vertex : Vertex} (work : FutureWorkAt state rawAge vertex) :
    vertex ∈ state.stack.queuedVertices :=
  work.mem_queued

example {certificate : Certificate} {state : ReservationState}
    {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt state rawAge vertex)
    (invariant : SchedulerInvariant certificate state) :
    rawAge ∈ state.stack.sigma ∧
      rawAge < state.stack.nextAge ∧
      state.core.representative rawAge = rawAge :=
  ⟨work.rawAge_mem_sigma invariant, work.rawAge_lt_nextAge invariant,
    work.representative_eq_rawAge invariant⟩

example {certificate : Certificate} {before : ReservationState}
    (input : ReadyHeadInput before)
    (invariant : SchedulerInvariant certificate before) :
    FutureWorkAt before input.rawAge input.vertex :=
  input.futureWorkAt invariant

example {certificate : Certificate} {before : ReservationState}
    (guard : NewGuard certificate before)
    (invariant : SchedulerInvariant certificate before) :
    FutureNewCandidateAt certificate before :=
  guard.futureNewCandidateAt invariant

/-! ## Public source-region separation consumers -/

example {certificate : Certificate} {first second : Vertex}
    (disjoint : SourceLeftRegionsDisjoint certificate first second) :
    SourceLeftRegionsDisjoint certificate second first :=
  disjoint.symm

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (separated : OlderSourceRegionSeparated tagHistory)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    (candidate : FutureNewCandidateAt certificate state)
    (older :
      state.core.representative event.rawAge <
        state.core.representative candidate.rawAge)
    {vertex : Vertex} (touched : event.Touched vertex)
    (candidateRegion :
      SourceLeftRegionVertex certificate candidate.tensor.mate vertex) :
    False :=
  separated.not_event_touch_of_lt eventMembership candidate older touched
    candidateRegion

example (certificate : Certificate) :
    OlderSourceRegionSeparated
      (CanonicalTagHistory.empty :
        CanonicalTagHistory certificate
          (ExecutedHistory.empty : ExecutedHistory certificate
            (ReservationState.empty certificate))) :=
  empty_olderSourceRegionSeparated certificate

/-! ## Executable singleton-ledger regression -/

private def axiomCertificate : Certificate where
  formulas := #[.atom "p" true, .atom "p" false]
  links := [.axiom 0 1]
  conclusions := [0, 1]

private theorem axiomCertificate_structural :
    axiomCertificate.StructurallyWellFormed := by
  exact
    (Certificate.wellFormed_iff_structurallyWellFormed
      axiomCertificate).mp (by native_decide)

private def axiomInitial : ReservationState :=
  match initializeReservation? axiomCertificate 0 with
  | some state => state
  | none => ReservationState.empty axiomCertificate

private theorem axiomInitial_eq :
    initializeReservation? axiomCertificate 0 = some axiomInitial := by
  native_decide

/- A real initialization yields the singleton-ledger separation theorem;
the strict representative premise is impossible at its only boundary. -/
private theorem axiom_initial_separation_regression :
    ∃ step : InitialReservationStep axiomCertificate axiomInitial 0,
      OlderSourceRegionSeparated (CanonicalTagHistory.init step) := by
  rcases initializeReservation?_some_iff.mp axiomInitial_eq with ⟨step⟩
  exact ⟨step,
    ProofNetIR.SequentialFigure7.InitialReservationStep.olderSourceRegionSeparated
      step axiomCertificate_structural⟩

end ProofNetIRCrossRepresentativeInvariantTests

def main : IO Unit :=
  IO.println "Figure-7 cross-representative invariant consumers passed"
