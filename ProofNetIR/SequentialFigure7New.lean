import ProofNetIR.SequentialConsumerIndex
import ProofNetIR.SequentialSchedulerBridge

namespace ProofNetIR

/-!
# Executable Figure-7 `new`

This module composes the already separated scheduler operations using the
project's documented operational interpretation of Guerrini's Figure 7:

1. remove one occurrence from the top ready bucket and mark it with the old
   top raw age;
2. inspect the exact tensor consuming that occurrence;
3. run `NEXTAXIOM` from the still-unmarked opposite tensor premise, using the
   production state *after* the raw mark;
4. append the fresh `sigma`/ready reservation, initialize the old active
   waiting boundary while leaving the fresh top undefined, and reserve the
   exact submitted axiom found by that search.

The executable driver deterministically chooses the first element of the last
ready bucket.  Figure 7 permits any member of that top set; this module is one
deterministic refinement, not yet a proof that every reachable nonterminal
state admits this rule or that the complete scheduler is live.  Its input
proof is the current reservation-layer invariant, not yet a reachable-state
certificate: that invariant aligns carriers, raw ages, and the initialized
waiting-cell domain, but does not yet prove tag monotonicity/provenance, global
ready/waiting payload ownership, or a complete search history.
-/

namespace SequentialUnification

/-- A successful bounded `NEXTAXIOM` call passed its first dynamic guard: the
starting occurrence was in bounds and unmarked in the exact input production
state. -/
theorem nextAxiomWithFuel?_startReady
    {certificate : Certificate} {state : UnificationState}
    {index : SourceIndex} {fuel : Nat} {tags : Array Bool}
    {indexSound : SourceIndex.Sound certificate index}
    {start : Vertex}
    {result : NextAxiomResult certificate state fuel tags}
    (equation :
      nextAxiomWithFuel? certificate state index indexSound
          fuel tags start =
        some result) :
    state.marks[start]? = some none := by
  cases fuel with
  | zero =>
      simp [nextAxiomWithFuel?] at equation
  | succ remaining =>
      by_cases tagReady : tags[start]? = some false
      · by_cases markReady : state.marks[start]? = some none
        · exact markReady
        · simp [nextAxiomWithFuel?, tagReady, markReady] at equation
      · simp [nextAxiomWithFuel?, tagReady] at equation

/-- Production-wrapper form of `nextAxiomWithFuel?_startReady`. -/
theorem nextAxiom?_startReady
    {certificate : Certificate} {state : UnificationState}
    {index : SourceIndex} {tags : Array Bool}
    {indexSound : SourceIndex.Sound certificate index}
    {start : Vertex}
    {result :
      NextAxiomResult certificate state certificate.formulas.size tags}
    (equation :
      nextAxiom? certificate state index indexSound tags start =
        some result) :
    state.marks[start]? = some none := by
  exact nextAxiomWithFuel?_startReady (by
    simpa [nextAxiom?] using equation)

end SequentialUnification

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- Execute the deterministic-head operational interpretation of Figure-7
`new`.

The input proof binds the executable pipeline to the synchronized
reservation-layer state: in particular the stack horizon/raw ages and the
production parent carrier cannot be forged independently.  The consumer
lookup is fixed to the certificate's sound-and-complete public
`consumerIndex`; callers cannot substitute a partial or forged table.  The
source index used by `NEXTAXIOM` remains its distinct producer/axiom-incidence
index.  Every query fails closed; no eager marking operation, waiting-list
drain, connective firing, or union is hidden in this transition.

Success is therefore the exact local operational rule over the currently
proved reservation layer.  The 1999 printed fresh-cell assignment is retained
separately by `newEnqueue?`; this transition instead initializes the old active
boundary and leaves the fresh top undefined.  It is not by itself a
reachability, progress, or no-repeated-axiom theorem. -/
def new? (certificate : Certificate)
    (before : ReservationState)
    (_invariant : ReservationInvariant certificate before) :
    Option ReservationState :=
  match before.stack.popReadyMark? with
  | .error _ => none
  | .ok stackResult =>
      match
          before.core.markReadyRaw?
            stackResult.vertex stackResult.rawAge with
      | .error _ => none
      | .ok coreMarked => do
          let tensor ←
            certificate.tensorBelow? stackResult.vertex
          let search ←
            SequentialUnification.nextAxiom? certificate coreMarked
              (SequentialUnification.sourceIndex certificate)
              (SequentialUnification.sourceIndex_sound certificate)
              before.tags tensor.mate
          let (reached, partner) ← search.orientedEndpoints?
          let stackAfter ←
            stackResult.after.operationalNewEnqueue? reached partner
          let coreAfter ←
            certificate.reserveAxiomAt? coreMarked search.linkIndex
          some {
            stack := stackAfter
            core := coreAfter
            tags := search.tags }

/-- Proof-relevant exact specification of one successful deterministic
Figure-7 `new` transition.

The type of `search` mentions `coreMarked`, so the witness records the
mathematically material ordering: `u₁` is raw-marked before `NEXTAXIOM(u₂)` is
evaluated.  `before_invariant` prevents independent stack/core/raw-age
forgeries, while the stronger reachable-scheduler invariant remains future
work. -/
structure NewStep (certificate : Certificate)
    (before after : ReservationState) : Type where
  before_invariant : ReservationInvariant certificate before
  stackResult : PopReadyMarkResult
  coreMarked : UnificationState
  tensor : TensorBelow
  search :
    SequentialUnification.NextAxiomResult certificate coreMarked
      certificate.formulas.size before.tags
  reached : Vertex
  partner : Vertex
  stackAfter : SequentialStackState
  coreAfter : UnificationState
  stack_eq :
    before.stack.popReadyMark? = .ok stackResult
  core_mark_eq :
    before.core.markReadyRaw?
        stackResult.vertex stackResult.rawAge =
      .ok coreMarked
  tensor_eq :
    certificate.tensorBelow? stackResult.vertex =
      some tensor
  search_eq :
    SequentialUnification.nextAxiom? certificate coreMarked
        (SequentialUnification.sourceIndex certificate)
        (SequentialUnification.sourceIndex_sound certificate)
        before.tags tensor.mate =
      some search
  oriented_eq :
    search.orientedEndpoints? = some (reached, partner)
  stack_enqueue_eq :
    stackResult.after.operationalNewEnqueue? reached partner =
      some stackAfter
  core_reserve_eq :
    certificate.reserveAxiomAt? coreMarked search.linkIndex =
      some coreAfter
  output_eq :
    after = {
      stack := stackAfter
      core := coreAfter
      tags := search.tags }

/-- Executable success is equivalent to the exact dependent Figure-7 `new`
witness. -/
theorem new?_some_iff
    {certificate : Certificate}
    {before after : ReservationState}
    (invariant : ReservationInvariant certificate before) :
    new? certificate before invariant = some after ↔
      Nonempty (NewStep certificate before after) := by
  constructor
  · intro equation
    unfold new? at equation
    cases stackEquation : before.stack.popReadyMark? with
    | error stackError =>
        simp [stackEquation] at equation
    | ok stackResult =>
        cases coreEquation :
            before.core.markReadyRaw?
              stackResult.vertex stackResult.rawAge with
        | error coreError =>
            simp [stackEquation, coreEquation] at equation
        | ok coreMarked =>
            cases tensorEquation :
                certificate.tensorBelow? stackResult.vertex with
            | none =>
                simp [stackEquation, coreEquation, tensorEquation] at equation
            | some tensor =>
                cases searchEquation :
                    SequentialUnification.nextAxiom? certificate coreMarked
                      (SequentialUnification.sourceIndex certificate)
                      (SequentialUnification.sourceIndex_sound certificate)
                      before.tags tensor.mate with
                | none =>
                    simp [stackEquation, coreEquation, tensorEquation,
                      searchEquation] at equation
                | some search =>
                    cases orientedEquation :
                        search.orientedEndpoints? with
                    | none =>
                        simp [stackEquation, coreEquation, tensorEquation,
                          searchEquation, orientedEquation] at equation
                    | some endpoints =>
                        rcases endpoints with ⟨reached, partner⟩
                        cases stackEnqueueEquation :
                            stackResult.after.operationalNewEnqueue?
                              reached partner with
                        | none =>
                            simp [stackEquation, coreEquation, tensorEquation,
                              searchEquation, orientedEquation,
                              stackEnqueueEquation] at equation
                        | some stackAfter =>
                            cases coreReserveEquation :
                                certificate.reserveAxiomAt? coreMarked
                                  search.linkIndex with
                            | none =>
                                simp [stackEquation, coreEquation,
                                  tensorEquation, searchEquation,
                                  orientedEquation,
                                  coreReserveEquation] at equation
                            | some coreAfter =>
                                simp [stackEquation, coreEquation,
                                  tensorEquation, searchEquation,
                                  orientedEquation, stackEnqueueEquation,
                                  coreReserveEquation] at equation
                                subst after
                                exact ⟨{
                                  before_invariant := invariant
                                  stackResult
                                  coreMarked
                                  tensor
                                  search
                                  reached
                                  partner
                                  stackAfter
                                  coreAfter
                                  stack_eq := stackEquation
                                  core_mark_eq := coreEquation
                                  tensor_eq := tensorEquation
                                  search_eq := searchEquation
                                  oriented_eq := orientedEquation
                                  stack_enqueue_eq := stackEnqueueEquation
                                  core_reserve_eq := coreReserveEquation
                                  output_eq := rfl }⟩
  · rintro ⟨step⟩
    rcases step with
      ⟨stepInvariant, stackResult, coreMarked, tensor, search, reached, partner,
        stackAfter, coreAfter, stackEquation, coreEquation,
        tensorEquation, searchEquation, orientedEquation,
        stackEnqueueEquation, coreReserveEquation, outputEquation⟩
    subst after
    simp [new?, stackEquation, coreEquation, tensorEquation,
      searchEquation, orientedEquation, stackEnqueueEquation,
      coreReserveEquation]

namespace NewStep

/-- The exact tensor below the selected occurrence, including its stored
orientation and opposite premise. -/
theorem tensorValid
    {certificate : Certificate}
    {before after : ReservationState}
    (step : NewStep certificate before after) :
    step.tensor.Valid certificate certificate.consumerIndex
      step.stackResult.vertex :=
  Certificate.tensorBelow?_eq_some_iff.mp step.tensor_eq

/-- Figure 7's dynamic side condition `μ(u₂) = ⊥` holds in the state after
marking `u₁` and before searching from `u₂`. -/
theorem mate_unmarked
    {certificate : Certificate}
    {before after : ReservationState}
    (step : NewStep certificate before after) :
    step.coreMarked.marks[step.tensor.mate]? = some none :=
  SequentialUnification.nextAxiom?_startReady step.search_eq

/-- The successful search records the exact source-left route from the
opposite tensor premise to the reached endpoint of the newly reserved axiom. -/
theorem route
    {certificate : Certificate}
    {before after : ReservationState}
    (step : NewStep certificate before after) :
    SequentialUnification.NextAxiomRoute step.tensor.mate step.search
      step.reached step.partner := by
  rcases SequentialUnification.nextAxiom?_route step.search_eq with
    ⟨reached, partner, route⟩
  have endpoints :=
    route.orientedEndpoints?_eq.symm.trans step.oriented_eq
  have pairEquation :
      (reached, partner) = (step.reached, step.partner) :=
    Option.some.inj endpoints
  cases pairEquation
  exact route

/-- The common pop/raw-mark prefix packaged as the exact bridge state expected
by the existing later-reservation theorem. -/
def markedMiddle
    {certificate : Certificate}
    {before after : ReservationState}
    (step : NewStep certificate before after) :
    ReservationState where
  stack := step.stackResult.after
  core := step.coreMarked
  tags := before.tags

/-- One full `new` witness contains an exact later reservation step from its
already-marked middle state. -/
def reservationStep
    {certificate : Certificate}
    {before after : ReservationState}
    (step : NewStep certificate before after) :
    NewReservationStep certificate step.markedMiddle after
      step.tensor.mate where
  result := step.search
  reached := step.reached
  partner := step.partner
  stackAfter := step.stackAfter
  coreAfter := step.coreAfter
  search_eq := step.search_eq
  oriented_eq := step.oriented_eq
  stack_eq := step.stack_enqueue_eq
  core_eq := step.core_reserve_eq
  output_eq := step.output_eq

/-- The synchronized pop/raw-mark prefix preserves the reservation-layer
invariant. -/
theorem markedMiddle_reservationInvariant
    {certificate : Certificate}
    {before after : ReservationState}
    (step : NewStep certificate before after) :
    ReservationInvariant certificate step.markedMiddle := by
  exact popReadyMark_markReadyRaw_reservationInvariant
    step.before_invariant step.stack_eq step.core_mark_eq

/-- Every successful deterministic Figure-7 `new` transition preserves the
complete invariant currently established for the reservation layer.

This is preservation, not progress: it assumes the executable transition
succeeds and does not yet prove that a correct reachable state must select
`new` or that `NEXTAXIOM` is total there. -/
theorem reservationInvariant
    {certificate : Certificate}
    {before after : ReservationState}
    (step : NewStep certificate before after) :
    ReservationInvariant certificate after :=
  step.reservationStep.reservationInvariant
    step.markedMiddle_reservationInvariant

end NewStep

/-- Success of the executable composed local `new` transition preserves the
current reservation invariant. -/
theorem new?_reservationInvariant
    {certificate : Certificate}
    {before after : ReservationState}
    (invariant : ReservationInvariant certificate before)
    (equation : new? certificate before invariant = some after) :
    ReservationInvariant certificate after := by
  rcases (new?_some_iff invariant).mp equation with ⟨step⟩
  exact step.reservationInvariant

end SequentialFigure7

end ProofNetIR
