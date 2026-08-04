import ProofNetIR.SequentialFigure7History
import ProofNetIR.SequentialFigure7UnifyPayloadInvariant

namespace ProofNetIR

/-!
# Canonical executable dispatcher for the implemented Figure-7 rules

This module gives the currently implemented successful local rules one
canonical executable entry point and records exact dispatcher executions in a
proof-relevant history.  The dispatcher deliberately uses only the general
`unifyPayload?` branch.  The older empty- and singleton-payload executors remain
compatibility APIs, but admitting them here would give one empty or singleton
execution several history representations.

The fixed precedence is a representation choice: conclusion, par no-op,
tensor new, par wait, par forward, then general tensor unify.  The rule guards
make those branches semantically disjoint on intended states, but this module
does not use that fact to claim applicability.  A dispatcher result exists only
when one of the existing executors already succeeds.  In particular, no
totality, progress, completeness, scheduling-order, or complexity theorem is
proved here.
-/

namespace SequentialFigure7

open SequentialSchedulerBridge

/-- Canonical public tags for the implemented Figure-7 dispatcher.

`unifyPayload` is the sole unification tag.  `unifyEmpty?` and `unifyOne?` are
intentionally omitted because their successful witnesses already embed into
the arbitrary-payload implementation. -/
inductive Figure7RuleKind where
  | concl
  | nop
  | new
  | wait
  | forward
  | unifyPayload
  deriving Repr, DecidableEq

/-- Observable output of one successful canonical dispatcher call. -/
structure Figure7DispatchResult where
  kind : Figure7RuleKind
  after : ReservationState
  deriving Repr, DecidableEq

/-- Unprioritized proof-relevant union of all canonical successful local
Figure-7 steps.

This type is useful for invariant transport.  It does not by itself say that
the deterministic dispatcher selected the constructor; that stronger fact is
recorded by `DispatchStep`. -/
inductive Figure7SuccessfulStep (certificate : Certificate) :
    ReservationState → ReservationState → Type where
  | concl {before after : ReservationState} :
      ConclStep certificate before after →
      Figure7SuccessfulStep certificate before after
  | nop {before after : ReservationState} :
      NopStep certificate before after →
      Figure7SuccessfulStep certificate before after
  | new {before after : ReservationState} :
      NewStep certificate before after →
      Figure7SuccessfulStep certificate before after
  | wait {before after : ReservationState} :
      WaitStep certificate before after →
      Figure7SuccessfulStep certificate before after
  | forward {before after : ReservationState} :
      ForwardStep certificate before after →
      Figure7SuccessfulStep certificate before after
  | unifyPayload {before after : ReservationState} :
      UnifyPayloadStep certificate before after →
      Figure7SuccessfulStep certificate before after

/-- Every canonical successful-step constructor preserves the complete
occurrence-exact state-only scheduler invariant. -/
theorem Figure7SuccessfulStep.schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (step : Figure7SuccessfulStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    SchedulerInvariant certificate after := by
  cases step with
  | concl step => exact step.schedulerInvariant invariant
  | nop step => exact step.schedulerInvariant invariant
  | new step => exact step.schedulerInvariant invariant
  | wait step => exact step.schedulerInvariant invariant
  | forward step => exact step.schedulerInvariant invariant
  | unifyPayload step => exact step.schedulerInvariant invariant

/-- Run the canonical deterministic dispatcher over the implemented local
Figure-7 executors.

The precedence is fixed as `concl`, `nop`, `new`, `wait`, `forward`, then
`unifyPayload`.  Failed branches do not mutate state.  The older
`unifyEmpty?` and `unifyOne?` executors are not queried. -/
def dispatch? (certificate : Certificate) (before : ReservationState)
    (invariant : SchedulerInvariant certificate before) :
    Option Figure7DispatchResult :=
  match concl? certificate before invariant.toReservationInvariant with
  | some after => some ⟨.concl, after⟩
  | none =>
      match nop? certificate before invariant.toReservationInvariant with
      | some after => some ⟨.nop, after⟩
      | none =>
          match new? certificate before invariant.toReservationInvariant with
          | some after => some ⟨.new, after⟩
          | none =>
              match wait? certificate before invariant.toReservationInvariant with
              | some after => some ⟨.wait, after⟩
              | none =>
                  match
                      forward? certificate before
                        invariant.toReservationInvariant with
                  | some after => some ⟨.forward, after⟩
                  | none =>
                      match
                          unifyPayload? certificate before
                            invariant.toReservationInvariant with
                      | some after => some ⟨.unifyPayload, after⟩
                      | none => none

/-- Exact proof-relevant specification of one successful canonical dispatcher
call.

Every non-first constructor retains equations showing that all earlier
priority branches returned `none`.  Thus this is stronger than merely knowing
that one member of `Figure7SuccessfulStep` exists. -/
inductive DispatchStep (certificate : Certificate)
    (before : ReservationState)
    (invariant : SchedulerInvariant certificate before) :
    Figure7DispatchResult → Type where
  | concl {after : ReservationState}
      (concl_eq :
        concl? certificate before invariant.toReservationInvariant =
          some after) :
      DispatchStep certificate before invariant ⟨.concl, after⟩
  | nop {after : ReservationState}
      (concl_none :
        concl? certificate before invariant.toReservationInvariant = none)
      (nop_eq :
        nop? certificate before invariant.toReservationInvariant =
          some after) :
      DispatchStep certificate before invariant ⟨.nop, after⟩
  | new {after : ReservationState}
      (concl_none :
        concl? certificate before invariant.toReservationInvariant = none)
      (nop_none :
        nop? certificate before invariant.toReservationInvariant = none)
      (new_eq :
        new? certificate before invariant.toReservationInvariant =
          some after) :
      DispatchStep certificate before invariant ⟨.new, after⟩
  | wait {after : ReservationState}
      (concl_none :
        concl? certificate before invariant.toReservationInvariant = none)
      (nop_none :
        nop? certificate before invariant.toReservationInvariant = none)
      (new_none :
        new? certificate before invariant.toReservationInvariant = none)
      (wait_eq :
        wait? certificate before invariant.toReservationInvariant =
          some after) :
      DispatchStep certificate before invariant ⟨.wait, after⟩
  | forward {after : ReservationState}
      (concl_none :
        concl? certificate before invariant.toReservationInvariant = none)
      (nop_none :
        nop? certificate before invariant.toReservationInvariant = none)
      (new_none :
        new? certificate before invariant.toReservationInvariant = none)
      (wait_none :
        wait? certificate before invariant.toReservationInvariant = none)
      (forward_eq :
        forward? certificate before invariant.toReservationInvariant =
          some after) :
      DispatchStep certificate before invariant ⟨.forward, after⟩
  | unifyPayload {after : ReservationState}
      (concl_none :
        concl? certificate before invariant.toReservationInvariant = none)
      (nop_none :
        nop? certificate before invariant.toReservationInvariant = none)
      (new_none :
        new? certificate before invariant.toReservationInvariant = none)
      (wait_none :
        wait? certificate before invariant.toReservationInvariant = none)
      (forward_none :
        forward? certificate before invariant.toReservationInvariant = none)
      (unify_eq :
        unifyPayload? certificate before invariant.toReservationInvariant =
          some after) :
      DispatchStep certificate before invariant ⟨.unifyPayload, after⟩

/-- Canonical dispatcher success is equivalent to its exact priority-aware
dependent witness. -/
theorem dispatch?_some_iff
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    {result : Figure7DispatchResult} :
    dispatch? certificate before invariant = some result ↔
      Nonempty (DispatchStep certificate before invariant result) := by
  constructor
  · intro equation
    cases conclEquation :
        concl? certificate before invariant.toReservationInvariant with
    | some after =>
        have exactEquation :
            (some ⟨Figure7RuleKind.concl, after⟩ :
                Option Figure7DispatchResult) = some result := by
          simpa [dispatch?, conclEquation] using equation
        have resultEquation := Option.some.inj exactEquation
        subst result
        exact ⟨DispatchStep.concl conclEquation⟩
    | none =>
        cases nopEquation :
            nop? certificate before invariant.toReservationInvariant with
        | some after =>
            have exactEquation :
                (some ⟨Figure7RuleKind.nop, after⟩ :
                    Option Figure7DispatchResult) = some result := by
              simpa [dispatch?, conclEquation, nopEquation] using equation
            have resultEquation := Option.some.inj exactEquation
            subst result
            exact ⟨DispatchStep.nop conclEquation nopEquation⟩
        | none =>
            cases newEquation :
                new? certificate before invariant.toReservationInvariant with
            | some after =>
                have exactEquation :
                    (some ⟨Figure7RuleKind.new, after⟩ :
                        Option Figure7DispatchResult) = some result := by
                  simpa [dispatch?, conclEquation, nopEquation, newEquation]
                    using equation
                have resultEquation := Option.some.inj exactEquation
                subst result
                exact ⟨DispatchStep.new conclEquation nopEquation newEquation⟩
            | none =>
                cases waitEquation :
                    wait? certificate before
                      invariant.toReservationInvariant with
                | some after =>
                    have exactEquation :
                        (some ⟨Figure7RuleKind.wait, after⟩ :
                            Option Figure7DispatchResult) = some result := by
                      simpa [dispatch?, conclEquation, nopEquation,
                        newEquation, waitEquation] using equation
                    have resultEquation := Option.some.inj exactEquation
                    subst result
                    exact ⟨DispatchStep.wait conclEquation nopEquation
                      newEquation waitEquation⟩
                | none =>
                    cases forwardEquation :
                        forward? certificate before
                          invariant.toReservationInvariant with
                    | some after =>
                        have exactEquation :
                            (some ⟨Figure7RuleKind.forward, after⟩ :
                                Option Figure7DispatchResult) = some result := by
                          simpa [dispatch?, conclEquation, nopEquation,
                            newEquation, waitEquation, forwardEquation]
                            using equation
                        have resultEquation := Option.some.inj exactEquation
                        subst result
                        exact ⟨DispatchStep.forward conclEquation nopEquation
                          newEquation waitEquation forwardEquation⟩
                    | none =>
                        cases unifyEquation :
                            unifyPayload? certificate before
                              invariant.toReservationInvariant with
                        | some after =>
                            have exactEquation :
                                (some ⟨Figure7RuleKind.unifyPayload, after⟩ :
                                    Option Figure7DispatchResult) = some result := by
                              simpa [dispatch?, conclEquation, nopEquation,
                                newEquation, waitEquation, forwardEquation,
                                unifyEquation] using equation
                            have resultEquation := Option.some.inj exactEquation
                            subst result
                            exact ⟨DispatchStep.unifyPayload conclEquation
                              nopEquation newEquation waitEquation
                              forwardEquation unifyEquation⟩
                        | none =>
                            simp [dispatch?, conclEquation, nopEquation,
                              newEquation, waitEquation, forwardEquation,
                              unifyEquation] at equation
  · rintro ⟨step⟩
    cases step with
    | concl conclEquation =>
        simp [dispatch?, conclEquation]
    | nop conclEquation nopEquation =>
        simp [dispatch?, conclEquation, nopEquation]
    | new conclEquation nopEquation newEquation =>
        simp [dispatch?, conclEquation, nopEquation, newEquation]
    | wait conclEquation nopEquation newEquation waitEquation =>
        simp [dispatch?, conclEquation, nopEquation, newEquation,
          waitEquation]
    | forward conclEquation nopEquation newEquation waitEquation
        forwardEquation =>
        simp [dispatch?, conclEquation, nopEquation, newEquation,
          waitEquation, forwardEquation]
    | unifyPayload conclEquation nopEquation newEquation waitEquation
        forwardEquation unifyEquation =>
        simp [dispatch?, conclEquation, nopEquation, newEquation,
          waitEquation, forwardEquation, unifyEquation]

/-- Forget priority evidence from an exact dispatcher step while retaining a
typed successful local-rule witness. -/
theorem DispatchStep.toSuccessfulStep
    {certificate : Certificate} {before : ReservationState}
    {invariant : SchedulerInvariant certificate before}
    {result : Figure7DispatchResult}
    (step : DispatchStep certificate before invariant result) :
    Nonempty (Figure7SuccessfulStep certificate before result.after) := by
  cases step with
  | concl equation =>
      rcases
          (concl?_some_iff invariant.toReservationInvariant).mp equation with
        ⟨typed⟩
      exact ⟨Figure7SuccessfulStep.concl typed⟩
  | nop _ equation =>
      rcases
          (nop?_some_iff invariant.toReservationInvariant).mp equation with
        ⟨typed⟩
      exact ⟨Figure7SuccessfulStep.nop typed⟩
  | new _ _ equation =>
      rcases
          (new?_some_iff invariant.toReservationInvariant).mp equation with
        ⟨typed⟩
      exact ⟨Figure7SuccessfulStep.new typed⟩
  | wait _ _ _ equation =>
      rcases
          (wait?_some_iff invariant.toReservationInvariant).mp equation with
        ⟨typed⟩
      exact ⟨Figure7SuccessfulStep.wait typed⟩
  | forward _ _ _ _ equation =>
      rcases
          (forward?_some_iff invariant.toReservationInvariant).mp equation with
        ⟨typed⟩
      exact ⟨Figure7SuccessfulStep.forward typed⟩
  | unifyPayload _ _ _ _ _ equation =>
      rcases
          (unifyPayload?_some_iff invariant.toReservationInvariant).mp
              equation with
        ⟨typed⟩
      exact ⟨Figure7SuccessfulStep.unifyPayload typed⟩

/-- An exact priority-aware dispatcher step preserves the complete scheduler
invariant. -/
theorem DispatchStep.schedulerInvariant
    {certificate : Certificate} {before : ReservationState}
    {invariant : SchedulerInvariant certificate before}
    {result : Figure7DispatchResult}
    (step : DispatchStep certificate before invariant result) :
    SchedulerInvariant certificate result.after := by
  rcases step.toSuccessfulStep with ⟨successful⟩
  exact successful.schedulerInvariant invariant

/-- The canonical dispatcher has one exact tagged output for fixed input and
invariant evidence. -/
theorem DispatchStep.output_unique
    {certificate : Certificate} {before : ReservationState}
    {invariant : SchedulerInvariant certificate before}
    {first second : Figure7DispatchResult}
    (left : DispatchStep certificate before invariant first)
    (right : DispatchStep certificate before invariant second) :
    first = second := by
  have leftEquation : dispatch? certificate before invariant = some first :=
    (dispatch?_some_iff invariant).mpr ⟨left⟩
  have rightEquation : dispatch? certificate before invariant = some second :=
    (dispatch?_some_iff invariant).mpr ⟨right⟩
  exact Option.some.inj (leftEquation.symm.trans rightEquation)

/-- Every successful canonical dispatcher call preserves the complete current
scheduler invariant. -/
theorem dispatch?_schedulerInvariant
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    {result : Figure7DispatchResult}
    (equation : dispatch? certificate before invariant = some result) :
    SchedulerInvariant certificate result.after := by
  rcases (dispatch?_some_iff invariant).mp equation with ⟨step⟩
  exact step.schedulerInvariant

/-- Every successful executable initialization establishes the complete
scheduler invariant on a structurally valid certificate. -/
theorem initializeReservation?_schedulerInvariant
    {certificate : Certificate} {after : ReservationState} {start : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (equation : initializeReservation? certificate start = some after) :
    SchedulerInvariant certificate after := by
  rcases initializeReservation?_some_iff.mp equation with ⟨step⟩
  exact step.schedulerInvariant structural

/-- Proof-relevant certified history of exact canonical dispatcher executions.

`empty` and `init` retain the same exact starting forms as `InitNewHistory`.
Every `later` constructor stores an exact priority-aware dispatcher witness and
the full invariant used by that executable call.  Consequently this is a
proof-carrying execution trace, not an independent theorem that some rule is
enabled or that the dispatcher makes progress. -/
inductive ExecutedHistory (certificate : Certificate) :
    ReservationState → Type where
  | empty :
      ExecutedHistory certificate (ReservationState.empty certificate)
  | init {after : ReservationState} {start : Vertex} :
      InitialReservationStep certificate after start →
      ExecutedHistory certificate after
  | later {before : ReservationState} {result : Figure7DispatchResult} :
      ExecutedHistory certificate before →
      (invariant : SchedulerInvariant certificate before) →
      DispatchStep certificate before invariant result →
      ExecutedHistory certificate result.after

/-- Certified reachability generated only by exact initialization and exact
canonical dispatcher successes.  Every later edge carries the invariant
evidence required by the executable dispatcher; no applicability is implied. -/
def ReachableByImplementedDispatcher
    (certificate : Certificate) (state : ReservationState) : Prop :=
  Nonempty (ExecutedHistory certificate state)

namespace ExecutedHistory

/-- Every state in an exact canonical dispatcher history satisfies the
complete scheduler invariant when the certificate is structurally valid. -/
theorem schedulerInvariant
    {certificate : Certificate} {state : ReservationState}
    (history : ExecutedHistory certificate state)
    (structural : certificate.StructurallyWellFormed) :
    SchedulerInvariant certificate state := by
  cases history with
  | empty => exact empty_schedulerInvariant structural
  | init step => exact step.schedulerInvariant structural
  | later _ invariant step => exact step.schedulerInvariant

end ExecutedHistory

/-- The exact empty scheduler state is reachable before initialization. -/
theorem dispatcher_reachable_empty (certificate : Certificate) :
    ReachableByImplementedDispatcher certificate
      (ReservationState.empty certificate) :=
  ⟨ExecutedHistory.empty⟩

/-- Every successful executable initialization creates an exact dispatcher
history. -/
theorem dispatcher_reachable_of_initializeReservation?_eq_some
    {certificate : Certificate} {after : ReservationState} {start : Vertex}
    (equation : initializeReservation? certificate start = some after) :
    ReachableByImplementedDispatcher certificate after := by
  rcases initializeReservation?_some_iff.mp equation with ⟨step⟩
  exact ⟨ExecutedHistory.init step⟩

/-- Certified dispatcher reachability is closed under another successful
canonical dispatcher call. -/
theorem ReachableByImplementedDispatcher.dispatch
    {certificate : Certificate} {before : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate before)
    (invariant : SchedulerInvariant certificate before)
    {result : Figure7DispatchResult}
    (equation : dispatch? certificate before invariant = some result) :
    ReachableByImplementedDispatcher certificate result.after := by
  rcases reachable with ⟨history⟩
  rcases (dispatch?_some_iff invariant).mp equation with ⟨step⟩
  exact ⟨ExecutedHistory.later history invariant step⟩

/-- Every certified dispatcher-reachable state satisfies the complete scheduler
invariant under structural certificate validity. -/
theorem ReachableByImplementedDispatcher.schedulerInvariant
    {certificate : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate state)
    (structural : certificate.StructurallyWellFormed) :
    SchedulerInvariant certificate state := by
  rcases reachable with ⟨history⟩
  exact history.schedulerInvariant structural

end SequentialFigure7

end ProofNetIR
