import ProofNetIR.SequentialFigure7Dispatcher

namespace ProofNetIR

/-!
# Canonical dispatcher tag and reservation history

The canonical dispatcher already records every successful branch and the
complete scheduler invariant used by that call.  Its `new` constructor stores
only the executable equation, however, whereas the older `InitNewHistory`
retains the exact `NEXTAXIOM` result.  This module attaches the smallest extra
proof-relevant evidence needed to recover that search event without changing
the dispatcher or treating an arbitrary invariant-satisfying state as
reachable.

The resulting history proves exact true-tag provenance, monotone tag growth,
pairwise separation of newly touched vertices from all earlier touches, and
global non-reuse of submitted axiom-link positions.  Stable dispatcher rules
record no search event and preserve the tag carrier exactly.  Nothing here
asserts that a rule is enabled, that a future call succeeds, or that the
dispatcher is total.
-/

namespace SequentialFigure7

open SequentialSchedulerBridge

namespace ConclStep

/-- A successful conclusion step preserves the tag carrier exactly. -/
theorem output_tags_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : ConclStep certificate before after) :
    after.tags = before.tags := by
  rw [step.output_eq]
  rfl

end ConclStep

namespace NopStep

/-- A successful par no-op preserves the tag carrier exactly. -/
theorem output_tags_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after) :
    after.tags = before.tags := by
  rw [step.output_eq]
  rfl

end NopStep

namespace WaitStep

/-- A successful waiting enqueue preserves the tag carrier exactly. -/
theorem output_tags_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after) :
    after.tags = before.tags := by
  rcases step.destination.exact with
    ⟨_payload, _initialized, _updated, _marks, _nextAge, _sigma, _ready,
      _core, tags⟩
  exact tags

end WaitStep

namespace ForwardStep

/-- A successful forward step preserves the tag carrier exactly. -/
theorem output_tags_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) :
    after.tags = before.tags := by
  simpa using
    congrArg (fun state : ReservationState ↦ state.tags) step.output_eq

end ForwardStep

namespace UnifyPayloadStep

/-- A successful arbitrary-payload unification preserves the tag carrier
exactly. -/
theorem output_tags_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    after.tags = before.tags := by
  simpa using
    congrArg (fun state : ReservationState ↦ state.tags) step.output_eq

end UnifyPayloadStep

/-- Branch-aligned proof evidence for the tag effect of one exact dispatcher
result.

The result tag indexes the constructor, so a stable dispatcher branch cannot
be paired with an unrelated `new` search witness. -/
inductive DispatchTagEvidence (certificate : Certificate)
    (before : ReservationState) : Figure7DispatchResult → Type where
  | concl {after : ReservationState} :
      ConclStep certificate before after →
      DispatchTagEvidence certificate before ⟨.concl, after⟩
  | nop {after : ReservationState} :
      NopStep certificate before after →
      DispatchTagEvidence certificate before ⟨.nop, after⟩
  | new {after : ReservationState} :
      NewStep certificate before after →
      DispatchTagEvidence certificate before ⟨.new, after⟩
  | wait {after : ReservationState} :
      WaitStep certificate before after →
      DispatchTagEvidence certificate before ⟨.wait, after⟩
  | forward {after : ReservationState} :
      ForwardStep certificate before after →
      DispatchTagEvidence certificate before ⟨.forward, after⟩
  | unifyPayload {after : ReservationState} :
      UnifyPayloadStep certificate before after →
      DispatchTagEvidence certificate before ⟨.unifyPayload, after⟩

namespace DispatchStep

/-- Every exact dispatcher step admits branch-aligned tag evidence.  This is
an extraction from a successful equation, not a future-success theorem. -/
theorem tagEvidence
    {certificate : Certificate} {before : ReservationState}
    {invariant : SchedulerInvariant certificate before}
    {result : Figure7DispatchResult}
    (step : DispatchStep certificate before invariant result) :
    Nonempty (DispatchTagEvidence certificate before result) := by
  cases step with
  | concl equation =>
      rcases
          (concl?_some_iff invariant.toReservationInvariant).mp equation with
        ⟨typed⟩
      exact ⟨DispatchTagEvidence.concl typed⟩
  | nop _ equation =>
      rcases
          (nop?_some_iff invariant.toReservationInvariant).mp equation with
        ⟨typed⟩
      exact ⟨DispatchTagEvidence.nop typed⟩
  | new _ _ equation =>
      rcases
          (new?_some_iff invariant.toReservationInvariant).mp equation with
        ⟨typed⟩
      exact ⟨DispatchTagEvidence.new typed⟩
  | wait _ _ _ equation =>
      rcases
          (wait?_some_iff invariant.toReservationInvariant).mp equation with
        ⟨typed⟩
      exact ⟨DispatchTagEvidence.wait typed⟩
  | forward _ _ _ _ equation =>
      rcases
          (forward?_some_iff invariant.toReservationInvariant).mp equation with
        ⟨typed⟩
      exact ⟨DispatchTagEvidence.forward typed⟩
  | unifyPayload _ _ _ _ _ equation =>
      rcases
          (unifyPayload?_some_iff invariant.toReservationInvariant).mp
              equation with
        ⟨typed⟩
      exact ⟨DispatchTagEvidence.unifyPayload typed⟩

end DispatchStep

namespace DispatchTagEvidence

/-- Vertices touched by the one possible `NEXTAXIOM` event in a dispatcher
step.  The five stable branches touch no search tag. -/
def Touched
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult} :
    DispatchTagEvidence certificate before result → Vertex → Prop
  | .concl _ => fun _ ↦ False
  | .nop _ => fun _ ↦ False
  | .new step => step.search.Touched
  | .wait _ => fun _ ↦ False
  | .forward _ => fun _ ↦ False
  | .unifyPayload _ => fun _ ↦ False

/-- Submitted axiom-link positions reserved by one dispatcher step. -/
def linkIndices
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult} :
    DispatchTagEvidence certificate before result → List Nat
  | .new step => [step.search.linkIndex]
  | _ => []

/-- Exact tag effect of every successful dispatcher branch. -/
theorem tagged_iff_input_or_touched
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result)
    {vertex : Vertex} :
    result.after.tags[vertex]? = some true ↔
      before.tags[vertex]? = some true ∨ evidence.Touched vertex := by
  cases evidence with
  | concl step => simp [Touched, step.output_tags_eq]
  | nop step => simp [Touched, step.output_tags_eq]
  | new step =>
      rw [step.output_tags_eq,
        SequentialUnification.nextAxiom?_tagged_iff_input_or_touched
          step.search_eq]
      rfl
  | wait step => simp [Touched, step.output_tags_eq]
  | forward step => simp [Touched, step.output_tags_eq]
  | unifyPayload step => simp [Touched, step.output_tags_eq]

/-- Every dispatcher step pointwise extends its input tag carrier. -/
theorem tagsExtend
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result) :
    TagsExtend before.tags result.after.tags := by
  intro vertex inputTrue
  exact evidence.tagged_iff_input_or_touched.2 (Or.inl inputTrue)

/-- Every vertex attributed to the current search was false on input. -/
theorem touched_input_false
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result)
    {vertex : Vertex} (touched : evidence.Touched vertex) :
    before.tags[vertex]? = some false := by
  cases evidence with
  | concl _ => exact False.elim touched
  | nop _ => exact False.elim touched
  | new step =>
      exact
        (SequentialUnification.nextAxiomWithFuel?_touched_tagged
          step.search_eq touched).1
  | wait _ => exact False.elim touched
  | forward _ => exact False.elim touched
  | unifyPayload _ => exact False.elim touched

/-- Membership in one dispatch event's reservation list carries the exact
submitted axiom and a touched endpoint. -/
theorem mem_linkIndices_witness
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result)
    {index : Nat} (membership : index ∈ evidence.linkIndices) :
    ∃ left right,
      certificate.links[index]? = some (.axiom left right) ∧
        evidence.Touched left := by
  cases evidence with
  | concl _ => simp [linkIndices] at membership
  | nop _ => simp [linkIndices] at membership
  | new step =>
      simp [linkIndices] at membership
      subst index
      exact ⟨step.search.left, step.search.right,
        step.search.exactLink, by
          simp [Touched, SequentialUnification.NextAxiomResult.Touched]⟩
  | wait _ => simp [linkIndices] at membership
  | forward _ => simp [linkIndices] at membership
  | unifyPayload _ => simp [linkIndices] at membership

/-- One dispatcher event never records a duplicate reservation slot. -/
theorem linkIndices_nodup
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result) :
    evidence.linkIndices.Nodup := by
  cases evidence <;> simp [linkIndices]

/-- Every non-`new` dispatcher branch preserves the complete tag array, not
only the pointwise truth implication exposed by `TagsExtend`. -/
theorem output_tags_eq_of_kind_ne_new
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result)
    (notNew : result.kind ≠ .new) :
    result.after.tags = before.tags := by
  cases evidence with
  | concl step => exact step.output_tags_eq
  | nop step => exact step.output_tags_eq
  | new _ => exact False.elim (notNew rfl)
  | wait step => exact step.output_tags_eq
  | forward step => exact step.output_tags_eq
  | unifyPayload step => exact step.output_tags_eq

/-- A dispatcher event tagged `new` has a genuinely fresh touched vertex and
records exactly one submitted axiom-link position. -/
theorem new_growth_and_singleton_link
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result)
    (isNew : result.kind = .new) :
    ∃ vertex linkIndex,
      evidence.Touched vertex ∧
        before.tags[vertex]? = some false ∧
        result.after.tags[vertex]? = some true ∧
        evidence.linkIndices = [linkIndex] := by
  cases evidence with
  | concl _ => contradiction
  | nop _ => contradiction
  | new step =>
      let vertex := step.search.left
      have touched :
          (DispatchTagEvidence.new step).Touched vertex := by
        simp [Touched, vertex,
          SequentialUnification.NextAxiomResult.Touched]
      exact ⟨vertex, step.search.linkIndex, touched,
        (DispatchTagEvidence.new step).touched_input_false touched,
        (DispatchTagEvidence.new step).tagged_iff_input_or_touched.2
          (Or.inr touched), rfl⟩
  | wait _ => contradiction
  | forward _ => contradiction
  | unifyPayload _ => contradiction

end DispatchTagEvidence

/-- The minimal proof-carrying tag augmentation of one exact canonical
dispatcher history.

This type is indexed by the already-recorded `ExecutedHistory`; it neither
widens reachability nor assumes that another dispatcher call will succeed. -/
inductive CanonicalTagHistory (certificate : Certificate) :
    {state : ReservationState} → ExecutedHistory certificate state → Type where
  | empty :
      CanonicalTagHistory certificate (ExecutedHistory.empty)
  | init {after : ReservationState} {start : Vertex}
      (step : InitialReservationStep certificate after start) :
      CanonicalTagHistory certificate (ExecutedHistory.init step)
  | later {before : ReservationState} {result : Figure7DispatchResult}
      {history : ExecutedHistory certificate before}
      {invariant : SchedulerInvariant certificate before}
      {dispatch : DispatchStep certificate before invariant result} :
      CanonicalTagHistory certificate history →
      DispatchTagEvidence certificate before result →
      CanonicalTagHistory certificate
        (ExecutedHistory.later history invariant dispatch)

namespace ExecutedHistory

/-- Every exact dispatcher history admits its minimal branch-aligned tag
augmentation. -/
theorem hasCanonicalTagHistory
    {certificate : Certificate} {state : ReservationState}
    (history : ExecutedHistory certificate state) :
    Nonempty (CanonicalTagHistory certificate history) := by
  induction history with
  | empty => exact ⟨CanonicalTagHistory.empty⟩
  | init step => exact ⟨CanonicalTagHistory.init step⟩
  | later history invariant dispatch induction =>
      rcases induction with ⟨tagHistory⟩
      rcases dispatch.tagEvidence with ⟨evidence⟩
      exact ⟨CanonicalTagHistory.later tagHistory evidence⟩

end ExecutedHistory

/-- Every state already certified reachable by the canonical dispatcher has
an exact execution history together with its canonical tag augmentation. -/
theorem ReachableByImplementedDispatcher.hasCanonicalTagHistory
    {certificate : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate state) :
    ∃ history : ExecutedHistory certificate state,
      Nonempty (CanonicalTagHistory certificate history) := by
  rcases reachable with ⟨history⟩
  exact ⟨history, history.hasCanonicalTagHistory⟩

namespace CanonicalTagHistory

/-- Vertices touched by initialization or any later canonical `new` search. -/
def Touched
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state} :
    CanonicalTagHistory certificate history → Vertex → Prop
  | .empty => fun _ ↦ False
  | .init step => step.result.Touched
  | .later prior evidence =>
      fun vertex ↦ prior.Touched vertex ∨ evidence.Touched vertex

/-- Submitted axiom-link positions, newest dispatcher event first. -/
def linkIndices
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state} :
    CanonicalTagHistory certificate history → List Nat
  | .empty => []
  | .init step => [step.result.linkIndex]
  | .later prior evidence => evidence.linkIndices ++ prior.linkIndices

/-- Exact global provenance: a current true tag exists exactly when an
initialization or canonical `new` search touched that vertex. -/
theorem tagged_iff_touched
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {vertex : Vertex} :
    state.tags[vertex]? = some true ↔ tagHistory.Touched vertex := by
  induction tagHistory with
  | empty =>
      simpa [Touched, InitNewHistory.Touched] using
        (InitNewHistory.tagged_iff_touched
          (InitNewHistory.empty :
            InitNewHistory certificate (ReservationState.empty certificate))
          (vertex := vertex))
  | init step =>
      simpa [Touched, InitNewHistory.Touched] using
        (InitNewHistory.tagged_iff_touched (InitNewHistory.init step)
          (vertex := vertex))
  | later prior evidence induction =>
      rw [evidence.tagged_iff_input_or_touched, induction]
      rfl

/-- The touched predicate is independent of which exact execution-history
witness reaches the same concrete state. -/
theorem touched_history_independent
    {certificate : Certificate} {state : ReservationState}
    {firstHistory secondHistory : ExecutedHistory certificate state}
    (first : CanonicalTagHistory certificate firstHistory)
    (second : CanonicalTagHistory certificate secondHistory)
    {vertex : Vertex} :
    first.Touched vertex ↔ second.Touched vertex := by
  rw [← first.tagged_iff_touched, ← second.tagged_iff_touched]

/-- A true tag in a canonically recorded state always has an exact recorded
initialization or `new` touch. -/
theorem true_tag_has_touch
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {vertex : Vertex}
    (tagged : state.tags[vertex]? = some true) :
    tagHistory.Touched vertex :=
  tagHistory.tagged_iff_touched.mp tagged

/-- Every previously touched vertex remains tagged after one more canonical
dispatcher step. -/
theorem touched_persists_next
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result)
    {vertex : Vertex} (oldTouched : tagHistory.Touched vertex) :
    result.after.tags[vertex]? = some true := by
  exact evidence.tagsExtend (tagHistory.tagged_iff_touched.2 oldTouched)

/-- A new dispatch event cannot touch a vertex touched anywhere earlier in
the same exact history. -/
theorem touched_disjoint_next
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result)
    {vertex : Vertex}
    (oldTouched : tagHistory.Touched vertex)
    (newTouched : evidence.Touched vertex) : False := by
  have oldTrue : before.tags[vertex]? = some true :=
    tagHistory.tagged_iff_touched.2 oldTouched
  have newFalse : before.tags[vertex]? = some false :=
    evidence.touched_input_false newTouched
  rw [oldTrue] at newFalse
  contradiction

/-- Membership in the global submitted-slot list carries an exact axiom
lookup and an endpoint touched by that history. -/
theorem mem_linkIndices_witness
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {index : Nat} (membership : index ∈ tagHistory.linkIndices) :
    ∃ left right,
      certificate.links[index]? = some (.axiom left right) ∧
        tagHistory.Touched left := by
  induction tagHistory with
  | empty => simp [linkIndices] at membership
  | init step =>
      simp [linkIndices] at membership
      subst index
      exact ⟨step.result.left, step.result.right,
        step.result.exactLink, by
          simp [Touched, SequentialUnification.NextAxiomResult.Touched]⟩
  | later prior evidence induction =>
      simp only [linkIndices, List.mem_append] at membership
      rcases membership with current | old
      · rcases evidence.mem_linkIndices_witness current with
          ⟨left, right, exactLink, touched⟩
        exact ⟨left, right, exactLink, Or.inr touched⟩
      · rcases induction old with ⟨left, right, exactLink, touched⟩
        exact ⟨left, right, exactLink, Or.inl touched⟩

/-- No submitted axiom-link position occurs twice in a canonical dispatcher
history.  Equal-valued links in distinct submitted positions remain distinct. -/
theorem linkIndices_nodup
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history) :
    tagHistory.linkIndices.Nodup := by
  induction tagHistory with
  | empty => simp [linkIndices]
  | init step => simp [linkIndices]
  | later prior evidence induction =>
      rw [linkIndices, List.nodup_append]
      refine ⟨evidence.linkIndices_nodup, induction, ?_⟩
      intro currentIndex currentMembership oldIndex oldMembership sameIndex
      rcases evidence.mem_linkIndices_witness currentMembership with
        ⟨currentLeft, currentRight, currentLink, currentTouched⟩
      rcases prior.mem_linkIndices_witness oldMembership with
        ⟨oldLeft, oldRight, oldLink, oldTouched⟩
      subst oldIndex
      have sameAxiom :
          Link.axiom currentLeft currentRight =
            Link.axiom oldLeft oldRight := by
        exact Option.some.inj (currentLink.symm.trans oldLink)
      have sameLeft : currentLeft = oldLeft := by
        injection sameAxiom
      subst oldLeft
      exact prior.touched_disjoint_next evidence oldTouched currentTouched

end CanonicalTagHistory

end SequentialFigure7

end ProofNetIR
