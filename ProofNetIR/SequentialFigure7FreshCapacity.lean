import ProofNetIR.IntrinsicCanonical
import ProofNetIR.SequentialFigure7TagHistory
import ProofNetIR.SequentialFreshSourceLeftRun

namespace ProofNetIR

/-!
# Fresh terminal capacity for canonical Figure-7 histories

An exact source-left run whose input tags are the current canonical-history
tags terminates at an axiom slot not used by that history.  Combining that
fresh slot with the history's exact slot/raw-age count gives strict remaining
formula capacity.  This is a local cardinality theorem: it assumes neither
another executor success nor scheduler progress or totality.
-/

namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialUnification

/-- A duplicate-free finite list contained in an ambient list cannot be
longer than that ambient carrier. -/
private theorem distinct_indices_length_le
    {values ambient : List Nat}
    (nodup : values.Nodup)
    (subset : ∀ value ∈ values, value ∈ ambient) :
    values.length ≤ ambient.length := by
  induction values generalizing ambient with
  | nil =>
      simp
  | cons head tail induction =>
      have headMembership : head ∈ ambient :=
        subset head (by simp)
      have tailSubset :
          ∀ value ∈ tail, value ∈ ambient.erase head := by
        intro value membership
        have valueMembership : value ∈ ambient :=
          subset value (by simp [membership])
        have different : value ≠ head := by
          intro same
          subst value
          exact (List.nodup_cons.mp nodup).1 membership
        exact (List.mem_erase_of_ne different).2 valueMembership
      have tailBound :=
        induction (List.nodup_cons.mp nodup).2 tailSubset
      rw [List.length_erase_of_mem headMembership] at tailBound
      have positive : 0 < ambient.length :=
        List.length_pos_of_mem headMembership
      simp only [List.length_cons]
      omega

namespace CanonicalTagHistory

/-- A fresh exact terminal axiom leaves room for one more raw-age allocation.

The run is indexed by the current state's exact tag carrier.  Its terminal
slot cannot occur in the canonical history: a recorded slot has a touched
stored-left endpoint tagged `true`, while the same exact axiom would make that
endpoint either the run's reached occurrence or partner, both tagged `false`
on input.  Adding this fresh valid slot to the history's duplicate-free slot
list and using its exact length/`nextAge` equation yields the strict bound. -/
theorem fresh_terminal_capacity
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed)
    {runState : UnificationState}
    {fuel : Nat} {start reached partner : Vertex}
    {trace : List Vertex} {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate runState fuel state.tags start
      trace reached partner linkIndex) :
    state.stack.nextAge < certificate.formulas.size := by
  have reachedFresh : state.tags[reached]? = some false :=
    run.traceFresh (List.mem_of_getLast? run.traceLast)
  have partnerFresh : state.tags[partner]? = some false :=
    run.partnerFresh
  have freshIndex : linkIndex ∉ tagHistory.linkIndices := by
    intro membership
    rcases tagHistory.mem_linkIndices_witness membership with
      ⟨oldLeft, oldRight, oldExactLink, oldTouched⟩
    have oldTagged : state.tags[oldLeft]? = some true :=
      tagHistory.tagged_iff_touched.2 oldTouched
    rcases run.exactAxiom with exactLink | exactLink
    · have sameAxiom :
          Link.axiom oldLeft oldRight =
            Link.axiom reached partner :=
        Option.some.inj (oldExactLink.symm.trans exactLink)
      have sameLeft : oldLeft = reached := by
        injection sameAxiom
      subst oldLeft
      rw [oldTagged] at reachedFresh
      contradiction
    · have sameAxiom :
          Link.axiom oldLeft oldRight =
            Link.axiom partner reached :=
        Option.some.inj (oldExactLink.symm.trans exactLink)
      have sameLeft : oldLeft = partner := by
        injection sameAxiom
      subst oldLeft
      rw [oldTagged] at partnerFresh
      contradiction
  have submittedNodup :
      (linkIndex :: tagHistory.linkIndices).Nodup :=
    List.nodup_cons.mpr ⟨freshIndex, tagHistory.linkIndices_nodup⟩
  have submittedInBounds :
      ∀ index ∈ linkIndex :: tagHistory.linkIndices,
        index ∈ List.range certificate.links.length := by
    intro index membership
    simp only [List.mem_cons] at membership
    rcases membership with rfl | oldMembership
    · rcases run.exactAxiom with exactLink | exactLink
      · exact List.mem_range.mpr
          (List.getElem?_eq_some_iff.mp exactLink).choose
      · exact List.mem_range.mpr
          (List.getElem?_eq_some_iff.mp exactLink).choose
    · rcases tagHistory.mem_linkIndices_witness oldMembership with
        ⟨left, right, exactLink, _touched⟩
      exact List.mem_range.mpr
        (List.getElem?_eq_some_iff.mp exactLink).choose
  have submittedBound :
      (linkIndex :: tagHistory.linkIndices).length ≤
        certificate.links.length := by
    simpa using
      distinct_indices_length_le submittedNodup submittedInBounds
  have nextAgeSucc :
      Nat.succ state.stack.nextAge ≤ certificate.links.length := by
    rw [List.length_cons, tagHistory.linkIndices_length_eq_nextAge]
      at submittedBound
    simpa [Nat.succ_eq_add_one, Nat.add_comm] using submittedBound
  have nextAgeLtLinks :
      state.stack.nextAge < certificate.links.length :=
    Nat.lt_of_succ_le nextAgeSucc
  exact Nat.lt_of_lt_of_le nextAgeLtLinks
    structural.links_length_le_formulas_size

end CanonicalTagHistory

end SequentialFigure7

end ProofNetIR
