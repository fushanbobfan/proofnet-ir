import ProofNetIR.Sequentialization

namespace ProofNetIR

namespace NetFragment

/-- Every boundary occurrence is labelled by the formula stored at its root
vertex. This is the invariant needed to turn the internal occurrence boundary
into the public `conclusionFormulas?` lookup contract. -/
def FormulaConsistent (fragment : NetFragment) : Prop :=
  ∀ entry ∈ fragment.entries,
    fragment.formulas[entry.2]? = some entry.1

@[simp] theorem ofEntries_entries (formulas : Array Formula) (links : List Link)
    (entries : List (Formula × Vertex)) :
    (ofEntries formulas links entries).entries = entries := by
  simp [NetFragment.entries, NetFragment.ofEntries,
    list_zip_map_fst_snd]

theorem FormulaConsistent.formula?_of_mem
    {fragment : NetFragment} (consistent : fragment.FormulaConsistent)
    {formula : Formula} {root : Vertex}
    (membership : (formula, root) ∈ fragment.entries) :
    fragment.toCertificate.formula? root = some formula := by
  exact consistent (formula, root) membership

private theorem mapM_formula?_eq_some_map_fst
    (fragment : NetFragment) (entries : List (Formula × Vertex))
    (consistent : ∀ entry ∈ entries,
      fragment.toCertificate.formula? entry.2 = some entry.1) :
    (entries.map Prod.snd).mapM fragment.toCertificate.formula? =
      some (entries.map Prod.fst) := by
  induction entries with
  | nil => simp
  | cons head tail ih =>
      have headLookup := consistent head (by simp)
      have tailLookup : ∀ entry ∈ tail,
          fragment.toCertificate.formula? entry.2 = some entry.1 := by
        intro entry membership
        exact consistent entry (by simp [membership])
      simp [headLookup, ih tailLookup]

/-- Formula consistency plus the lockstep boundary invariant implies that the
public certificate API recovers exactly the fragment's ordered conclusion
labels. -/
theorem FormulaConsistent.conclusionFormulas?
    {fragment : NetFragment} (consistent : fragment.FormulaConsistent)
    (balanced : fragment.Balanced) :
    fragment.toCertificate.conclusionFormulas? =
      some fragment.conclusions := by
  unfold Certificate.conclusionFormulas?
  change fragment.roots.mapM fragment.toCertificate.formula? =
    some fragment.conclusions
  rw [← fragment.entries_map_snd balanced,
    ← fragment.entries_map_fst balanced]
  exact mapM_formula?_eq_some_map_fst fragment fragment.entries
    (fun entry membership => consistent entry membership)

end NetFragment

namespace CutFreeDerivation

/-- Every fragment produced by the occurrence-aware builder labels each
boundary root with exactly the formula stored in its boundary entry. -/
theorem build?_formulaConsistent
    {tree : CutFreeDerivation} {fragment : NetFragment}
    (equation : tree.build? = some fragment) :
    fragment.FormulaConsistent := by
  induction tree generalizing fragment with
  | «axiom» name positive =>
      simp [build?] at equation
      subst fragment
      intro entry membership
      simp [NetFragment.entries] at membership
      rcases membership with rfl | rfl <;> rfl
  | tensor leftFocus rightFocus leftTree rightTree leftIH rightIH =>
      simp only [build?] at equation
      cases leftEquation : leftTree.build? with
      | none => simp [leftEquation] at equation
      | some leftFragment =>
          cases rightEquation : rightTree.build? with
          | none => simp [leftEquation, rightEquation] at equation
          | some rightFragment =>
              cases leftPick : pick? leftFragment.entries leftFocus with
              | none =>
                  simp [leftEquation, rightEquation, leftPick] at equation
              | some leftPair =>
                  rcases leftPair with ⟨leftSelected, leftRemaining⟩
                  cases rightPick : pick? rightFragment.entries rightFocus with
                  | none =>
                      simp [leftEquation, rightEquation, rightPick] at equation
                  | some rightPair =>
                      rcases rightPair with
                        ⟨rightSelected, rightRemaining⟩
                      simp [leftEquation, rightEquation, leftPick, rightPick]
                        at equation
                      subst fragment
                      have leftConsistent := leftIH leftEquation
                      have rightConsistent := rightIH rightEquation
                      intro entry membership
                      simp only [NetFragment.ofEntries_entries] at membership
                      simp only [List.mem_cons, List.mem_append,
                        List.mem_map] at membership
                      rcases membership with newEntry | oldEntry
                      · subst entry
                        change (leftFragment.formulas ++
                          rightFragment.formulas.push
                            (.tensor leftSelected.1 rightSelected.1))[
                              leftFragment.formulas.size +
                                rightFragment.formulas.size]? =
                          some (.tensor leftSelected.1 rightSelected.1)
                        rw [Array.getElem?_append_right (by omega)]
                        rw [show leftFragment.formulas.size +
                            rightFragment.formulas.size -
                              leftFragment.formulas.size =
                            rightFragment.formulas.size by omega]
                        exact Array.getElem?_push_size
                      · rcases oldEntry with leftEntry | rightEntry
                        · have originalMembership :
                              entry ∈ leftFragment.entries :=
                            (pick?_perm leftPick).mem_iff.mpr (by
                              simp [leftEntry])
                          have oldLookup :=
                            leftConsistent entry originalMembership
                          have rootInBounds : entry.2 <
                              leftFragment.formulas.size :=
                            (Array.getElem?_eq_some_iff.mp oldLookup).1
                          change (leftFragment.formulas ++
                            rightFragment.formulas.push
                              (.tensor leftSelected.1 rightSelected.1))[
                                entry.2]? = some entry.1
                          rw [Array.getElem?_append_left rootInBounds]
                          exact oldLookup
                        · rcases rightEntry with
                            ⟨sourceEntry, sourceMembership, rfl⟩
                          have originalMembership :
                              sourceEntry ∈ rightFragment.entries :=
                            (pick?_perm rightPick).mem_iff.mpr (by
                              simp [sourceMembership])
                          have oldLookup :=
                            rightConsistent sourceEntry originalMembership
                          have rootInBounds : sourceEntry.2 <
                              rightFragment.formulas.size :=
                            (Array.getElem?_eq_some_iff.mp oldLookup).1
                          change (leftFragment.formulas ++
                            rightFragment.formulas.push
                              (.tensor leftSelected.1 rightSelected.1))[
                                sourceEntry.2 +
                                  leftFragment.formulas.size]? =
                            some sourceEntry.1
                          rw [Array.getElem?_append_right (by
                            omega)]
                          rw [show sourceEntry.2 +
                              leftFragment.formulas.size -
                                leftFragment.formulas.size =
                              sourceEntry.2 by simp]
                          rw [Array.getElem?_push, if_neg
                            (Nat.ne_of_lt rootInBounds)]
                          exact oldLookup
  | par leftFocus rightFocus premise ih =>
      simp only [build?] at equation
      cases premiseEquation : premise.build? with
      | none => simp [premiseEquation] at equation
      | some premiseFragment =>
          cases leftPick : pick? premiseFragment.entries leftFocus with
          | none => simp [premiseEquation, leftPick] at equation
          | some leftPair =>
              rcases leftPair with ⟨leftSelected, afterLeft⟩
              cases rightPick : pick? afterLeft rightFocus with
              | none =>
                  simp [premiseEquation, leftPick, rightPick] at equation
              | some rightPair =>
                  rcases rightPair with ⟨rightSelected, remaining⟩
                  simp [premiseEquation, leftPick, rightPick] at equation
                  subst fragment
                  have premiseConsistent := ih premiseEquation
                  intro entry membership
                  simp only [NetFragment.ofEntries_entries, List.mem_append,
                    List.mem_singleton] at membership
                  rcases membership with oldEntry | newEntry
                  · have remainingInAfter : entry ∈ afterLeft :=
                      (pick?_perm rightPick).mem_iff.mpr (by
                        simp [oldEntry])
                    have originalMembership :
                        entry ∈ premiseFragment.entries :=
                      (pick?_perm leftPick).mem_iff.mpr (by
                        simp [remainingInAfter])
                    have oldLookup :=
                      premiseConsistent entry originalMembership
                    have rootInBounds : entry.2 <
                        premiseFragment.formulas.size :=
                      (Array.getElem?_eq_some_iff.mp oldLookup).1
                    change (premiseFragment.formulas.push
                      (.par leftSelected.1 rightSelected.1))[entry.2]? =
                        some entry.1
                    rw [Array.getElem?_push, if_neg
                      (Nat.ne_of_lt rootInBounds)]
                    exact oldLookup
                  · subst entry
                    change (premiseFragment.formulas.push
                      (.par leftSelected.1 rightSelected.1))[
                        premiseFragment.formulas.size]? =
                          some (.par leftSelected.1 rightSelected.1)
                    exact Array.getElem?_push_size
  | exchange order premise ih =>
      simp only [build?] at equation
      cases premiseEquation : premise.build? with
      | none => simp [premiseEquation] at equation
      | some premiseFragment =>
          cases reorderedEquation : reorder? premiseFragment.entries order with
          | none => simp [premiseEquation, reorderedEquation] at equation
          | some reordered =>
              simp [premiseEquation, reorderedEquation] at equation
              subst fragment
              have premiseConsistent := ih premiseEquation
              intro entry membership
              simp only [NetFragment.ofEntries_entries] at membership
              exact premiseConsistent entry
                ((reorder?_perm reorderedEquation).mem_iff.mpr membership)

/-- Successful fragment construction exposes exactly its inferred boundary
through the public certificate formula lookup API. -/
theorem build?_conclusionFormulas?
    {tree : CutFreeDerivation} {fragment : NetFragment}
    (equation : tree.build? = some fragment) :
    fragment.toCertificate.conclusionFormulas? =
      some fragment.conclusions := by
  exact (build?_formulaConsistent equation).conclusionFormulas?
    (build?_balanced equation)

/-- Every successful public desequentialization result carries exactly the
formula sequent inferred by its source derivation. -/
theorem desequentialize?_conclusionFormulas?
    {tree : CutFreeDerivation} {certificate : Certificate}
    (equation : tree.desequentialize? = some certificate) :
    certificate.conclusionFormulas? = tree.infer? := by
  rcases build?_exists_of_desequentialize? equation with
    ⟨fragment, buildEquation, rfl⟩
  rw [infer?_of_build? buildEquation]
  exact build?_conclusionFormulas? buildEquation

/-- Formula-level validation is sufficient to construct a public certificate
whose boundary lookup returns the validated sequent. This theorem deliberately
does not yet claim that the switching checker accepts that certificate. -/
theorem desequentialize?_exists_with_labels_of_infer?
    {tree : CutFreeDerivation} {sequent : List Formula}
    (accepted : tree.infer? = some sequent) :
    ∃ certificate : Certificate,
      tree.desequentialize? = some certificate ∧
        certificate.conclusionFormulas? = some sequent := by
  rcases build?_exists_of_infer? accepted with ⟨fragment, buildEquation⟩
  refine ⟨fragment.toCertificate, ?_, ?_⟩
  · simp [desequentialize?, buildEquation]
  · rw [desequentialize?_conclusionFormulas?
      (tree := tree) (certificate := fragment.toCertificate)]
    · exact accepted
    · simp [desequentialize?, buildEquation]

end CutFreeDerivation

end ProofNetIR
