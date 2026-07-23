import ProofNetIR.StructuralComposition

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

/-- Every successfully constructed occurrence-aware fragment satisfies the
full structural certificate contract: local typing, unique production,
single-parent ownership, and a duplicate-free in-bounds boundary. -/
theorem build?_structurallyWellFormed
    {tree : CutFreeDerivation} {fragment : NetFragment}
    (equation : tree.build? = some fragment) :
    fragment.toCertificate.StructurallyWellFormed := by
  induction tree generalizing fragment with
  | «axiom» name positive =>
      simp [build?] at equation
      subst fragment
      cases positive <;>
        simp [NetFragment.toCertificate, Certificate.StructurallyWellFormed,
          Certificate.LinkWellFormed, Certificate.NodeWellFormed,
          Certificate.formula?, Certificate.axiomCount,
          Certificate.producerCount, Certificate.parentUseCount,
          Link.containsAxiomEndpoint, Link.produces,
          Link.usesAsPremise, Link.premises]
      all_goals
        constructor
        · decide
        · intro vertex inBounds
          have vertexCases : vertex = 0 ∨ vertex = 1 := by omega
          rcases vertexCases with rfl | rfl <;> simp [Formula.dual]
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
                      have leftMembership :
                          leftSelected ∈ leftFragment.entries :=
                        (pick?_perm leftPick).mem_iff.mpr (by simp)
                      have rightMembership :
                          rightSelected ∈ rightFragment.entries :=
                        (pick?_perm rightPick).mem_iff.mpr (by simp)
                      have leftLookup :=
                        (build?_formulaConsistent leftEquation)
                          leftSelected leftMembership
                      have rightLookup :=
                        (build?_formulaConsistent rightEquation)
                          rightSelected rightMembership
                      have leftBoundaryPermutation :
                          leftFragment.toCertificate.conclusions.Perm
                            (leftSelected.2 :: leftRemaining.map Prod.snd) := by
                        change leftFragment.roots.Perm
                          (leftSelected.2 :: leftRemaining.map Prod.snd)
                        rw [← leftFragment.entries_map_snd
                          (build?_balanced leftEquation)]
                        simpa using (pick?_perm leftPick).map Prod.snd
                      have rightBoundaryPermutation :
                          rightFragment.toCertificate.conclusions.Perm
                            (rightSelected.2 :: rightRemaining.map Prod.snd) := by
                        change rightFragment.roots.Perm
                          (rightSelected.2 :: rightRemaining.map Prod.snd)
                        rw [← rightFragment.entries_map_snd
                          (build?_balanced rightEquation)]
                        simpa using (pick?_perm rightPick).map Prod.snd
                      have composed :=
                        (leftIH leftEquation).appendTensorOccurrence
                          (rightIH rightEquation) leftSelected.1 rightSelected.1
                          leftLookup rightLookup
                          (leftRemaining.map Prod.snd)
                          (rightRemaining.map Prod.snd)
                          leftBoundaryPermutation rightBoundaryPermutation
                      simpa [NetFragment.toCertificate, NetFragment.ofEntries,
                        Certificate.appendTensorOccurrence, shiftEntry,
                        List.map_append, Function.comp_def, Nat.add_comm]
                        using composed
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
                  have afterMembership : rightSelected ∈ afterLeft :=
                    (pick?_perm rightPick).mem_iff.mpr (by simp)
                  have leftMembership :
                      leftSelected ∈ premiseFragment.entries :=
                    (pick?_perm leftPick).mem_iff.mpr (by simp)
                  have rightMembership :
                      rightSelected ∈ premiseFragment.entries :=
                    (pick?_perm leftPick).mem_iff.mpr (by
                      simp [afterMembership])
                  have premiseConsistent :=
                    build?_formulaConsistent premiseEquation
                  have leftLookup :=
                    premiseConsistent leftSelected leftMembership
                  have rightLookup :=
                    premiseConsistent rightSelected rightMembership
                  have entryPermutation :
                      premiseFragment.entries.Perm
                        (leftSelected :: rightSelected :: remaining) :=
                    (pick?_perm leftPick).trans
                      ((pick?_perm rightPick).cons leftSelected)
                  have boundaryPermutation :
                      premiseFragment.toCertificate.conclusions.Perm
                        (leftSelected.2 :: rightSelected.2 ::
                          remaining.map Prod.snd) := by
                    change premiseFragment.roots.Perm
                      (leftSelected.2 :: rightSelected.2 ::
                        remaining.map Prod.snd)
                    rw [← premiseFragment.entries_map_snd
                      (build?_balanced premiseEquation)]
                    simpa using entryPermutation.map Prod.snd
                  have composed :=
                    (ih premiseEquation).appendParOccurrence
                      leftSelected.1 rightSelected.1 leftLookup rightLookup
                      (remaining.map Prod.snd) boundaryPermutation
                  simpa [NetFragment.toCertificate, NetFragment.ofEntries,
                    Certificate.appendParOccurrence, List.map_append]
                    using composed
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
              have boundaryPermutation :
                  premiseFragment.toCertificate.conclusions.Perm
                    (reordered.map Prod.snd) := by
                change premiseFragment.roots.Perm (reordered.map Prod.snd)
                rw [← premiseFragment.entries_map_snd
                  (build?_balanced premiseEquation)]
                exact (reorder?_perm reorderedEquation).map Prod.snd
              have composed :=
                (ih premiseEquation).withConclusions
                  (reordered.map Prod.snd) boundaryPermutation
              simpa [NetFragment.toCertificate, NetFragment.ofEntries]
                using composed

/-- Every switching of every successfully constructed fragment is a tree.
This theorem is independent of the certificate ownership/typing proof needed
for full structural well-formedness. -/
theorem build?_switchingCorrect
    {tree : CutFreeDerivation} {fragment : NetFragment}
    (equation : tree.build? = some fragment) :
    fragment.toCertificate.SwitchingCorrect := by
  induction tree generalizing fragment with
  | «axiom» name positive =>
      simp [build?] at equation
      subst fragment
      intro graph switching
      rcases switching with ⟨selected, selection, rfl⟩
      cases selection
      change (Graph.mk 2 [Edge.mk 0 1]).IsTree
      refine ⟨?_, ?_, rfl⟩
      · intro edge membership
        simp only [List.mem_singleton] at membership
        subst edge
        change 0 < 2 ∧ 1 < 2 ∧ 0 ≠ 1
        exact ⟨by decide, by decide, by decide⟩
      · refine ⟨by decide, ?_⟩
        intro vertex inBounds
        change vertex < 2 at inBounds
        have cases : vertex = 0 ∨ vertex = 1 := by omega
        rcases cases with rfl | rfl
        · exact .refl 0
        · exact .step (.refl 0)
            ⟨Edge.mk 0 1, by simp, Or.inl ⟨rfl, rfl⟩⟩
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
                      have leftMembership :
                          leftSelected ∈ leftFragment.entries :=
                        (pick?_perm leftPick).mem_iff.mpr (by simp)
                      have rightMembership :
                          rightSelected ∈ rightFragment.entries :=
                        (pick?_perm rightPick).mem_iff.mpr (by simp)
                      have leftLookup :=
                        (build?_formulaConsistent leftEquation)
                          leftSelected leftMembership
                      have rightLookup :=
                        (build?_formulaConsistent rightEquation)
                          rightSelected rightMembership
                      have leftRootInBounds : leftSelected.2 <
                          leftFragment.formulas.size :=
                        (Array.getElem?_eq_some_iff.mp leftLookup).1
                      have rightRootInBounds : rightSelected.2 <
                          rightFragment.formulas.size :=
                        (Array.getElem?_eq_some_iff.mp rightLookup).1
                      let boundary :=
                        (((.tensor leftSelected.1 rightSelected.1,
                            (leftFragment.formulas ++
                              rightFragment.formulas).size) ::
                          (leftRemaining ++ rightRemaining.map
                            (shiftEntry leftFragment.formulas.size)))).map
                              Prod.snd
                      have composed :=
                        (leftIH leftEquation).appendTensorOccurrence
                          (rightIH rightEquation) leftSelected.1 rightSelected.1
                          leftRootInBounds rightRootInBounds boundary
                      simpa [NetFragment.toCertificate, NetFragment.ofEntries,
                        Certificate.appendTensorOccurrence, boundary,
                        shiftEntry, List.map_append, Function.comp_def,
                        Nat.add_comm] using composed
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
                  have afterMembership : rightSelected ∈ afterLeft :=
                    (pick?_perm rightPick).mem_iff.mpr (by simp)
                  have leftMembership :
                      leftSelected ∈ premiseFragment.entries :=
                    (pick?_perm leftPick).mem_iff.mpr (by simp)
                  have rightMembership :
                      rightSelected ∈ premiseFragment.entries :=
                    (pick?_perm leftPick).mem_iff.mpr (by
                      simp [afterMembership])
                  have premiseConsistent :=
                    build?_formulaConsistent premiseEquation
                  have leftLookup :=
                    premiseConsistent leftSelected leftMembership
                  have rightLookup :=
                    premiseConsistent rightSelected rightMembership
                  have leftRootInBounds : leftSelected.2 <
                      premiseFragment.formulas.size :=
                    (Array.getElem?_eq_some_iff.mp leftLookup).1
                  have rightRootInBounds : rightSelected.2 <
                      premiseFragment.formulas.size :=
                    (Array.getElem?_eq_some_iff.mp rightLookup).1
                  let boundary :=
                    (remaining ++ [(Formula.par leftSelected.1 rightSelected.1,
                      premiseFragment.formulas.size)]).map Prod.snd
                  have composed :=
                    (ih premiseEquation).appendParOccurrence
                      leftSelected.1 rightSelected.1 leftRootInBounds
                      rightRootInBounds boundary
                  simpa [NetFragment.toCertificate, NetFragment.ofEntries,
                    Certificate.appendParOccurrence, boundary] using composed
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
              simpa [Certificate.SwitchingCorrect, NetFragment.toCertificate,
                NetFragment.ofEntries, Certificate.SwitchingGraph,
                Certificate.parChoices, Certificate.fixedEdges,
                Certificate.graphForSelection] using ih premiseEquation

/-- A successfully built derivation fragment satisfies both independent
halves of the public proof-net semantics. -/
theorem build?_declarativelyCorrect
    {tree : CutFreeDerivation} {fragment : NetFragment}
    (equation : tree.build? = some fragment) :
    fragment.toCertificate.DeclarativelyCorrect :=
  ⟨build?_structurallyWellFormed equation,
    build?_switchingCorrect equation⟩

/-- The executable checker accepts every certificate produced by a successful
derivation build. This is the end-to-end desequentialization soundness theorem
for the checker, not merely formula-boundary consistency. -/
theorem build?_check
    {tree : CutFreeDerivation} {fragment : NetFragment}
    (equation : tree.build? = some fragment) :
    fragment.toCertificate.check = true :=
  fragment.toCertificate.check_iff_declarativelyCorrect.mpr
    (build?_declarativelyCorrect equation)

/-- Every successful public desequentialization result satisfies the
independent declarative proof-net contract. -/
theorem desequentialize?_declarativelyCorrect
    {tree : CutFreeDerivation} {certificate : Certificate}
    (equation : tree.desequentialize? = some certificate) :
    certificate.DeclarativelyCorrect := by
  rcases build?_exists_of_desequentialize? equation with
    ⟨fragment, buildEquation, rfl⟩
  exact build?_declarativelyCorrect buildEquation

/-- Every successful public desequentialization result is checker-accepted. -/
theorem desequentialize?_check
    {tree : CutFreeDerivation} {certificate : Certificate}
    (equation : tree.desequentialize? = some certificate) :
    certificate.check = true :=
  certificate.check_iff_declarativelyCorrect.mpr
    (desequentialize?_declarativelyCorrect equation)

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

/-- Backward-compatible boundary-only corollary: formula-level validation is
sufficient to construct a public certificate whose lookup returns the
validated sequent. See `desequentialize?_exists_checked_of_infer?` for the
stronger checker-accepted result. -/
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

/-- Formula-level validation constructs a certificate with the requested
boundary and a kernel proof that the executable checker accepts it. -/
theorem desequentialize?_exists_checked_of_infer?
    {tree : CutFreeDerivation} {sequent : List Formula}
    (accepted : tree.infer? = some sequent) :
    ∃ certificate : Certificate,
      tree.desequentialize? = some certificate ∧
        certificate.conclusionFormulas? = some sequent ∧
        certificate.check = true := by
  rcases build?_exists_of_infer? accepted with ⟨fragment, buildEquation⟩
  have publicEquation :
      tree.desequentialize? = some fragment.toCertificate := by
    simp [desequentialize?, buildEquation]
  refine ⟨fragment.toCertificate, publicEquation, ?_,
    desequentialize?_check publicEquation⟩
  rw [desequentialize?_conclusionFormulas? publicEquation]
  exact accepted

/-- The checker-gated public desequentializer is total on formula-valid rule
trees; its returned payload retains the checker-acceptance proof. -/
theorem desequentializeChecked?_exists_of_infer?
    {tree : CutFreeDerivation} {sequent : List Formula}
    (accepted : tree.infer? = some sequent) :
    ∃ result : CheckedCertificate,
      tree.desequentializeChecked? = some result := by
  rcases desequentialize?_exists_checked_of_infer? accepted with
    ⟨certificate, publicEquation, _, checked⟩
  refine ⟨⟨certificate, checked⟩, ?_⟩
  simp [desequentializeChecked?, publicEquation, checked]

/-- The strongest public elaborator is total on derivation trees accepted by
the independent formula inference pass. -/
theorem elaborate?_exists_of_infer?
    {tree : CutFreeDerivation} {sequent : List Formula}
    (accepted : tree.infer? = some sequent) :
    ∃ result : ElaboratedCertificate, tree.elaborate? = some result := by
  rcases desequentialize?_exists_checked_of_infer? accepted with
    ⟨certificate, publicEquation, labels, checked⟩
  simp only [elaborate?]
  split <;> simp_all

end CutFreeDerivation

end ProofNetIR
