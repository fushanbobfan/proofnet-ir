import ProofNetIR.SwitchingComposition

namespace ProofNetIR

namespace Certificate

private theorem eraseDups_eq_self_of_nodup [BEq α] [LawfulBEq α]
    {values : List α} (nodup : values.Nodup) :
    values.eraseDups = values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      rcases List.nodup_cons.mp nodup with ⟨headFresh, tailNodup⟩
      rw [List.eraseDups_cons]
      have filtered : tail.filter (fun value => !value == head) = tail := by
        apply List.filter_eq_self.mpr
        intro value membership
        have different : value ≠ head :=
          fun same => headFresh (same ▸ membership)
        simpa using different
      rw [filtered]
      exact congrArg (List.cons head) (ih tailNodup)

private theorem formula?_appendParOccurrence_old
    (premise : Certificate) (left right : Formula)
    (leftRoot rightRoot : Vertex) (boundary : List Vertex)
    {vertex : Vertex} (inBounds : vertex < premise.formulas.size) :
    (premise.appendParOccurrence left right leftRoot rightRoot boundary).formula?
        vertex = premise.formula? vertex := by
  simp [appendParOccurrence, formula?, Array.getElem?_push,
    Nat.ne_of_lt inBounds]

private theorem LinkWellFormed.appendParOccurrence_old
    {premise : Certificate} {link : Link}
    (wellFormed : premise.LinkWellFormed link)
    (left right : Formula) (leftRoot rightRoot : Vertex)
    (boundary : List Vertex) :
    (premise.appendParOccurrence left right leftRoot rightRoot boundary).LinkWellFormed
      link := by
  cases link with
  | «axiom» first second =>
      rcases wellFormed with
        ⟨different, firstBound, secondBound, typing⟩
      simp only [LinkWellFormed]
      refine ⟨different,
        by simpa [appendParOccurrence] using Nat.lt_succ_of_lt firstBound,
        by simpa [appendParOccurrence] using Nat.lt_succ_of_lt secondBound, ?_⟩
      rw [formula?_appendParOccurrence_old premise left right leftRoot
          rightRoot boundary firstBound,
        formula?_appendParOccurrence_old premise left right leftRoot
          rightRoot boundary secondBound]
      exact typing
  | tensor first second conclusion =>
      rcases wellFormed with
        ⟨firstSecond, firstConclusion, secondConclusion,
          firstBound, secondBound, conclusionBound, typing⟩
      simp only [LinkWellFormed]
      refine ⟨firstSecond, firstConclusion, secondConclusion,
        by simpa [appendParOccurrence] using Nat.lt_succ_of_lt firstBound,
        by simpa [appendParOccurrence] using Nat.lt_succ_of_lt secondBound,
        by simpa [appendParOccurrence] using Nat.lt_succ_of_lt conclusionBound,
        ?_⟩
      rw [formula?_appendParOccurrence_old premise left right leftRoot
          rightRoot boundary firstBound,
        formula?_appendParOccurrence_old premise left right leftRoot
          rightRoot boundary secondBound,
        formula?_appendParOccurrence_old premise left right leftRoot
          rightRoot boundary conclusionBound]
      exact typing
  | par first second conclusion =>
      rcases wellFormed with
        ⟨firstSecond, firstConclusion, secondConclusion,
          firstBound, secondBound, conclusionBound, typing⟩
      simp only [LinkWellFormed]
      refine ⟨firstSecond, firstConclusion, secondConclusion,
        by simpa [appendParOccurrence] using Nat.lt_succ_of_lt firstBound,
        by simpa [appendParOccurrence] using Nat.lt_succ_of_lt secondBound,
        by simpa [appendParOccurrence] using Nat.lt_succ_of_lt conclusionBound,
        ?_⟩
      rw [formula?_appendParOccurrence_old premise left right leftRoot
          rightRoot boundary firstBound,
        formula?_appendParOccurrence_old premise left right leftRoot
          rightRoot boundary secondBound,
        formula?_appendParOccurrence_old premise left right leftRoot
          rightRoot boundary conclusionBound]
      exact typing

private theorem axiomCount_appendParOccurrence_old
    (premise : Certificate) (left right : Formula)
    (leftRoot rightRoot : Vertex) (boundary : List Vertex)
    (vertex : Vertex) :
    (premise.appendParOccurrence left right leftRoot rightRoot boundary).axiomCount
      vertex = premise.axiomCount vertex := by
  simp [axiomCount, appendParOccurrence, Link.containsAxiomEndpoint]

private theorem producerCount_appendParOccurrence_old
    (premise : Certificate) (left right : Formula)
    (leftRoot rightRoot : Vertex) (boundary : List Vertex)
    {vertex : Vertex} (inBounds : vertex < premise.formulas.size) :
    (premise.appendParOccurrence left right leftRoot rightRoot boundary).producerCount
      vertex = premise.producerCount vertex := by
  have different : premise.formulas.size ≠ vertex :=
    Nat.ne_of_gt inBounds
  simp [producerCount, appendParOccurrence, Link.produces, different]

private theorem parentUseCount_appendParOccurrence_left
    (premise : Certificate) (left right : Formula)
    {leftRoot rightRoot : Vertex} (different : leftRoot ≠ rightRoot)
    (boundary : List Vertex) :
    (premise.appendParOccurrence left right leftRoot rightRoot boundary).parentUseCount
      leftRoot = premise.parentUseCount leftRoot + 1 := by
  simp [parentUseCount, appendParOccurrence, Link.usesAsPremise,
    Link.premises, different]

private theorem parentUseCount_appendParOccurrence_right
    (premise : Certificate) (left right : Formula)
    {leftRoot rightRoot : Vertex} (different : leftRoot ≠ rightRoot)
    (boundary : List Vertex) :
    (premise.appendParOccurrence left right leftRoot rightRoot boundary).parentUseCount
      rightRoot = premise.parentUseCount rightRoot + 1 := by
  simp [parentUseCount, appendParOccurrence, Link.usesAsPremise,
    Link.premises, Ne.symm different]

private theorem parentUseCount_appendParOccurrence_other
    (premise : Certificate) (left right : Formula)
    {leftRoot rightRoot vertex : Vertex}
    (notLeft : vertex ≠ leftRoot) (notRight : vertex ≠ rightRoot)
    (boundary : List Vertex) :
    (premise.appendParOccurrence left right leftRoot rightRoot boundary).parentUseCount
      vertex = premise.parentUseCount vertex := by
  simp [parentUseCount, appendParOccurrence, Link.usesAsPremise,
    Link.premises, notLeft, notRight]

private theorem StructurallyWellFormed.producerCount_at_size
    {premise : Certificate} (structural : premise.StructurallyWellFormed) :
    premise.producerCount premise.formulas.size = 0 := by
  unfold producerCount
  have filtered : premise.links.filter
      (fun link => link.produces premise.formulas.size) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro link membership
    have linkWellFormed := structural.2.2.2.2.1 link membership
    cases link with
    | «axiom» left right => simp [Link.produces]
    | tensor left right conclusion =>
        have conclusionBound := linkWellFormed.2.2.2.2.2.1
        simp [Link.produces, Nat.ne_of_lt conclusionBound]
    | par left right conclusion =>
        have conclusionBound := linkWellFormed.2.2.2.2.2.1
        simp [Link.produces, Nat.ne_of_lt conclusionBound]
  rw [filtered]
  rfl

private theorem StructurallyWellFormed.parentUseCount_at_size
    {premise : Certificate} (structural : premise.StructurallyWellFormed) :
    premise.parentUseCount premise.formulas.size = 0 := by
  unfold parentUseCount
  have filtered : premise.links.filter
      (fun link => link.usesAsPremise premise.formulas.size) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro link membership
    have linkWellFormed := structural.2.2.2.2.1 link membership
    cases link with
    | «axiom» left right => simp [Link.usesAsPremise, Link.premises]
    | tensor left right conclusion =>
        have leftBound := linkWellFormed.2.2.2.1
        have rightBound := linkWellFormed.2.2.2.2.1
        simp [Link.usesAsPremise, Link.premises,
          Ne.symm (Nat.ne_of_lt leftBound),
          Ne.symm (Nat.ne_of_lt rightBound)]
    | par left right conclusion =>
        have leftBound := linkWellFormed.2.2.2.1
        have rightBound := linkWellFormed.2.2.2.2.1
        simp [Link.usesAsPremise, Link.premises,
          Ne.symm (Nat.ne_of_lt leftBound),
          Ne.symm (Nat.ne_of_lt rightBound)]
  rw [filtered]
  rfl

private theorem StructurallyWellFormed.axiomCount_outOfBounds
    {premise : Certificate} (structural : premise.StructurallyWellFormed)
    {vertex : Vertex} (outside : premise.formulas.size ≤ vertex) :
    premise.axiomCount vertex = 0 := by
  unfold axiomCount
  have filtered : premise.links.filter
      (fun link => link.containsAxiomEndpoint vertex) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro link membership
    have linkWellFormed := structural.2.2.2.2.1 link membership
    cases link with
    | «axiom» left right =>
        have leftBound := linkWellFormed.2.1
        have rightBound := linkWellFormed.2.2.1
        have leftDifferent : left ≠ vertex :=
          Nat.ne_of_lt (Nat.lt_of_lt_of_le leftBound outside)
        have rightDifferent : right ≠ vertex :=
          Nat.ne_of_lt (Nat.lt_of_lt_of_le rightBound outside)
        simp [Link.containsAxiomEndpoint, leftDifferent, rightDifferent]
    | tensor left right conclusion => simp [Link.containsAxiomEndpoint]
    | par left right conclusion => simp [Link.containsAxiomEndpoint]
  rw [filtered]
  rfl

private theorem StructurallyWellFormed.producerCount_outOfBounds
    {premise : Certificate} (structural : premise.StructurallyWellFormed)
    {vertex : Vertex} (outside : premise.formulas.size ≤ vertex) :
    premise.producerCount vertex = 0 := by
  unfold producerCount
  have filtered : premise.links.filter
      (fun link => link.produces vertex) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro link membership
    have linkWellFormed := structural.2.2.2.2.1 link membership
    cases link with
    | «axiom» left right => simp [Link.produces]
    | tensor left right conclusion =>
        have conclusionBound := linkWellFormed.2.2.2.2.2.1
        have different : conclusion ≠ vertex :=
          Nat.ne_of_lt (Nat.lt_of_lt_of_le conclusionBound outside)
        simp [Link.produces, different]
    | par left right conclusion =>
        have conclusionBound := linkWellFormed.2.2.2.2.2.1
        have different : conclusion ≠ vertex :=
          Nat.ne_of_lt (Nat.lt_of_lt_of_le conclusionBound outside)
        simp [Link.produces, different]
  rw [filtered]
  rfl

private theorem StructurallyWellFormed.parentUseCount_outOfBounds
    {premise : Certificate} (structural : premise.StructurallyWellFormed)
    {vertex : Vertex} (outside : premise.formulas.size ≤ vertex) :
    premise.parentUseCount vertex = 0 := by
  unfold parentUseCount
  have filtered : premise.links.filter
      (fun link => link.usesAsPremise vertex) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro link membership
    have linkWellFormed := structural.2.2.2.2.1 link membership
    cases link with
    | «axiom» left right => simp [Link.usesAsPremise, Link.premises]
    | tensor left right conclusion =>
        have leftBound := linkWellFormed.2.2.2.1
        have rightBound := linkWellFormed.2.2.2.2.1
        have leftDifferent : left ≠ vertex :=
          Nat.ne_of_lt (Nat.lt_of_lt_of_le leftBound outside)
        have rightDifferent : right ≠ vertex :=
          Nat.ne_of_lt (Nat.lt_of_lt_of_le rightBound outside)
        simp [Link.usesAsPremise, Link.premises,
          Ne.symm leftDifferent, Ne.symm rightDifferent]
    | par left right conclusion =>
        have leftBound := linkWellFormed.2.2.2.1
        have rightBound := linkWellFormed.2.2.2.2.1
        have leftDifferent : left ≠ vertex :=
          Nat.ne_of_lt (Nat.lt_of_lt_of_le leftBound outside)
        have rightDifferent : right ≠ vertex :=
          Nat.ne_of_lt (Nat.lt_of_lt_of_le rightBound outside)
        simp [Link.usesAsPremise, Link.premises,
          Ne.symm leftDifferent, Ne.symm rightDifferent]
  rw [filtered]
  rfl

private theorem containsAxiomEndpoint_shift_same (link : Link)
    (offset vertex : Nat) :
    (link.shift offset).containsAxiomEndpoint (vertex + offset) =
      link.containsAxiomEndpoint vertex := by
  cases link with
  | «axiom» left right =>
      simp only [Link.shift, Link.containsAxiomEndpoint]
      apply Bool.eq_iff_iff.mpr
      simpa only [Bool.or_eq_true, beq_iff_eq] using (show
        (left + offset = vertex + offset ∨
          right + offset = vertex + offset) ↔
        (left = vertex ∨ right = vertex) from
          or_congr Nat.add_right_cancel_iff Nat.add_right_cancel_iff)
  | tensor left right conclusion => rfl
  | par left right conclusion => rfl

private theorem produces_shift_same (link : Link) (offset vertex : Nat) :
    (link.shift offset).produces (vertex + offset) =
      link.produces vertex := by
  cases link with
  | «axiom» left right => rfl
  | tensor left right conclusion =>
      simp only [Link.shift, Link.produces]
      apply Bool.eq_iff_iff.mpr
      simpa only [beq_iff_eq] using (show
        conclusion + offset = vertex + offset ↔ conclusion = vertex from
          Nat.add_right_cancel_iff)
  | par left right conclusion =>
      simp only [Link.shift, Link.produces]
      apply Bool.eq_iff_iff.mpr
      simpa only [beq_iff_eq] using (show
        conclusion + offset = vertex + offset ↔ conclusion = vertex from
          Nat.add_right_cancel_iff)

private theorem usesAsPremise_shift_same (link : Link)
    (offset vertex : Nat) :
    (link.shift offset).usesAsPremise (vertex + offset) =
      link.usesAsPremise vertex := by
  cases link <;>
    simp [Link.shift, Link.usesAsPremise, Link.premises,
      Nat.add_right_cancel_iff]

private theorem containsAxiomEndpoint_shift_below (link : Link)
    {offset vertex : Nat} (below : vertex < offset) :
    (link.shift offset).containsAxiomEndpoint vertex = false := by
  cases link with
  | «axiom» left right =>
      simp only [Link.shift, Link.containsAxiomEndpoint]
      apply Bool.eq_false_iff.mpr
      intro selected
      have equality : left + offset = vertex ∨ right + offset = vertex := by
        simpa only [Bool.or_eq_true, beq_iff_eq] using selected
      rcases equality with equality | equality
      · have vertexBelow : vertex < left + offset :=
          Nat.lt_of_lt_of_le below (Nat.le_add_left offset left)
        exact (Nat.ne_of_gt vertexBelow) equality
      · have vertexBelow : vertex < right + offset :=
          Nat.lt_of_lt_of_le below (Nat.le_add_left offset right)
        exact (Nat.ne_of_gt vertexBelow) equality
  | tensor left right conclusion => rfl
  | par left right conclusion => rfl

private theorem produces_shift_below (link : Link)
    {offset vertex : Nat} (below : vertex < offset) :
    (link.shift offset).produces vertex = false := by
  cases link with
  | «axiom» left right => rfl
  | tensor left right conclusion =>
      simp only [Link.shift, Link.produces]
      apply Bool.eq_false_iff.mpr
      intro selected
      have equality : conclusion + offset = vertex := by
        simpa only [beq_iff_eq] using selected
      have vertexBelow : vertex < conclusion + offset :=
        Nat.lt_of_lt_of_le below (Nat.le_add_left offset conclusion)
      exact (Nat.ne_of_gt vertexBelow) equality
  | par left right conclusion =>
      simp only [Link.shift, Link.produces]
      apply Bool.eq_false_iff.mpr
      intro selected
      have equality : conclusion + offset = vertex := by
        simpa only [beq_iff_eq] using selected
      have vertexBelow : vertex < conclusion + offset :=
        Nat.lt_of_lt_of_le below (Nat.le_add_left offset conclusion)
      exact (Nat.ne_of_gt vertexBelow) equality

private theorem usesAsPremise_shift_below (link : Link)
    {offset vertex : Nat} (below : vertex < offset) :
    (link.shift offset).usesAsPremise vertex = false := by
  cases link with
  | «axiom» left right => rfl
  | tensor left right conclusion =>
      have leftDifferent : left + offset ≠ vertex :=
        Ne.symm (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le below (Nat.le_add_left offset left)))
      have rightDifferent : right + offset ≠ vertex :=
        Ne.symm (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le below (Nat.le_add_left offset right)))
      simp [Link.shift, Link.usesAsPremise, Link.premises,
        Ne.symm leftDifferent, Ne.symm rightDifferent]
  | par left right conclusion =>
      have leftDifferent : left + offset ≠ vertex :=
        Ne.symm (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le below (Nat.le_add_left offset left)))
      have rightDifferent : right + offset ≠ vertex :=
        Ne.symm (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le below (Nat.le_add_left offset right)))
      simp [Link.shift, Link.usesAsPremise, Link.premises,
        Ne.symm leftDifferent, Ne.symm rightDifferent]

private theorem shifted_axiomCount (links : List Link) (offset vertex : Nat) :
    ((links.map (Link.shift offset)).filter
      (fun link => link.containsAxiomEndpoint (vertex + offset))).length =
      (links.filter (fun link => link.containsAxiomEndpoint vertex)).length := by
  induction links with
  | nil => rfl
  | cons link rest ih =>
      rw [List.map_cons, List.filter_cons, List.filter_cons,
        containsAxiomEndpoint_shift_same link offset vertex]
      by_cases selected : link.containsAxiomEndpoint vertex = true <;>
        simp [selected, ih]

private theorem shifted_producerCount (links : List Link)
    (offset vertex : Nat) :
    ((links.map (Link.shift offset)).filter
      (fun link => link.produces (vertex + offset))).length =
      (links.filter (fun link => link.produces vertex)).length := by
  induction links with
  | nil => rfl
  | cons link rest ih =>
      rw [List.map_cons, List.filter_cons, List.filter_cons,
        produces_shift_same link offset vertex]
      by_cases selected : link.produces vertex = true <;>
        simp [selected, ih]

private theorem shifted_parentUseCount (links : List Link)
    (offset vertex : Nat) :
    ((links.map (Link.shift offset)).filter
      (fun link => link.usesAsPremise (vertex + offset))).length =
      (links.filter (fun link => link.usesAsPremise vertex)).length := by
  induction links with
  | nil => rfl
  | cons link rest ih =>
      rw [List.map_cons, List.filter_cons, List.filter_cons,
        usesAsPremise_shift_same link offset vertex]
      by_cases selected : link.usesAsPremise vertex = true <;>
        simp [selected, ih]

private theorem shifted_axiomCount_below (links : List Link)
    {offset vertex : Nat} (below : vertex < offset) :
    ((links.map (Link.shift offset)).filter
      (fun link => link.containsAxiomEndpoint vertex)).length = 0 := by
  induction links with
  | nil => rfl
  | cons link rest ih =>
      rw [List.map_cons, List.filter_cons,
        containsAxiomEndpoint_shift_below link below]
      simp [ih]

private theorem shifted_producerCount_below (links : List Link)
    {offset vertex : Nat} (below : vertex < offset) :
    ((links.map (Link.shift offset)).filter
      (fun link => link.produces vertex)).length = 0 := by
  induction links with
  | nil => rfl
  | cons link rest ih =>
      rw [List.map_cons, List.filter_cons,
        produces_shift_below link below]
      simp [ih]

private theorem shifted_parentUseCount_below (links : List Link)
    {offset vertex : Nat} (below : vertex < offset) :
    ((links.map (Link.shift offset)).filter
      (fun link => link.usesAsPremise vertex)).length = 0 := by
  induction links with
  | nil => rfl
  | cons link rest ih =>
      rw [List.map_cons, List.filter_cons,
        usesAsPremise_shift_below link below]
      simp [ih]

private theorem formula?_appendTensorOccurrence_left
    (leftPremise rightPremise : Certificate) (left right : Formula)
    (leftRoot rightRoot : Vertex) (boundary : List Vertex)
    {vertex : Vertex} (inBounds : vertex < leftPremise.formulas.size) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot boundary).formula? vertex = leftPremise.formula? vertex := by
  change ((leftPremise.formulas ++ rightPremise.formulas).push
      (.tensor left right))[vertex]? = leftPremise.formulas[vertex]?
  rw [Array.getElem?_push, if_neg (by
    have combinedBound : vertex <
        (leftPremise.formulas ++ rightPremise.formulas).size := by
      simpa using Nat.lt_of_lt_of_le inBounds
        (Nat.le_add_right leftPremise.formulas.size
          rightPremise.formulas.size)
    exact Nat.ne_of_lt combinedBound)]
  exact Array.getElem?_append_left inBounds

private theorem formula?_appendTensorOccurrence_right
    (leftPremise rightPremise : Certificate) (left right : Formula)
    (leftRoot rightRoot : Vertex) (boundary : List Vertex)
    {vertex : Vertex} (inBounds : vertex < rightPremise.formulas.size) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot boundary).formula? (vertex + leftPremise.formulas.size) =
        rightPremise.formula? vertex := by
  change ((leftPremise.formulas ++ rightPremise.formulas).push
      (.tensor left right))[vertex + leftPremise.formulas.size]? =
        rightPremise.formulas[vertex]?
  have combinedBound : vertex + leftPremise.formulas.size <
      (leftPremise.formulas ++ rightPremise.formulas).size := by
    simpa [Nat.add_comm] using Nat.add_lt_add_right inBounds
      leftPremise.formulas.size
  rw [Array.getElem?_push, if_neg (Nat.ne_of_lt combinedBound)]
  rw [Array.getElem?_append_right
    (Nat.le_add_left leftPremise.formulas.size vertex)]
  rw [show vertex + leftPremise.formulas.size -
      leftPremise.formulas.size = vertex by
        exact Nat.add_sub_cancel_right vertex leftPremise.formulas.size]

private theorem appendTensorOccurrence_left_bound
    (leftPremise rightPremise : Certificate) (left right : Formula)
    (leftRoot rightRoot : Vertex) (boundary : List Vertex)
    {vertex : Vertex} (inBounds : vertex < leftPremise.formulas.size) :
    vertex < (leftPremise.appendTensorOccurrence rightPremise left right
      leftRoot rightRoot boundary).formulas.size := by
  rw [appendTensorOccurrence_formulas_size]
  exact Nat.lt_of_lt_of_le inBounds (by simp [Nat.add_assoc])

private theorem appendTensorOccurrence_right_bound
    (leftPremise rightPremise : Certificate) (left right : Formula)
    (leftRoot rightRoot : Vertex) (boundary : List Vertex)
    {vertex : Vertex} (inBounds : vertex < rightPremise.formulas.size) :
    vertex + leftPremise.formulas.size <
      (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
        rightRoot boundary).formulas.size := by
  rw [appendTensorOccurrence_formulas_size]
  have beforeFresh : vertex + leftPremise.formulas.size <
      leftPremise.formulas.size + rightPremise.formulas.size := by
    simpa [Nat.add_comm] using Nat.add_lt_add_right inBounds
      leftPremise.formulas.size
  exact Nat.lt_trans beforeFresh (Nat.lt_succ_self _)

private theorem LinkWellFormed.appendTensorOccurrence_left
    {leftPremise rightPremise : Certificate} {link : Link}
    (wellFormed : leftPremise.LinkWellFormed link)
    (left right : Formula) (leftRoot rightRoot : Vertex)
    (boundary : List Vertex) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot boundary).LinkWellFormed link := by
  cases link with
  | «axiom» first second =>
      rcases wellFormed with ⟨different, firstBound, secondBound, typing⟩
      simp only [LinkWellFormed]
      refine ⟨different,
        appendTensorOccurrence_left_bound leftPremise rightPremise left right
          leftRoot rightRoot boundary firstBound,
        appendTensorOccurrence_left_bound leftPremise rightPremise left right
          leftRoot rightRoot boundary secondBound, ?_⟩
      rw [formula?_appendTensorOccurrence_left leftPremise rightPremise left
          right leftRoot rightRoot boundary firstBound,
        formula?_appendTensorOccurrence_left leftPremise rightPremise left
          right leftRoot rightRoot boundary secondBound]
      exact typing
  | tensor first second conclusion =>
      rcases wellFormed with
        ⟨firstSecond, firstConclusion, secondConclusion,
          firstBound, secondBound, conclusionBound, typing⟩
      simp only [LinkWellFormed]
      refine ⟨firstSecond, firstConclusion, secondConclusion,
        appendTensorOccurrence_left_bound leftPremise rightPremise left right
          leftRoot rightRoot boundary firstBound,
        appendTensorOccurrence_left_bound leftPremise rightPremise left right
          leftRoot rightRoot boundary secondBound,
        appendTensorOccurrence_left_bound leftPremise rightPremise left right
          leftRoot rightRoot boundary conclusionBound, ?_⟩
      rw [formula?_appendTensorOccurrence_left leftPremise rightPremise left
          right leftRoot rightRoot boundary firstBound,
        formula?_appendTensorOccurrence_left leftPremise rightPremise left
          right leftRoot rightRoot boundary secondBound,
        formula?_appendTensorOccurrence_left leftPremise rightPremise left
          right leftRoot rightRoot boundary conclusionBound]
      exact typing
  | par first second conclusion =>
      rcases wellFormed with
        ⟨firstSecond, firstConclusion, secondConclusion,
          firstBound, secondBound, conclusionBound, typing⟩
      simp only [LinkWellFormed]
      refine ⟨firstSecond, firstConclusion, secondConclusion,
        appendTensorOccurrence_left_bound leftPremise rightPremise left right
          leftRoot rightRoot boundary firstBound,
        appendTensorOccurrence_left_bound leftPremise rightPremise left right
          leftRoot rightRoot boundary secondBound,
        appendTensorOccurrence_left_bound leftPremise rightPremise left right
          leftRoot rightRoot boundary conclusionBound, ?_⟩
      rw [formula?_appendTensorOccurrence_left leftPremise rightPremise left
          right leftRoot rightRoot boundary firstBound,
        formula?_appendTensorOccurrence_left leftPremise rightPremise left
          right leftRoot rightRoot boundary secondBound,
        formula?_appendTensorOccurrence_left leftPremise rightPremise left
          right leftRoot rightRoot boundary conclusionBound]
      exact typing

private theorem LinkWellFormed.appendTensorOccurrence_right
    {leftPremise rightPremise : Certificate} {link : Link}
    (wellFormed : rightPremise.LinkWellFormed link)
    (left right : Formula) (leftRoot rightRoot : Vertex)
    (boundary : List Vertex) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot boundary).LinkWellFormed
        (link.shift leftPremise.formulas.size) := by
  cases link with
  | «axiom» first second =>
      rcases wellFormed with ⟨different, firstBound, secondBound, typing⟩
      simp only [Link.shift, LinkWellFormed]
      refine ⟨fun shifted => different (Nat.add_right_cancel shifted),
        appendTensorOccurrence_right_bound leftPremise rightPremise left right
          leftRoot rightRoot boundary firstBound,
        appendTensorOccurrence_right_bound leftPremise rightPremise left right
          leftRoot rightRoot boundary secondBound, ?_⟩
      rw [formula?_appendTensorOccurrence_right leftPremise rightPremise left
          right leftRoot rightRoot boundary firstBound,
        formula?_appendTensorOccurrence_right leftPremise rightPremise left
          right leftRoot rightRoot boundary secondBound]
      exact typing
  | tensor first second conclusion =>
      rcases wellFormed with
        ⟨firstSecond, firstConclusion, secondConclusion,
          firstBound, secondBound, conclusionBound, typing⟩
      simp only [Link.shift, LinkWellFormed]
      refine ⟨fun shifted => firstSecond (Nat.add_right_cancel shifted),
        fun shifted => firstConclusion (Nat.add_right_cancel shifted),
        fun shifted => secondConclusion (Nat.add_right_cancel shifted),
        appendTensorOccurrence_right_bound leftPremise rightPremise left right
          leftRoot rightRoot boundary firstBound,
        appendTensorOccurrence_right_bound leftPremise rightPremise left right
          leftRoot rightRoot boundary secondBound,
        appendTensorOccurrence_right_bound leftPremise rightPremise left right
          leftRoot rightRoot boundary conclusionBound, ?_⟩
      rw [formula?_appendTensorOccurrence_right leftPremise rightPremise left
          right leftRoot rightRoot boundary firstBound,
        formula?_appendTensorOccurrence_right leftPremise rightPremise left
          right leftRoot rightRoot boundary secondBound,
        formula?_appendTensorOccurrence_right leftPremise rightPremise left
          right leftRoot rightRoot boundary conclusionBound]
      exact typing
  | par first second conclusion =>
      rcases wellFormed with
        ⟨firstSecond, firstConclusion, secondConclusion,
          firstBound, secondBound, conclusionBound, typing⟩
      simp only [Link.shift, LinkWellFormed]
      refine ⟨fun shifted => firstSecond (Nat.add_right_cancel shifted),
        fun shifted => firstConclusion (Nat.add_right_cancel shifted),
        fun shifted => secondConclusion (Nat.add_right_cancel shifted),
        appendTensorOccurrence_right_bound leftPremise rightPremise left right
          leftRoot rightRoot boundary firstBound,
        appendTensorOccurrence_right_bound leftPremise rightPremise left right
          leftRoot rightRoot boundary secondBound,
        appendTensorOccurrence_right_bound leftPremise rightPremise left right
          leftRoot rightRoot boundary conclusionBound, ?_⟩
      rw [formula?_appendTensorOccurrence_right leftPremise rightPremise left
          right leftRoot rightRoot boundary firstBound,
        formula?_appendTensorOccurrence_right leftPremise rightPremise left
          right leftRoot rightRoot boundary secondBound,
        formula?_appendTensorOccurrence_right leftPremise rightPremise left
          right leftRoot rightRoot boundary conclusionBound]
      exact typing

private theorem LinkWellFormed.appendTensorOccurrence_new
    {leftPremise rightPremise : Certificate} (left right : Formula)
    {leftRoot rightRoot : Vertex}
    (leftRootInBounds : leftRoot < leftPremise.formulas.size)
    (rightRootInBounds : rightRoot < rightPremise.formulas.size)
    (leftLookup : leftPremise.formula? leftRoot = some left)
    (rightLookup : rightPremise.formula? rightRoot = some right)
    (boundary : List Vertex) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot boundary).LinkWellFormed
        (.tensor leftRoot (rightRoot + leftPremise.formulas.size)
          (leftPremise.formulas ++ rightPremise.formulas).size) := by
  simp only [LinkWellFormed]
  have leftBeforeRight : leftRoot <
      rightRoot + leftPremise.formulas.size :=
    Nat.lt_of_lt_of_le leftRootInBounds
      (Nat.le_add_left leftPremise.formulas.size rightRoot)
  have leftBeforeFresh : leftRoot <
      (leftPremise.formulas ++ rightPremise.formulas).size := by
    simpa using Nat.lt_of_lt_of_le leftRootInBounds
      (Nat.le_add_right leftPremise.formulas.size
        rightPremise.formulas.size)
  have rightBeforeFresh : rightRoot + leftPremise.formulas.size <
      (leftPremise.formulas ++ rightPremise.formulas).size := by
    simpa [Nat.add_comm] using Nat.add_lt_add_right rightRootInBounds
      leftPremise.formulas.size
  refine ⟨Nat.ne_of_lt leftBeforeRight, Nat.ne_of_lt leftBeforeFresh,
    Nat.ne_of_lt rightBeforeFresh,
    appendTensorOccurrence_left_bound leftPremise rightPremise left right
      leftRoot rightRoot boundary leftRootInBounds,
    appendTensorOccurrence_right_bound leftPremise rightPremise left right
      leftRoot rightRoot boundary rightRootInBounds,
    by simp [appendTensorOccurrence], ?_⟩
  rw [formula?_appendTensorOccurrence_left leftPremise rightPremise left right
      leftRoot rightRoot boundary leftRootInBounds,
    formula?_appendTensorOccurrence_right leftPremise rightPremise left right
      leftRoot rightRoot boundary rightRootInBounds,
    leftLookup, rightLookup]
  have freshFormula :
      (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
        rightRoot boundary).formula?
          (leftPremise.formulas ++ rightPremise.formulas).size =
        some (.tensor left right) := by
    change ((leftPremise.formulas ++ rightPremise.formulas).push
      (.tensor left right))[(leftPremise.formulas ++
        rightPremise.formulas).size]? = some (.tensor left right)
    exact Array.getElem?_push_size
  rw [freshFormula]

private theorem axiomCount_appendTensorOccurrence_left
    (leftPremise rightPremise : Certificate) (left right : Formula)
    (leftRoot rightRoot : Vertex) (boundary : List Vertex)
    {vertex : Vertex} (inBounds : vertex < leftPremise.formulas.size) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot boundary).axiomCount vertex =
        leftPremise.axiomCount vertex := by
  unfold axiomCount
  simp only [appendTensorOccurrence, List.filter_append, List.length_append]
  rw [shifted_axiomCount_below rightPremise.links inBounds]
  simp [Link.containsAxiomEndpoint]

private theorem producerCount_appendTensorOccurrence_left
    (leftPremise rightPremise : Certificate) (left right : Formula)
    (leftRoot rightRoot : Vertex) (boundary : List Vertex)
    {vertex : Vertex} (inBounds : vertex < leftPremise.formulas.size) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot boundary).producerCount vertex =
        leftPremise.producerCount vertex := by
  unfold producerCount
  simp only [appendTensorOccurrence, List.filter_append, List.length_append]
  rw [shifted_producerCount_below rightPremise.links inBounds]
  have notFresh : leftPremise.formulas.size +
      rightPremise.formulas.size ≠ vertex := by
    have beforeFresh : vertex <
        leftPremise.formulas.size + rightPremise.formulas.size := by
      exact Nat.lt_of_lt_of_le inBounds
        (Nat.le_add_right leftPremise.formulas.size
          rightPremise.formulas.size)
    exact Ne.symm (Nat.ne_of_lt beforeFresh)
  simp [Link.produces, notFresh]

private theorem parentUseCount_appendTensorOccurrence_left_selected
    (leftPremise rightPremise : Certificate) (left right : Formula)
    {leftRoot rightRoot : Vertex}
    (leftRootInBounds : leftRoot < leftPremise.formulas.size)
    (boundary : List Vertex) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot boundary).parentUseCount leftRoot =
        leftPremise.parentUseCount leftRoot + 1 := by
  unfold parentUseCount
  simp only [appendTensorOccurrence, List.filter_append, List.length_append]
  rw [shifted_parentUseCount_below rightPremise.links leftRootInBounds]
  have notRight : leftRoot ≠ rightRoot + leftPremise.formulas.size :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le leftRootInBounds
      (Nat.le_add_left leftPremise.formulas.size rightRoot))
  simp [Link.usesAsPremise, Link.premises, notRight]

private theorem parentUseCount_appendTensorOccurrence_left_other
    (leftPremise rightPremise : Certificate) (left right : Formula)
    {leftRoot rightRoot vertex : Vertex}
    (inBounds : vertex < leftPremise.formulas.size)
    (notLeft : vertex ≠ leftRoot) (boundary : List Vertex) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot boundary).parentUseCount vertex =
        leftPremise.parentUseCount vertex := by
  unfold parentUseCount
  simp only [appendTensorOccurrence, List.filter_append, List.length_append]
  rw [shifted_parentUseCount_below rightPremise.links inBounds]
  have notRight : vertex ≠ rightRoot + leftPremise.formulas.size :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le inBounds
      (Nat.le_add_left leftPremise.formulas.size rightRoot))
  simp [Link.usesAsPremise, Link.premises, notLeft, notRight]

private theorem axiomCount_appendTensorOccurrence_right
    {leftPremise rightPremise : Certificate}
    (leftStructural : leftPremise.StructurallyWellFormed)
    (left right : Formula) (leftRoot rightRoot : Vertex)
    (boundary : List Vertex) {vertex : Vertex}
    (_inBounds : vertex < rightPremise.formulas.size) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot boundary).axiomCount
        (vertex + leftPremise.formulas.size) =
          rightPremise.axiomCount vertex := by
  unfold axiomCount
  simp only [appendTensorOccurrence, List.filter_append, List.length_append]
  have leftZero := leftStructural.axiomCount_outOfBounds
    (vertex := vertex + leftPremise.formulas.size)
    (Nat.le_add_left leftPremise.formulas.size vertex)
  unfold axiomCount at leftZero
  rw [leftZero, shifted_axiomCount rightPremise.links
    leftPremise.formulas.size vertex]
  simp [Link.containsAxiomEndpoint]

private theorem producerCount_appendTensorOccurrence_right
    {leftPremise rightPremise : Certificate}
    (leftStructural : leftPremise.StructurallyWellFormed)
    (left right : Formula) (leftRoot rightRoot : Vertex)
    (boundary : List Vertex) {vertex : Vertex}
    (inBounds : vertex < rightPremise.formulas.size) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot boundary).producerCount
        (vertex + leftPremise.formulas.size) =
          rightPremise.producerCount vertex := by
  unfold producerCount
  simp only [appendTensorOccurrence, List.filter_append, List.length_append]
  have leftZero := leftStructural.producerCount_outOfBounds
    (vertex := vertex + leftPremise.formulas.size)
    (Nat.le_add_left leftPremise.formulas.size vertex)
  unfold producerCount at leftZero
  rw [leftZero, shifted_producerCount rightPremise.links
    leftPremise.formulas.size vertex]
  have beforeFresh : vertex + leftPremise.formulas.size <
      leftPremise.formulas.size + rightPremise.formulas.size := by
    simpa [Nat.add_comm] using Nat.add_lt_add_right inBounds
      leftPremise.formulas.size
  have notFresh : leftPremise.formulas.size +
      rightPremise.formulas.size ≠
        vertex + leftPremise.formulas.size :=
    Ne.symm (Nat.ne_of_lt beforeFresh)
  simp [Link.produces, notFresh]

private theorem parentUseCount_appendTensorOccurrence_right_selected
    {leftPremise rightPremise : Certificate}
    (leftStructural : leftPremise.StructurallyWellFormed)
    (left right : Formula) {leftRoot rightRoot : Vertex}
    (leftRootInBounds : leftRoot < leftPremise.formulas.size)
    (boundary : List Vertex) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot boundary).parentUseCount
        (rightRoot + leftPremise.formulas.size) =
          rightPremise.parentUseCount rightRoot + 1 := by
  unfold parentUseCount
  simp only [appendTensorOccurrence, List.filter_append, List.length_append]
  have leftZero := leftStructural.parentUseCount_outOfBounds
    (vertex := rightRoot + leftPremise.formulas.size)
    (Nat.le_add_left leftPremise.formulas.size rightRoot)
  unfold parentUseCount at leftZero
  rw [leftZero, shifted_parentUseCount rightPremise.links
    leftPremise.formulas.size rightRoot]
  have notLeft : rightRoot + leftPremise.formulas.size ≠ leftRoot := by
    exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le leftRootInBounds
      (Nat.le_add_left leftPremise.formulas.size rightRoot)))
  simp [Link.usesAsPremise, Link.premises, notLeft]

private theorem parentUseCount_appendTensorOccurrence_right_other
    {leftPremise rightPremise : Certificate}
    (leftStructural : leftPremise.StructurallyWellFormed)
    (left right : Formula) {leftRoot rightRoot vertex : Vertex}
    (leftRootInBounds : leftRoot < leftPremise.formulas.size)
    (notRight : vertex ≠ rightRoot) (boundary : List Vertex) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot boundary).parentUseCount
        (vertex + leftPremise.formulas.size) =
          rightPremise.parentUseCount vertex := by
  unfold parentUseCount
  simp only [appendTensorOccurrence, List.filter_append, List.length_append]
  have leftZero := leftStructural.parentUseCount_outOfBounds
    (vertex := vertex + leftPremise.formulas.size)
    (Nat.le_add_left leftPremise.formulas.size vertex)
  unfold parentUseCount at leftZero
  rw [leftZero, shifted_parentUseCount rightPremise.links
    leftPremise.formulas.size vertex]
  have notLeft : vertex + leftPremise.formulas.size ≠ leftRoot :=
    Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le leftRootInBounds
      (Nat.le_add_left leftPremise.formulas.size vertex)))
  simp [Link.usesAsPremise, Link.premises, notLeft, notRight]

private theorem axiomCount_appendTensorOccurrence_new
    {leftPremise rightPremise : Certificate}
    (leftStructural : leftPremise.StructurallyWellFormed)
    (rightStructural : rightPremise.StructurallyWellFormed)
    (left right : Formula) (leftRoot rightRoot : Vertex)
    (boundary : List Vertex) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot boundary).axiomCount
        (leftPremise.formulas ++ rightPremise.formulas).size = 0 := by
  unfold axiomCount
  simp only [appendTensorOccurrence, List.filter_append, List.length_append,
    Array.size_append]
  have leftZero := leftStructural.axiomCount_outOfBounds
    (vertex := leftPremise.formulas.size + rightPremise.formulas.size)
    (Nat.le_add_right leftPremise.formulas.size
      rightPremise.formulas.size)
  unfold axiomCount at leftZero
  have rightZero := rightStructural.axiomCount_outOfBounds
    (vertex := rightPremise.formulas.size) (Nat.le_refl _)
  unfold axiomCount at rightZero
  have shiftedZero :
      ((rightPremise.links.map (Link.shift leftPremise.formulas.size)).filter
        (fun link => link.containsAxiomEndpoint
          (leftPremise.formulas.size + rightPremise.formulas.size))).length =
        0 := by
    rw [show leftPremise.formulas.size + rightPremise.formulas.size =
        rightPremise.formulas.size + leftPremise.formulas.size by
          exact Nat.add_comm _ _,
      shifted_axiomCount rightPremise.links leftPremise.formulas.size
        rightPremise.formulas.size,
      rightZero]
  rw [leftZero, shiftedZero]
  simp [Link.containsAxiomEndpoint]

private theorem producerCount_appendTensorOccurrence_new
    {leftPremise rightPremise : Certificate}
    (leftStructural : leftPremise.StructurallyWellFormed)
    (rightStructural : rightPremise.StructurallyWellFormed)
    (left right : Formula) (leftRoot rightRoot : Vertex)
    (boundary : List Vertex) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot boundary).producerCount
        (leftPremise.formulas ++ rightPremise.formulas).size = 1 := by
  unfold producerCount
  simp only [appendTensorOccurrence, List.filter_append, List.length_append,
    Array.size_append]
  have leftZero := leftStructural.producerCount_outOfBounds
    (vertex := leftPremise.formulas.size + rightPremise.formulas.size)
    (Nat.le_add_right leftPremise.formulas.size
      rightPremise.formulas.size)
  unfold producerCount at leftZero
  have rightZero := rightStructural.producerCount_outOfBounds
    (vertex := rightPremise.formulas.size) (Nat.le_refl _)
  unfold producerCount at rightZero
  have shiftedZero :
      ((rightPremise.links.map (Link.shift leftPremise.formulas.size)).filter
        (fun link => link.produces
          (leftPremise.formulas.size + rightPremise.formulas.size))).length =
        0 := by
    rw [show leftPremise.formulas.size + rightPremise.formulas.size =
        rightPremise.formulas.size + leftPremise.formulas.size by
          exact Nat.add_comm _ _,
      shifted_producerCount rightPremise.links leftPremise.formulas.size
        rightPremise.formulas.size,
      rightZero]
  rw [leftZero, shiftedZero]
  simp [Link.produces]

private theorem parentUseCount_appendTensorOccurrence_new
    {leftPremise rightPremise : Certificate}
    (leftStructural : leftPremise.StructurallyWellFormed)
    (rightStructural : rightPremise.StructurallyWellFormed)
    (left right : Formula) {leftRoot rightRoot : Vertex}
    (leftRootInBounds : leftRoot < leftPremise.formulas.size)
    (rightRootInBounds : rightRoot < rightPremise.formulas.size)
    (boundary : List Vertex) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot boundary).parentUseCount
        (leftPremise.formulas ++ rightPremise.formulas).size = 0 := by
  unfold parentUseCount
  simp only [appendTensorOccurrence, List.filter_append, List.length_append,
    Array.size_append]
  have leftZero := leftStructural.parentUseCount_outOfBounds
    (vertex := leftPremise.formulas.size + rightPremise.formulas.size)
    (Nat.le_add_right leftPremise.formulas.size
      rightPremise.formulas.size)
  unfold parentUseCount at leftZero
  have rightZero := rightStructural.parentUseCount_outOfBounds
    (vertex := rightPremise.formulas.size) (Nat.le_refl _)
  unfold parentUseCount at rightZero
  have shiftedZero :
      ((rightPremise.links.map (Link.shift leftPremise.formulas.size)).filter
        (fun link => link.usesAsPremise
          (leftPremise.formulas.size + rightPremise.formulas.size))).length =
        0 := by
    rw [show leftPremise.formulas.size + rightPremise.formulas.size =
        rightPremise.formulas.size + leftPremise.formulas.size by
          exact Nat.add_comm _ _,
      shifted_parentUseCount rightPremise.links leftPremise.formulas.size
        rightPremise.formulas.size,
      rightZero]
  rw [leftZero, shiftedZero]
  have notLeft : leftPremise.formulas.size + rightPremise.formulas.size ≠
      leftRoot := Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le
        leftRootInBounds (Nat.le_add_right leftPremise.formulas.size
          rightPremise.formulas.size)))
  have notRight : leftPremise.formulas.size + rightPremise.formulas.size ≠
      rightRoot + leftPremise.formulas.size := by
    have beforeFresh : rightRoot + leftPremise.formulas.size <
        leftPremise.formulas.size + rightPremise.formulas.size := by
      simpa [Nat.add_comm] using Nat.add_lt_add_right rightRootInBounds
        leftPremise.formulas.size
    exact Ne.symm (Nat.ne_of_lt beforeFresh)
  simp [Link.usesAsPremise, Link.premises, notLeft, notRight]


private theorem LinkWellFormed.appendParOccurrence_new
    {premise : Certificate} (left right : Formula)
    {leftRoot rightRoot : Vertex}
    (different : leftRoot ≠ rightRoot)
    (leftRootInBounds : leftRoot < premise.formulas.size)
    (rightRootInBounds : rightRoot < premise.formulas.size)
    (leftLookup : premise.formula? leftRoot = some left)
    (rightLookup : premise.formula? rightRoot = some right)
    (boundary : List Vertex) :
    (premise.appendParOccurrence left right leftRoot rightRoot boundary).LinkWellFormed
      (.par leftRoot rightRoot premise.formulas.size) := by
  simp only [LinkWellFormed]
  refine ⟨different, Nat.ne_of_lt leftRootInBounds,
    Nat.ne_of_lt rightRootInBounds,
    by simpa [appendParOccurrence] using Nat.lt_succ_of_lt leftRootInBounds,
    by simpa [appendParOccurrence] using Nat.lt_succ_of_lt rightRootInBounds,
    by simp [appendParOccurrence], ?_⟩
  rw [formula?_appendParOccurrence_old premise left right leftRoot rightRoot
      boundary leftRootInBounds,
    formula?_appendParOccurrence_old premise left right leftRoot rightRoot
      boundary rightRootInBounds,
    leftLookup, rightLookup]
  simp [appendParOccurrence, formula?]

private theorem producerCount_appendParOccurrence_new
    {premise : Certificate} (structural : premise.StructurallyWellFormed)
    (left right : Formula) (leftRoot rightRoot : Vertex)
    (boundary : List Vertex) :
    (premise.appendParOccurrence left right leftRoot rightRoot boundary).producerCount
      premise.formulas.size = 1 := by
  rw [show (premise.appendParOccurrence left right leftRoot rightRoot
      boundary).producerCount premise.formulas.size =
        premise.producerCount premise.formulas.size + 1 by
    simp [producerCount, appendParOccurrence, Link.produces]]
  rw [structural.producerCount_at_size]

private theorem parentUseCount_appendParOccurrence_new
    {premise : Certificate} (structural : premise.StructurallyWellFormed)
    (left right : Formula) (leftRoot rightRoot : Vertex)
    (leftRootInBounds : leftRoot < premise.formulas.size)
    (rightRootInBounds : rightRoot < premise.formulas.size)
    (boundary : List Vertex) :
    (premise.appendParOccurrence left right leftRoot rightRoot boundary).parentUseCount
      premise.formulas.size = 0 := by
  rw [show (premise.appendParOccurrence left right leftRoot rightRoot
      boundary).parentUseCount premise.formulas.size =
        premise.parentUseCount premise.formulas.size by
    simp [parentUseCount, appendParOccurrence, Link.usesAsPremise,
      Link.premises, Nat.ne_of_gt leftRootInBounds,
      Nat.ne_of_gt rightRootInBounds]]
  exact structural.parentUseCount_at_size

/-- Adding a par link at two distinct boundary occurrences preserves the full
structural certificate invariant.  The explicit permutation hypothesis states
that `leftRoot` and `rightRoot` are exactly the two occurrences removed from
the old boundary. -/
theorem StructurallyWellFormed.appendParOccurrence
    {premise : Certificate} (structural : premise.StructurallyWellFormed)
    (left right : Formula) {leftRoot rightRoot : Vertex}
    (leftLookup : premise.formula? leftRoot = some left)
    (rightLookup : premise.formula? rightRoot = some right)
    (remaining : List Vertex)
    (boundaryPermutation :
      premise.conclusions.Perm (leftRoot :: rightRoot :: remaining)) :
    (premise.appendParOccurrence left right leftRoot rightRoot
      (remaining ++ [premise.formulas.size])).StructurallyWellFormed := by
  have premiseBoundaryNodup : premise.conclusions.Nodup :=
    nodup_of_eraseDups_length_eq structural.2.2.2.1
  have decomposedNodup : (leftRoot :: rightRoot :: remaining).Nodup :=
    boundaryPermutation.nodup_iff.mp premiseBoundaryNodup
  have leftDifferentRight : leftRoot ≠ rightRoot := by
    exact fun same => (List.nodup_cons.mp decomposedNodup).1 (by simp [same])
  have remainingNodup : remaining.Nodup :=
    (List.nodup_cons.mp (List.nodup_cons.mp decomposedNodup).2).2
  have leftNotRemaining : leftRoot ∉ remaining := by
    intro membership
    exact (List.nodup_cons.mp decomposedNodup).1 (by simp [membership])
  have rightNotRemaining : rightRoot ∉ remaining :=
    (List.nodup_cons.mp (List.nodup_cons.mp decomposedNodup).2).1
  have leftBoundary : leftRoot ∈ premise.conclusions :=
    boundaryPermutation.mem_iff.mpr (by simp)
  have rightBoundary : rightRoot ∈ premise.conclusions :=
    boundaryPermutation.mem_iff.mpr (by simp)
  have leftRootInBounds : leftRoot < premise.formulas.size :=
    structural.2.2.1 leftRoot leftBoundary
  have rightRootInBounds : rightRoot < premise.formulas.size :=
    structural.2.2.1 rightRoot rightBoundary
  have remainingInBounds : ∀ vertex ∈ remaining,
      vertex < premise.formulas.size := by
    intro vertex membership
    exact structural.2.2.1 vertex
      (boundaryPermutation.mem_iff.mpr (by simp [membership]))
  have freshNotRemaining : premise.formulas.size ∉ remaining := by
    intro membership
    exact (Nat.ne_of_lt (remainingInBounds _ membership)) rfl
  have outputBoundaryNodup :
      (remaining ++ [premise.formulas.size]).Nodup := by
    rw [List.nodup_append]
    refine ⟨remainingNodup, by simp, ?_⟩
    intro oldVertex oldMembership freshVertex freshMembership
    have freshEquation : freshVertex = premise.formulas.size := by
      simpa using freshMembership
    subst freshVertex
    exact fun same => freshNotRemaining (same ▸ oldMembership)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change 0 < (premise.formulas.push (.par left right)).size
    simp
  · change 0 < (remaining ++ [premise.formulas.size]).length
    simp
  · intro vertex membership
    change vertex ∈ remaining ++ [premise.formulas.size] at membership
    rw [List.mem_append] at membership
    simp only [List.mem_singleton] at membership
    rcases membership with old | fresh
    · change vertex < (premise.formulas.push (.par left right)).size
      simpa using Nat.lt_succ_of_lt (remainingInBounds vertex old)
    · subst vertex
      change premise.formulas.size <
        (premise.formulas.push (.par left right)).size
      simp
  · change (remaining ++ [premise.formulas.size]).eraseDups.length =
      (remaining ++ [premise.formulas.size]).length
    rw [eraseDups_eq_self_of_nodup outputBoundaryNodup]
  · intro link membership
    change link ∈ premise.links ++
      [Link.par leftRoot rightRoot premise.formulas.size] at membership
    rw [List.mem_append] at membership
    simp only [List.mem_singleton] at membership
    rcases membership with old | fresh
    · exact (structural.2.2.2.2.1 link old).appendParOccurrence_old
        left right leftRoot rightRoot
        (remaining ++ [premise.formulas.size])
    · subst link
      exact LinkWellFormed.appendParOccurrence_new left right
        leftDifferentRight leftRootInBounds rightRootInBounds
        leftLookup rightLookup (remaining ++ [premise.formulas.size])
  · intro vertex inBounds
    have oldOrFresh : vertex < premise.formulas.size ∨
        vertex = premise.formulas.size := by
      rw [appendParOccurrence_formulas_size] at inBounds
      omega
    rcases oldOrFresh with oldInBounds | fresh
    · have oldNode := structural.2.2.2.2.2 vertex oldInBounds
      have oldFormula := formula?_appendParOccurrence_old premise left right
        leftRoot rightRoot (remaining ++ [premise.formulas.size]) oldInBounds
      unfold NodeWellFormed at oldNode ⊢
      rw [oldFormula]
      constructor
      · cases formulaEquation : premise.formula? vertex with
        | none => simp [formulaEquation] at oldNode
        | some formula =>
            cases formula with
            | atom name positive =>
                simpa [formulaEquation,
                  axiomCount_appendParOccurrence_old] using oldNode.1
            | tensor first second =>
                simpa [formulaEquation,
                  producerCount_appendParOccurrence_old premise left right
                    leftRoot rightRoot
                    (remaining ++ [premise.formulas.size]) oldInBounds] using
                      oldNode.1
            | par first second =>
                simpa [formulaEquation,
                  producerCount_appendParOccurrence_old premise left right
                    leftRoot rightRoot
                    (remaining ++ [premise.formulas.size]) oldInBounds] using
                      oldNode.1
      · by_cases isLeft : vertex = leftRoot
        · subst vertex
          have newNotBoundary : leftRoot ∉
              (premise.appendParOccurrence left right leftRoot rightRoot
                (remaining ++ [premise.formulas.size])).conclusions := by
            simpa [Certificate.appendParOccurrence] using (show
              leftRoot ∉ remaining ++ [premise.formulas.size] by
                simp [leftNotRemaining, Nat.ne_of_lt leftRootInBounds])
          rw [parentUseCount_appendParOccurrence_left premise left right
            leftDifferentRight]
          rw [if_neg newNotBoundary]
          rw [if_pos leftBoundary] at oldNode
          omega
        · by_cases isRight : vertex = rightRoot
          · subst vertex
            have newNotBoundary : rightRoot ∉
                (premise.appendParOccurrence left right leftRoot rightRoot
                  (remaining ++ [premise.formulas.size])).conclusions := by
              simpa [Certificate.appendParOccurrence] using (show
                rightRoot ∉ remaining ++ [premise.formulas.size] by
                  simp [rightNotRemaining, Nat.ne_of_lt rightRootInBounds])
            rw [parentUseCount_appendParOccurrence_right premise left right
              leftDifferentRight]
            rw [if_neg newNotBoundary]
            rw [if_pos rightBoundary] at oldNode
            omega
          · have boundaryIff :
                vertex ∈ remaining ↔ vertex ∈ premise.conclusions := by
              constructor
              · intro membership
                exact boundaryPermutation.mem_iff.mpr (by
                  simp [membership])
              · intro membership
                have decomposed := boundaryPermutation.mem_iff.mp membership
                simpa [isLeft, isRight] using decomposed
            have notFresh : vertex ≠ premise.formulas.size :=
              Nat.ne_of_lt oldInBounds
            rw [parentUseCount_appendParOccurrence_other premise left right
              isLeft isRight]
            have outputBoundaryIff :
                vertex ∈
                    (premise.appendParOccurrence left right leftRoot rightRoot
                      (remaining ++ [premise.formulas.size])).conclusions ↔
                  vertex ∈ premise.conclusions := by
              simpa [Certificate.appendParOccurrence] using (show
                vertex ∈ remaining ++ [premise.formulas.size] ↔
                  vertex ∈ premise.conclusions by
                    simp [notFresh, boundaryIff])
            by_cases oldBoundary : vertex ∈ premise.conclusions
            · rw [if_pos (outputBoundaryIff.mpr oldBoundary)]
              rw [if_pos oldBoundary] at oldNode
              exact oldNode.2
            · rw [if_neg (fun membership =>
                oldBoundary (outputBoundaryIff.mp membership))]
              rw [if_neg oldBoundary] at oldNode
              exact oldNode.2
    · subst vertex
      unfold NodeWellFormed
      constructor
      · have formulaEquation :
            (premise.appendParOccurrence left right leftRoot rightRoot
              (remaining ++ [premise.formulas.size])).formula?
                premise.formulas.size = some (.par left right) := by
          change (premise.formulas.push (.par left right))[
            premise.formulas.size]? = some (.par left right)
          exact Array.getElem?_push_size
        rw [formulaEquation]
        exact producerCount_appendParOccurrence_new structural left right
          leftRoot rightRoot (remaining ++ [premise.formulas.size])
      · have freshBoundary : premise.formulas.size ∈
            (premise.appendParOccurrence left right leftRoot rightRoot
              (remaining ++ [premise.formulas.size])).conclusions := by
          simp [Certificate.appendParOccurrence]
        rw [if_pos freshBoundary]
        exact parentUseCount_appendParOccurrence_new structural left right
          leftRoot rightRoot leftRootInBounds rightRootInBounds
          (remaining ++ [premise.formulas.size])

/-- Disjoint tensor composition preserves the complete structural invariant.
The two permutation hypotheses identify the selected boundary occurrence in
each premise; the right block is shifted by the left formula-array size. -/
theorem StructurallyWellFormed.appendTensorOccurrence
    {leftPremise rightPremise : Certificate}
    (leftStructural : leftPremise.StructurallyWellFormed)
    (rightStructural : rightPremise.StructurallyWellFormed)
    (left right : Formula) {leftRoot rightRoot : Vertex}
    (leftLookup : leftPremise.formula? leftRoot = some left)
    (rightLookup : rightPremise.formula? rightRoot = some right)
    (leftRemaining rightRemaining : List Vertex)
    (leftBoundaryPermutation :
      leftPremise.conclusions.Perm (leftRoot :: leftRemaining))
    (rightBoundaryPermutation :
      rightPremise.conclusions.Perm (rightRoot :: rightRemaining)) :
    (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
      rightRoot
      ((leftPremise.formulas ++ rightPremise.formulas).size ::
        (leftRemaining ++ rightRemaining.map
          (fun vertex => vertex + leftPremise.formulas.size)))).StructurallyWellFormed := by
  let leftSize := leftPremise.formulas.size
  let rightSize := rightPremise.formulas.size
  let fresh := (leftPremise.formulas ++ rightPremise.formulas).size
  let shiftedRight := rightRemaining.map (fun vertex => vertex + leftSize)
  let boundary := fresh :: (leftRemaining ++ shiftedRight)
  have leftBoundaryNodup : leftPremise.conclusions.Nodup :=
    nodup_of_eraseDups_length_eq leftStructural.2.2.2.1
  have rightBoundaryNodup : rightPremise.conclusions.Nodup :=
    nodup_of_eraseDups_length_eq rightStructural.2.2.2.1
  have leftDecomposedNodup : (leftRoot :: leftRemaining).Nodup :=
    leftBoundaryPermutation.nodup_iff.mp leftBoundaryNodup
  have rightDecomposedNodup : (rightRoot :: rightRemaining).Nodup :=
    rightBoundaryPermutation.nodup_iff.mp rightBoundaryNodup
  have leftRootFresh : leftRoot ∉ leftRemaining :=
    (List.nodup_cons.mp leftDecomposedNodup).1
  have rightRootFresh : rightRoot ∉ rightRemaining :=
    (List.nodup_cons.mp rightDecomposedNodup).1
  have leftRemainingNodup : leftRemaining.Nodup :=
    (List.nodup_cons.mp leftDecomposedNodup).2
  have rightRemainingNodup : rightRemaining.Nodup :=
    (List.nodup_cons.mp rightDecomposedNodup).2
  have leftBoundary : leftRoot ∈ leftPremise.conclusions :=
    leftBoundaryPermutation.mem_iff.mpr (by simp)
  have rightBoundary : rightRoot ∈ rightPremise.conclusions :=
    rightBoundaryPermutation.mem_iff.mpr (by simp)
  have leftRootInBounds : leftRoot < leftSize := by
    exact leftStructural.2.2.1 leftRoot leftBoundary
  have rightRootInBounds : rightRoot < rightSize := by
    exact rightStructural.2.2.1 rightRoot rightBoundary
  have leftRemainingInBounds : ∀ vertex ∈ leftRemaining,
      vertex < leftSize := by
    intro vertex membership
    exact leftStructural.2.2.1 vertex
      (leftBoundaryPermutation.mem_iff.mpr (by simp [membership]))
  have rightRemainingInBounds : ∀ vertex ∈ rightRemaining,
      vertex < rightSize := by
    intro vertex membership
    exact rightStructural.2.2.1 vertex
      (rightBoundaryPermutation.mem_iff.mpr (by simp [membership]))
  have shiftedRightNodup : shiftedRight.Nodup := by
    exact rightRemainingNodup.map
      (fun vertex => vertex + leftSize)
      (fun _ _ different equality =>
        different (Nat.add_right_cancel equality))
  have tailNodup : (leftRemaining ++ shiftedRight).Nodup := by
    rw [List.nodup_append]
    refine ⟨leftRemainingNodup, shiftedRightNodup, ?_⟩
    intro leftVertex leftMembership shiftedVertex shiftedMembership
    rcases List.mem_map.mp shiftedMembership with
      ⟨rightVertex, rightMembership, rfl⟩
    have leftBound := leftRemainingInBounds leftVertex leftMembership
    have rightAtOrAbove : leftSize ≤ rightVertex + leftSize :=
      Nat.le_add_left leftSize rightVertex
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le leftBound rightAtOrAbove)
  have freshNotTail : fresh ∉ leftRemaining ++ shiftedRight := by
    intro membership
    rw [List.mem_append] at membership
    rcases membership with leftMembership | shiftedMembership
    · have leftBound := leftRemainingInBounds fresh leftMembership
      have leftSizeAtMostFresh : leftSize ≤ fresh := by
        simp [leftSize, fresh]
      exact (Nat.not_lt_of_ge leftSizeAtMostFresh) leftBound
    · rcases List.mem_map.mp shiftedMembership with
        ⟨rightVertex, rightMembership, equality⟩
      have rightBound := rightRemainingInBounds rightVertex rightMembership
      have shiftedBeforeFresh : rightVertex + leftSize < fresh := by
        simpa [leftSize, rightSize, fresh, Nat.add_comm] using
          Nat.add_lt_add_right rightBound leftSize
      exact (Nat.ne_of_lt shiftedBeforeFresh) equality
  have boundaryNodup : boundary.Nodup := by
    exact List.nodup_cons.mpr ⟨freshNotTail, tailNodup⟩
  change (leftPremise.appendTensorOccurrence rightPremise left right leftRoot
    rightRoot boundary).StructurallyWellFormed
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [appendTensorOccurrence_formulas_size]
    omega
  · change 0 < boundary.length
    simp [boundary]
  · intro vertex membership
    change vertex ∈ boundary at membership
    simp only [boundary, shiftedRight, List.mem_cons, List.mem_append,
      List.mem_map] at membership
    rcases membership with isFresh | leftMembership | shiftedMembership
    · subst vertex
      simp [fresh]
    · exact appendTensorOccurrence_left_bound leftPremise rightPremise left
        right leftRoot rightRoot boundary
        (leftRemainingInBounds vertex leftMembership)
    · rcases shiftedMembership with ⟨source, sourceMembership, rfl⟩
      exact appendTensorOccurrence_right_bound leftPremise rightPremise left
        right leftRoot rightRoot boundary
        (rightRemainingInBounds source sourceMembership)
  · change boundary.eraseDups.length = boundary.length
    rw [eraseDups_eq_self_of_nodup boundaryNodup]
  · intro link membership
    change link ∈ leftPremise.links ++
      rightPremise.links.map (Link.shift leftSize) ++
      [Link.tensor leftRoot (rightRoot + leftSize) fresh] at membership
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at membership
    rcases membership with (leftMembership | rightMembership) | terminal
    · exact LinkWellFormed.appendTensorOccurrence_left
        (leftStructural.2.2.2.2.1 link leftMembership)
          left right leftRoot rightRoot boundary
    · rcases rightMembership with ⟨source, sourceMembership, rfl⟩
      exact LinkWellFormed.appendTensorOccurrence_right
        (rightStructural.2.2.2.2.1 source sourceMembership)
          left right leftRoot rightRoot boundary
    · subst link
      simpa [leftSize, fresh] using
        LinkWellFormed.appendTensorOccurrence_new left right
          leftRootInBounds rightRootInBounds leftLookup rightLookup boundary
  · intro vertex inBounds
    rw [appendTensorOccurrence_formulas_size] at inBounds
    by_cases inLeft : vertex < leftSize
    · have oldNode := leftStructural.2.2.2.2.2 vertex inLeft
      have formulaEquation := formula?_appendTensorOccurrence_left
        leftPremise rightPremise left right leftRoot rightRoot boundary inLeft
      unfold NodeWellFormed at oldNode ⊢
      rw [formulaEquation]
      constructor
      · cases oldFormula : leftPremise.formula? vertex with
        | none => simp [oldFormula] at oldNode
        | some formula =>
            cases formula with
            | atom name positive =>
                simpa [oldFormula,
                  axiomCount_appendTensorOccurrence_left leftPremise
                    rightPremise left right leftRoot rightRoot boundary inLeft]
                  using oldNode.1
            | tensor first second =>
                simpa [oldFormula,
                  producerCount_appendTensorOccurrence_left leftPremise
                    rightPremise left right leftRoot rightRoot boundary inLeft]
                  using oldNode.1
            | par first second =>
                simpa [oldFormula,
                  producerCount_appendTensorOccurrence_left leftPremise
                    rightPremise left right leftRoot rightRoot boundary inLeft]
                  using oldNode.1
      · by_cases selected : vertex = leftRoot
        · subst vertex
          have outputNotBoundary : leftRoot ∉
              (leftPremise.appendTensorOccurrence rightPremise left right
                leftRoot rightRoot boundary).conclusions := by
            change leftRoot ∉ boundary
            intro membership
            simp only [boundary, shiftedRight, List.mem_cons, List.mem_append,
              List.mem_map] at membership
            rcases membership with freshEquality | inRemaining | inShifted
            · have leftBeforeFresh : leftRoot < fresh := by
                exact Nat.lt_of_lt_of_le leftRootInBounds (by
                  simp [leftSize, fresh])
              exact (Nat.ne_of_lt leftBeforeFresh) freshEquality
            · exact leftRootFresh inRemaining
            · rcases inShifted with ⟨source, sourceMembership, equality⟩
              have leftBeforeShifted : leftRoot < source + leftSize :=
                Nat.lt_of_lt_of_le leftRootInBounds
                  (Nat.le_add_left leftSize source)
              exact (Nat.ne_of_gt leftBeforeShifted) equality
          rw [if_neg outputNotBoundary,
            parentUseCount_appendTensorOccurrence_left_selected leftPremise
              rightPremise left right leftRootInBounds]
          rw [if_pos leftBoundary] at oldNode
          omega
        · have boundaryIff : vertex ∈
                (leftPremise.appendTensorOccurrence rightPremise left right
                  leftRoot rightRoot boundary).conclusions ↔
              vertex ∈ leftPremise.conclusions := by
            change vertex ∈ boundary ↔ vertex ∈ leftPremise.conclusions
            constructor
            · intro membership
              simp only [boundary, shiftedRight, List.mem_cons, List.mem_append,
                List.mem_map] at membership
              rcases membership with freshEquality | inRemaining | inShifted
              · have vertexBeforeFresh : vertex < fresh := by
                  exact Nat.lt_of_lt_of_le inLeft (by simp [leftSize, fresh])
                exact False.elim ((Nat.ne_of_lt vertexBeforeFresh)
                  freshEquality)
              · exact leftBoundaryPermutation.mem_iff.mpr (by
                  simp [selected, inRemaining])
              · rcases inShifted with ⟨source, sourceMembership, equality⟩
                have vertexBeforeShifted : vertex < source + leftSize :=
                  Nat.lt_of_lt_of_le inLeft
                    (Nat.le_add_left leftSize source)
                exact False.elim ((Nat.ne_of_gt vertexBeforeShifted) equality)
            · intro membership
              have decomposed := leftBoundaryPermutation.mem_iff.mp membership
              have inRemaining : vertex ∈ leftRemaining := by
                simpa [selected] using decomposed
              simp [boundary, inRemaining]
          rw [parentUseCount_appendTensorOccurrence_left_other leftPremise
            rightPremise left right inLeft selected]
          by_cases oldBoundary : vertex ∈ leftPremise.conclusions
          · rw [if_pos (boundaryIff.mpr oldBoundary)]
            rw [if_pos oldBoundary] at oldNode
            exact oldNode.2
          · rw [if_neg (fun membership =>
              oldBoundary (boundaryIff.mp membership))]
            rw [if_neg oldBoundary] at oldNode
            exact oldNode.2
    · by_cases isFresh : vertex = fresh
      · subst vertex
        unfold NodeWellFormed
        constructor
        · have formulaAtFresh :
              (leftPremise.appendTensorOccurrence rightPremise left right
                leftRoot rightRoot boundary).formula? fresh =
                  some (.tensor left right) := by
            change ((leftPremise.formulas ++ rightPremise.formulas).push
              (.tensor left right))[fresh]? = some (.tensor left right)
            exact Array.getElem?_push_size
              (xs := leftPremise.formulas ++ rightPremise.formulas)
              (x := Formula.tensor left right)
          rw [formulaAtFresh]
          simpa [fresh] using producerCount_appendTensorOccurrence_new
            leftStructural rightStructural left right leftRoot rightRoot boundary
        · have freshBoundary : fresh ∈
              (leftPremise.appendTensorOccurrence rightPremise left right
                leftRoot rightRoot boundary).conclusions := by
            change fresh ∈ boundary
            simp [boundary]
          rw [if_pos freshBoundary]
          simpa [fresh] using parentUseCount_appendTensorOccurrence_new
            leftStructural rightStructural left right leftRootInBounds
              rightRootInBounds boundary
      · have middleLower : leftSize ≤ vertex := Nat.le_of_not_gt inLeft
        have freshValue : fresh = leftSize + rightSize := by
          simp [fresh, leftSize, rightSize]
        have middleUpper : vertex < leftSize + rightSize := by
          rw [freshValue] at isFresh
          omega
        have sourceExists : ∃ source, source < rightSize ∧
            vertex = source + leftSize := by
          refine ⟨vertex - leftSize, by omega, by omega⟩
        rcases sourceExists with ⟨source, sourceInBounds, rfl⟩
        have oldNode := rightStructural.2.2.2.2.2 source sourceInBounds
        have formulaEquation := formula?_appendTensorOccurrence_right
          leftPremise rightPremise left right leftRoot rightRoot boundary
            sourceInBounds
        unfold NodeWellFormed at oldNode ⊢
        rw [formulaEquation]
        constructor
        · cases oldFormula : rightPremise.formula? source with
          | none => simp [oldFormula] at oldNode
          | some formula =>
              cases formula with
              | atom name positive =>
                  simpa [oldFormula, leftSize,
                    axiomCount_appendTensorOccurrence_right leftStructural
                      left right leftRoot rightRoot boundary sourceInBounds]
                    using oldNode.1
              | tensor first second =>
                  simpa [oldFormula, leftSize,
                    producerCount_appendTensorOccurrence_right leftStructural
                      left right leftRoot rightRoot boundary sourceInBounds]
                    using oldNode.1
              | par first second =>
                  simpa [oldFormula, leftSize,
                    producerCount_appendTensorOccurrence_right leftStructural
                      left right leftRoot rightRoot boundary sourceInBounds]
                    using oldNode.1
        · by_cases selected : source = rightRoot
          · subst source
            have outputNotBoundary : rightRoot + leftSize ∉
                (leftPremise.appendTensorOccurrence rightPremise left right
                  leftRoot rightRoot boundary).conclusions := by
              change rightRoot + leftSize ∉ boundary
              intro membership
              simp only [boundary, shiftedRight, List.mem_cons, List.mem_append,
                List.mem_map] at membership
              rcases membership with freshEquality | inLeftRemaining |
                inShifted
              · have beforeFresh : rightRoot + leftSize < fresh := by
                  simpa [leftSize, rightSize, fresh, Nat.add_comm] using
                    Nat.add_lt_add_right rightRootInBounds leftSize
                exact (Nat.ne_of_lt beforeFresh) freshEquality
              · have leftBound :=
                  leftRemainingInBounds (rightRoot + leftSize) inLeftRemaining
                exact (Nat.not_lt_of_ge
                  (Nat.le_add_left leftSize rightRoot)) leftBound
              · rcases inShifted with ⟨source, sourceMembership, equality⟩
                have localEquality : rightRoot = source :=
                  (Nat.add_right_cancel equality).symm
                subst source
                exact rightRootFresh sourceMembership
            rw [if_neg outputNotBoundary,
              parentUseCount_appendTensorOccurrence_right_selected
                leftStructural left right leftRootInBounds]
            rw [if_pos rightBoundary] at oldNode
            omega
          · have boundaryIff : source + leftSize ∈
                  (leftPremise.appendTensorOccurrence rightPremise left right
                    leftRoot rightRoot boundary).conclusions ↔
                source ∈ rightPremise.conclusions := by
              change source + leftSize ∈ boundary ↔
                source ∈ rightPremise.conclusions
              constructor
              · intro membership
                simp only [boundary, shiftedRight, List.mem_cons,
                  List.mem_append,
                  List.mem_map] at membership
                rcases membership with freshEquality | inLeftRemaining |
                  inShifted
                · have beforeFresh : source + leftSize < fresh := by
                    simpa [leftSize, rightSize, fresh, Nat.add_comm] using
                      Nat.add_lt_add_right sourceInBounds leftSize
                  exact False.elim ((Nat.ne_of_lt beforeFresh) freshEquality)
                · have leftBound :=
                    leftRemainingInBounds (source + leftSize) inLeftRemaining
                  exact False.elim ((Nat.not_lt_of_ge
                    (Nat.le_add_left leftSize source)) leftBound)
                · rcases inShifted with
                    ⟨other, otherMembership, equality⟩
                  have same : source = other :=
                    (Nat.add_right_cancel equality).symm
                  subst other
                  exact rightBoundaryPermutation.mem_iff.mpr (by
                    simp [selected, otherMembership])
              · intro membership
                have decomposed :=
                  rightBoundaryPermutation.mem_iff.mp membership
                have inRemaining : source ∈ rightRemaining := by
                  simpa [selected] using decomposed
                simp [boundary, shiftedRight, inRemaining]
            rw [parentUseCount_appendTensorOccurrence_right_other
              leftStructural left right leftRootInBounds selected]
            by_cases oldBoundary : source ∈ rightPremise.conclusions
            · rw [if_pos (boundaryIff.mpr oldBoundary)]
              rw [if_pos oldBoundary] at oldNode
              exact oldNode.2
            · rw [if_neg (fun membership =>
                oldBoundary (boundaryIff.mp membership))]
              rw [if_neg oldBoundary] at oldNode
              exact oldNode.2

/-- Structural correctness is invariant under permutation of the ordered
conclusion interface. Formula/link ownership is unchanged, while boundary
membership and duplicate-freedom are transported by the permutation. -/
theorem StructurallyWellFormed.withConclusions
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (boundary : List Vertex)
    (permutation : certificate.conclusions.Perm boundary) :
    ({ certificate with conclusions := boundary } : Certificate).StructurallyWellFormed := by
  have sourceNodup : certificate.conclusions.Nodup :=
    nodup_of_eraseDups_length_eq structural.2.2.2.1
  have boundaryNodup : boundary.Nodup :=
    permutation.nodup_iff.mp sourceNodup
  refine ⟨structural.1, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [permutation.length_eq] using structural.2.1
  · intro vertex membership
    exact structural.2.2.1 vertex (permutation.mem_iff.mpr membership)
  · change boundary.eraseDups.length = boundary.length
    rw [eraseDups_eq_self_of_nodup boundaryNodup]
  · intro link membership
    exact structural.2.2.2.2.1 link membership
  · intro vertex inBounds
    have oldNode := structural.2.2.2.2.2 vertex inBounds
    unfold NodeWellFormed at oldNode ⊢
    constructor
    · exact oldNode.1
    · have boundaryIff : vertex ∈ boundary ↔
          vertex ∈ certificate.conclusions := by
        exact permutation.mem_iff.symm
      by_cases oldBoundary : vertex ∈ certificate.conclusions
      · rw [if_pos (boundaryIff.mpr oldBoundary)]
        rw [if_pos oldBoundary] at oldNode
        exact oldNode.2
      · rw [if_neg (fun membership =>
          oldBoundary (boundaryIff.mp membership))]
        rw [if_neg oldBoundary] at oldNode
        exact oldNode.2

end Certificate

end ProofNetIR
