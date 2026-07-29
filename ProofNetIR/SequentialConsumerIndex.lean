import ProofNetIR.UnificationSemantics

namespace ProofNetIR

/-- A single premise-to-submitted-link index shared by the worklist engine and
the sequential Figure-7 bridge.  Each bucket stores submitted link indices
whose connective uses the addressed formula occurrence as a premise. -/
abbrev ConsumerIndex := Array (List Nat)

namespace ConsumerIndex

private def push (consumers : ConsumerIndex)
    (vertex linkIndex : Nat) : ConsumerIndex :=
  match consumers[vertex]? with
  | none => consumers
  | some indices =>
      consumers.setIfInBounds vertex (linkIndex :: indices)

@[simp] private theorem push_size
    (consumers : ConsumerIndex) (vertex linkIndex : Nat) :
    (push consumers vertex linkIndex).size = consumers.size := by
  unfold push
  split <;> simp

private def addLink (consumers : ConsumerIndex)
    (entry : Link × Nat) : ConsumerIndex :=
  match entry with
  | (.axiom _ _, _) => consumers
  | (.par left right _, linkIndex)
  | (.tensor left right _, linkIndex) =>
      let withLeft := push consumers left linkIndex
      push withLeft right linkIndex

@[simp] private theorem addLink_size
    (consumers : ConsumerIndex) (entry : Link × Nat) :
    (addLink consumers entry).size = consumers.size := by
  rcases entry with ⟨link, linkIndex⟩
  cases link <;> simp [addLink]

private theorem fold_size (entries : List (Link × Nat))
    (consumers : ConsumerIndex) :
    (entries.foldl addLink consumers).size = consumers.size := by
  induction entries generalizing consumers with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.foldl_cons]
      rw [induction, addLink_size]

/-- Build the canonical premise-consumer table.

This is a pure builder, not a hidden cache. Callers proving a complexity bound
must thread the resulting table explicitly instead of assuming repeated calls
are constant-time. Out-of-range premises are ignored, so malformed input fails
closed. -/
def build (certificate : Certificate) : ConsumerIndex :=
  certificate.links.zipIdx.foldl addLink
    (Array.replicate certificate.formulas.size [])

/-- Total bucket projection. Out-of-range vertices have no consumers. -/
def bucket (index : ConsumerIndex) (vertex : Vertex) : List Nat :=
  (index[vertex]?).getD []

/-- The table carrier is exactly the formula-occurrence carrier. -/
@[simp] theorem build_size (certificate : Certificate) :
    (build certificate).size = certificate.formulas.size := by
  unfold build
  rw [fold_size]
  simp

private theorem mem_push_self
    {consumers : ConsumerIndex} {vertex linkIndex : Nat}
    (bound : vertex < consumers.size) :
    linkIndex ∈ (push consumers vertex linkIndex).bucket vertex := by
  simp [bucket, push, bound]

private theorem mem_push_of_mem
    {consumers : ConsumerIndex} {vertex linkIndex : Nat}
    {premise existingIndex : Nat}
    (membership : existingIndex ∈ consumers.bucket premise) :
    existingIndex ∈
      (push consumers vertex linkIndex).bucket premise := by
  by_cases vertexBound : vertex < consumers.size
  · by_cases same : vertex = premise
    · subst premise
      have oldMembership :
          existingIndex ∈ consumers[vertex] := by
        unfold bucket at membership
        rw [Array.getElem?_eq_getElem vertexBound] at membership
        simpa using membership
      simpa [bucket, push, vertexBound] using
        List.mem_cons_of_mem linkIndex oldMembership
    · simpa [bucket, push, vertexBound, same] using membership
  · have lookupNone : consumers[vertex]? = none :=
      Array.getElem?_eq_none (Nat.le_of_not_gt vertexBound)
    simpa [bucket, push, lookupNone] using membership

private theorem mem_push_origin
    {consumers : ConsumerIndex} {vertex linkIndex : Nat}
    {premise candidate : Nat}
    (membership :
      candidate ∈ (push consumers vertex linkIndex).bucket premise) :
    (candidate = linkIndex ∧ premise = vertex) ∨
      candidate ∈ consumers.bucket premise := by
  by_cases vertexBound : vertex < consumers.size
  · by_cases same : vertex = premise
    · subst premise
      have inserted :
          candidate = linkIndex ∨ candidate ∈ consumers[vertex] := by
        simpa [bucket, push, vertexBound] using membership
      rcases inserted with inserted | old
      · exact Or.inl ⟨inserted, rfl⟩
      · apply Or.inr
        unfold bucket
        rw [Array.getElem?_eq_getElem vertexBound]
        simpa using old
    · apply Or.inr
      simpa [bucket, push, vertexBound, same] using membership
  · have lookupNone : consumers[vertex]? = none :=
      Array.getElem?_eq_none (Nat.le_of_not_gt vertexBound)
    apply Or.inr
    simpa [bucket, push, lookupNone] using membership

private theorem mem_addLink_of_mem
    {consumers : ConsumerIndex} {entry : Link × Nat}
    {premise existingIndex : Nat}
    (membership : existingIndex ∈ consumers.bucket premise) :
    existingIndex ∈ (addLink consumers entry).bucket premise := by
  rcases entry with ⟨link, linkIndex⟩
  cases link with
  | «axiom» left right =>
      exact membership
  | «par» left right conclusion =>
      exact mem_push_of_mem (mem_push_of_mem membership)
  | «tensor» left right conclusion =>
      exact mem_push_of_mem (mem_push_of_mem membership)

private theorem mem_addLink_origin
    {consumers : ConsumerIndex} {link : Link} {linkIndex : Nat}
    {premise candidate : Nat}
    (membership :
      candidate ∈
        (addLink consumers (link, linkIndex)).bucket premise) :
    (candidate = linkIndex ∧ link.isConnective = true ∧
      premise ∈ link.premises) ∨
      candidate ∈ consumers.bucket premise := by
  cases link with
  | «axiom» left right =>
      exact Or.inr membership
  | «par» left right conclusion =>
      have rightOrigin := mem_push_origin membership
      rcases rightOrigin with rightInserted | beforeRight
      · exact Or.inl
          ⟨rightInserted.1, rfl, by
            simp [Link.premises, rightInserted.2]⟩
      · have leftOrigin := mem_push_origin beforeRight
        rcases leftOrigin with leftInserted | old
        · exact Or.inl
            ⟨leftInserted.1, rfl, by
              simp [Link.premises, leftInserted.2]⟩
        · exact Or.inr old
  | «tensor» left right conclusion =>
      have rightOrigin := mem_push_origin membership
      rcases rightOrigin with rightInserted | beforeRight
      · exact Or.inl
          ⟨rightInserted.1, rfl, by
            simp [Link.premises, rightInserted.2]⟩
      · have leftOrigin := mem_push_origin beforeRight
        rcases leftOrigin with leftInserted | old
        · exact Or.inl
            ⟨leftInserted.1, rfl, by
              simp [Link.premises, leftInserted.2]⟩
        · exact Or.inr old

private theorem mem_fold_of_mem
    (entries : List (Link × Nat))
    {consumers : ConsumerIndex} {premise existingIndex : Nat}
    (membership : existingIndex ∈ consumers.bucket premise) :
    existingIndex ∈
      (entries.foldl addLink consumers).bucket premise := by
  induction entries generalizing consumers with
  | nil =>
      exact membership
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction (mem_addLink_of_mem membership)

private theorem mem_fold_origin
    (entries : List (Link × Nat))
    {consumers : ConsumerIndex} {premise candidate : Nat}
    (membership :
      candidate ∈ (entries.foldl addLink consumers).bucket premise) :
    (∃ link linkIndex,
      (link, linkIndex) ∈ entries ∧
      candidate = linkIndex ∧
      link.isConnective = true ∧
      premise ∈ link.premises) ∨
      candidate ∈ consumers.bucket premise := by
  induction entries generalizing consumers with
  | nil =>
      exact Or.inr membership
  | cons head tail induction =>
      simp only [List.foldl_cons] at membership
      rcases induction membership with introduced | beforeTail
      · rcases introduced with
          ⟨link, linkIndex, entryMembership, candidateIndex,
            connective, premiseMembership⟩
        exact Or.inl
          ⟨link, linkIndex, by simp [entryMembership],
            candidateIndex, connective, premiseMembership⟩
      · rcases head with ⟨link, linkIndex⟩
        rcases mem_addLink_origin beforeTail with introduced | old
        · exact Or.inl
            ⟨link, linkIndex, by simp, introduced.1,
              introduced.2.1, introduced.2.2⟩
        · exact Or.inr old

private theorem mem_addLink_of_premise
    {consumers : ConsumerIndex} {link : Link} {linkIndex premise : Nat}
    (bound : premise < consumers.size)
    (premiseMembership : premise ∈ link.premises) :
    linkIndex ∈
      (addLink consumers (link, linkIndex)).bucket premise := by
  cases link with
  | «axiom» left right =>
      simp [Link.premises] at premiseMembership
  | «par» left right conclusion =>
      simp [Link.premises] at premiseMembership
      rcases premiseMembership with same | same
      · subst premise
        exact mem_push_of_mem (mem_push_self bound)
      · subst premise
        apply mem_push_self
        simpa using bound
  | «tensor» left right conclusion =>
      simp [Link.premises] at premiseMembership
      rcases premiseMembership with same | same
      · subst premise
        exact mem_push_of_mem (mem_push_self bound)
      · subst premise
        apply mem_push_self
        simpa using bound

private theorem mem_fold_of_entry
    (entries : List (Link × Nat)) (consumers : ConsumerIndex)
    {link : Link} {linkIndex premise : Nat}
    (entryMembership : (link, linkIndex) ∈ entries)
    (bound : premise < consumers.size)
    (premiseMembership : premise ∈ link.premises) :
    linkIndex ∈
      (entries.foldl addLink consumers).bucket premise := by
  induction entries generalizing consumers with
  | nil =>
      simp at entryMembership
  | cons head tail induction =>
      simp only [List.mem_cons] at entryMembership
      rcases entryMembership with same | inTail
      · subst head
        simp only [List.foldl_cons]
        apply mem_fold_of_mem
        exact mem_addLink_of_premise bound premiseMembership
      · simp only [List.foldl_cons]
        apply induction
        · exact inTail
        · simpa using bound

/-- Every stored entry has exact submitted-link and premise provenance. -/
def Sound (certificate : Certificate) (index : ConsumerIndex) : Prop :=
  index.size = certificate.formulas.size ∧
    ∀ {premise candidate : Nat},
      candidate ∈ index.bucket premise →
        ∃ link,
          certificate.links[candidate]? = some link ∧
          link.isConnective = true ∧
          premise ∈ link.premises

/-- Every submitted, in-bounds connective premise is represented. -/
def Complete (certificate : Certificate) (index : ConsumerIndex) : Prop :=
  ∀ {link : Link} {linkIndex premise : Nat},
    certificate.links[linkIndex]? = some link →
      premise < certificate.formulas.size →
      premise ∈ link.premises →
      linkIndex ∈ index.bucket premise

/-- Exact origin theorem for the shared built index. -/
theorem build_origin
    {certificate : Certificate} {premise candidate : Nat}
    (membership : candidate ∈ (build certificate).bucket premise) :
    ∃ link,
      certificate.links[candidate]? = some link ∧
      link.isConnective = true ∧
      premise ∈ link.premises := by
  rcases
      mem_fold_origin certificate.links.zipIdx membership with
    introduced | initial
  · rcases introduced with
      ⟨link, linkIndex, entryMembership, candidateIndex,
        connective, premiseMembership⟩
    subst candidate
    exact
      ⟨link,
        List.mk_mem_zipIdx_iff_getElem?.1 entryMembership,
        connective, premiseMembership⟩
  · by_cases premiseBound :
        premise < certificate.formulas.size
    · have initialLookup :
          (Array.replicate certificate.formulas.size
          ([] : List Nat))[premise]? = some [] := by
        simp [premiseBound]
      simp [bucket, initialLookup] at initial
    · have initialLookup :
          (Array.replicate certificate.formulas.size
          ([] : List Nat))[premise]? = none :=
        Array.getElem?_eq_none (by
          simpa using Nat.le_of_not_gt premiseBound)
      simp [bucket, initialLookup] at initial

/-- Exact no-missed-dependency theorem for the shared built index. -/
theorem build_complete
    {certificate : Certificate} {link : Link}
    {linkIndex premise : Nat}
    (lookup : certificate.links[linkIndex]? = some link)
    (bound : premise < certificate.formulas.size)
    (premiseMembership : premise ∈ link.premises) :
    linkIndex ∈ (build certificate).bucket premise := by
  apply mem_fold_of_entry
  · exact List.mk_mem_zipIdx_iff_getElem?.2 lookup
  · simpa using bound
  · exact premiseMembership

/-- The shared index satisfies exact carrier and origin soundness. -/
theorem build_sound (certificate : Certificate) :
    Sound certificate (build certificate) := by
  constructor
  · exact build_size certificate
  · exact fun membership => build_origin membership

/-- The shared index is complete for every in-bounds connective premise. -/
theorem build_isComplete (certificate : Certificate) :
    Complete certificate (build certificate) :=
  fun lookup bound premiseMembership =>
    build_complete lookup bound premiseMembership

/-- Soundness exposes exact origin without depending on the builder. -/
theorem Sound.origin
    {certificate : Certificate} {index : ConsumerIndex}
    (sound : index.Sound certificate)
    {premise candidate : Nat}
    (membership : candidate ∈ index.bucket premise) :
    ∃ link,
      certificate.links[candidate]? = some link ∧
      link.isConnective = true ∧
      premise ∈ link.premises :=
  sound.2 membership

/-- Structural linear ownership makes all consumer indices in a bucket equal.
This is set-level singleton uniqueness; no list-order claim is needed. -/
theorem build_members_eq
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {premise first second : Nat}
    (firstMembership :
      first ∈ (build certificate).bucket premise)
    (secondMembership :
      second ∈ (build certificate).bucket premise) :
    first = second := by
  rcases build_origin firstMembership with
    ⟨firstLink, firstLookup, _firstConnective, firstPremise⟩
  rcases build_origin secondMembership with
    ⟨secondLink, secondLookup, _secondConnective, secondPremise⟩
  have firstBound :
      first < certificate.links.length :=
    (List.getElem?_eq_some_iff.mp firstLookup).1
  have secondBound :
      second < certificate.links.length :=
    (List.getElem?_eq_some_iff.mp secondLookup).1
  have firstLinkMembership :
      firstLink ∈ certificate.links := by
    have membership := List.getElem_mem firstBound
    simpa [(List.getElem?_eq_some_iff.mp firstLookup).2] using membership
  have secondLinkMembership :
      secondLink ∈ certificate.links := by
    have membership := List.getElem_mem secondBound
    simpa [(List.getElem?_eq_some_iff.mp secondLookup).2] using membership
  have sameLink : firstLink = secondLink := by
    have firstWellFormed :=
      structural.2.2.2.2.1 firstLink firstLinkMembership
    have premiseBound : premise < certificate.formulas.size := by
      cases firstLink with
      | «axiom» left right =>
          simp [Link.premises] at firstPremise
      | tensor left right conclusion =>
          rcases firstWellFormed with
            ⟨_, _, _, leftBound, rightBound, _, _⟩
          simp [Link.premises] at firstPremise
          rcases firstPremise with rfl | rfl
          · exact leftBound
          · exact rightBound
      | «par» left right conclusion =>
          rcases firstWellFormed with
            ⟨_, _, _, leftBound, rightBound, _, _⟩
          simp [Link.premises] at firstPremise
          rcases firstPremise with rfl | rfl
          · exact leftBound
          · exact rightBound
    have firstUses : firstLink.usesAsPremise premise = true := by
      simpa [Link.usesAsPremise] using firstPremise
    have secondUses : secondLink.usesAsPremise premise = true := by
      simpa [Link.usesAsPremise] using secondPremise
    have node := structural.2.2.2.2.2 premise premiseBound
    have notBoundary : premise ∉ certificate.conclusions := by
      intro boundary
      have parentZero : certificate.parentUseCount premise = 0 := by
        simpa [boundary] using node.2
      have filtered :
          firstLink ∈ certificate.links.filter
            (·.usesAsPremise premise) := by
        simp [firstLinkMembership, firstUses]
      have positive := List.length_pos_of_mem filtered
      unfold Certificate.parentUseCount at parentZero
      omega
    have parentCount : certificate.parentUseCount premise = 1 := by
      simpa [notBoundary] using node.2
    unfold Certificate.parentUseCount at parentCount
    have firstFiltered :
        firstLink ∈ certificate.links.filter
          (·.usesAsPremise premise) := by
      simp [firstLinkMembership, firstUses]
    have secondFiltered :
        secondLink ∈ certificate.links.filter
          (·.usesAsPremise premise) := by
      simp [secondLinkMembership, secondUses]
    rcases List.length_eq_one_iff.mp parentCount with
      ⟨only, filterEquation⟩
    rw [filterEquation] at firstFiltered secondFiltered
    simp at firstFiltered secondFiltered
    exact firstFiltered.trans secondFiltered.symm
  apply
    (List.getElem?_inj firstBound structural.links_nodup).mp
  rw [firstLookup, secondLookup, sameLink]

/-- A concrete in-bounds premise has a set-level singleton consumer bucket in
every structurally well-formed certificate. -/
theorem build_singleton
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {link : Link} {linkIndex premise : Nat}
    (lookup : certificate.links[linkIndex]? = some link)
    (bound : premise < certificate.formulas.size)
    (premiseMembership : premise ∈ link.premises) :
    linkIndex ∈ (build certificate).bucket premise ∧
      ∀ {candidate},
        candidate ∈ (build certificate).bucket premise →
          candidate = linkIndex := by
  have membership :=
    build_complete lookup bound premiseMembership
  exact ⟨membership, fun candidateMembership =>
    build_members_eq structural candidateMembership membership⟩

/-- Return the unique semantic consumer of one occurrence. Repeated copies of
the same index are harmless, while two distinct candidates fail closed. -/
def uniqueConsumer? (index : ConsumerIndex) (vertex : Vertex) :
    Option Nat :=
  match index.bucket vertex with
  | [] => none
  | first :: rest =>
      if rest.all (· == first) then some first else none

/-- Exact semantic-singleton characterization of `uniqueConsumer?`. -/
theorem uniqueConsumer?_eq_some_iff
    {index : ConsumerIndex} {vertex candidate : Nat} :
    index.uniqueConsumer? vertex = some candidate ↔
      candidate ∈ index.bucket vertex ∧
        ∀ {other}, other ∈ index.bucket vertex → other = candidate := by
  cases bucketEquation : index.bucket vertex with
  | nil =>
      simp [uniqueConsumer?, bucketEquation]
  | cons first rest =>
      by_cases allSame : rest.all (· == first)
      · have restSame :
          ∀ other ∈ rest, other = first := by
          intro other membership
          have accepted :
              (other == first) = true :=
            (List.all_eq_true.mp allSame) other membership
          exact beq_iff_eq.mp accepted
        constructor
        · intro equation
          simp [uniqueConsumer?, bucketEquation, allSame] at equation
          subst candidate
          constructor
          · simp
          · intro other membership
            simp at membership
            rcases membership with rfl | inRest
            · rfl
            · exact restSame other inRest
        · intro singleton
          have candidateEq : candidate = first := by
            exact (singleton.2 (by simp)).symm
          subst candidate
          simp [uniqueConsumer?, bucketEquation, allSame]
      · constructor
        · simp [uniqueConsumer?, bucketEquation, allSame]
        · intro singleton
          have everySame :
              ∀ other ∈ rest, other = first := by
            intro other membership
            have otherCandidate :
                other = candidate :=
              singleton.2 (by simp [membership])
            have firstCandidate :
                first = candidate :=
              singleton.2 (by simp)
            exact otherCandidate.trans firstCandidate.symm
          have allTrue : rest.all (· == first) = true := by
            apply List.all_eq_true.mpr
            intro other membership
            exact beq_iff_eq.mpr (everySame other membership)
          exact (allSame allTrue).elim

/-- On structurally well-formed input, every concrete in-bounds premise makes
the shared index's unique-consumer query succeed at its submitted index. -/
theorem build_uniqueConsumer?_eq_some
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {link : Link} {linkIndex premise : Nat}
    (lookup : certificate.links[linkIndex]? = some link)
    (bound : premise < certificate.formulas.size)
    (premiseMembership : premise ∈ link.premises) :
    (build certificate).uniqueConsumer? premise = some linkIndex := by
  rw [uniqueConsumer?_eq_some_iff]
  exact build_singleton structural lookup bound premiseMembership

end ConsumerIndex

/-- Stored orientation of the queried occurrence within a tensor link. -/
inductive TensorPremiseSide where
  | storedLeft
  | storedRight
  deriving Repr, DecidableEq, BEq

namespace TensorPremiseSide

/-- The premise selected by this stored orientation. -/
def premise : TensorPremiseSide → Vertex → Vertex → Vertex
  | .storedLeft, left, _right => left
  | .storedRight, _left, right => right

/-- The other tensor premise selected by this stored orientation. -/
def mate : TensorPremiseSide → Vertex → Vertex → Vertex
  | .storedLeft, _left, right => right
  | .storedRight, left, _right => left

end TensorPremiseSide

/-- Exact orientation-aware view of the tensor immediately consuming one
formula occurrence. This is a lookup result, not a complete Figure-7 `new`
transition. -/
structure TensorBelow where
  linkIndex : Nat
  storedLeft : Vertex
  storedRight : Vertex
  conclusion : Vertex
  side : TensorPremiseSide
  deriving Repr, DecidableEq, BEq

namespace TensorBelow

/-- Stored premise addressed by the view. -/
def premise (result : TensorBelow) : Vertex :=
  result.side.premise result.storedLeft result.storedRight

/-- Opposite tensor premise addressed by the view. -/
def mate (result : TensorBelow) : Vertex :=
  result.side.mate result.storedLeft result.storedRight

/-- Exact successful-result semantics for `tensorBelow?`. -/
def Valid (certificate : Certificate) (index : ConsumerIndex)
    (vertex : Vertex) (result : TensorBelow) : Prop :=
  index.uniqueConsumer? vertex = some result.linkIndex ∧
    certificate.links[result.linkIndex]? =
      some (.tensor result.storedLeft result.storedRight result.conclusion) ∧
    certificate.LinkWellFormed
      (.tensor result.storedLeft result.storedRight result.conclusion) ∧
    vertex = result.premise

end TensorBelow

private def tensorBelowAt? (certificate : Certificate)
    (vertex : Vertex) (linkIndex : Nat) : Option TensorBelow :=
  match certificate.links[linkIndex]? with
  | some (.tensor left right conclusion) =>
      if _wellFormed :
          certificate.linkLocallyWellFormed
            (.tensor left right conclusion) = true then
        if _storedLeft : vertex = left then
          some {
            linkIndex
            storedLeft := left
            storedRight := right
            conclusion
            side := .storedLeft
          }
        else if _storedRight : vertex = right then
          some {
            linkIndex
            storedLeft := left
            storedRight := right
            conclusion
            side := .storedRight
          }
        else
          none
      else
        none
  | _ => none

/-- Low-level tensor-mate lookup relative to an explicitly supplied table.

The lookup rejects absent or nonunique entries *in that table*, axiom/par
entries, malformed tensor links, occurrences that are not the stored left or
right premise, and self-mates. It does not prove that an arbitrary supplied
table is the certificate's complete consumer index. Production scheduler code
must use `Certificate.tensorBelow?`, which fixes the table to
`certificate.consumerIndex`. -/
def tensorBelow? (certificate : Certificate) (index : ConsumerIndex)
    (vertex : Vertex) : Option TensorBelow :=
  match index.uniqueConsumer? vertex with
  | none => none
  | some linkIndex => tensorBelowAt? certificate vertex linkIndex

/-- Exact table-relative success characterization of the low-level query. -/
theorem tensorBelow?_eq_some_iff
    {certificate : Certificate} {index : ConsumerIndex}
    {vertex : Vertex} {result : TensorBelow} :
    tensorBelow? certificate index vertex = some result ↔
      result.Valid certificate index vertex := by
  rcases result with
    ⟨linkIndex, storedLeft, storedRight, conclusion, side⟩
  cases side with
  | storedLeft =>
      simp only [TensorBelow.Valid, TensorBelow.premise,
        TensorPremiseSide.premise]
      constructor
      · intro equation
        cases consumerEquation :
            index.uniqueConsumer? vertex with
        | none =>
            simp [tensorBelow?, consumerEquation] at equation
        | some candidate =>
            have equationAt :
                tensorBelowAt? certificate vertex candidate =
                  some {
                    linkIndex
                    storedLeft
                    storedRight
                    conclusion
                    side := .storedLeft
                  } := by
              simpa [tensorBelow?, consumerEquation] using equation
            cases linkEquation :
                certificate.links[candidate]? with
            | none =>
                simp [tensorBelowAt?, linkEquation] at equationAt
            | some link =>
                cases link with
                | «axiom» left right =>
                    simp [tensorBelowAt?, linkEquation] at equationAt
                | «par» left right produced =>
                    simp [tensorBelowAt?, linkEquation] at equationAt
                | tensor left right produced =>
                    unfold tensorBelowAt? at equationAt
                    rw [linkEquation] at equationAt
                    by_cases wellFormed :
                        certificate.linkLocallyWellFormed
                          (.tensor left right produced) = true
                    · by_cases leftMatch : vertex = left
                      · have optionEquality :
                            some ({
                              linkIndex := candidate
                              storedLeft := left
                              storedRight := right
                              conclusion := produced
                              side := .storedLeft
                            } : TensorBelow) =
                              some {
                                linkIndex
                                storedLeft
                                storedRight
                                conclusion
                                side := .storedLeft
                              } := by
                            simpa [wellFormed, leftMatch] using equationAt
                        have resultEquality :
                            ({
                              linkIndex := candidate
                              storedLeft := left
                              storedRight := right
                              conclusion := produced
                              side := .storedLeft
                            } : TensorBelow) =
                              {
                                linkIndex
                                storedLeft
                                storedRight
                                conclusion
                                side := .storedLeft
                              } := by
                            exact Option.some.inj optionEquality
                        have candidateEq :
                            candidate = linkIndex :=
                          congrArg TensorBelow.linkIndex resultEquality
                        have leftEq : left = storedLeft :=
                          congrArg TensorBelow.storedLeft resultEquality
                        have rightEq : right = storedRight :=
                          congrArg TensorBelow.storedRight resultEquality
                        have conclusionEq : produced = conclusion :=
                          congrArg TensorBelow.conclusion resultEquality
                        subst linkIndex
                        subst storedLeft
                        subst storedRight
                        subst conclusion
                        exact ⟨rfl, linkEquation,
                          (certificate.linkLocallyWellFormed_iff
                            (.tensor left right produced)).mp wellFormed,
                          leftMatch⟩
                      · simp [wellFormed, leftMatch] at equationAt
                    · simp [wellFormed] at equationAt
      · intro valid
        rcases valid with
          ⟨consumerEquation, linkEquation, wellFormed, input⟩
        have executableWellFormed :
            certificate.linkLocallyWellFormed
              (.tensor storedLeft storedRight conclusion) = true :=
          (certificate.linkLocallyWellFormed_iff
            (.tensor storedLeft storedRight conclusion)).mpr wellFormed
        unfold tensorBelow?
        rw [consumerEquation]
        change tensorBelowAt? certificate vertex linkIndex =
          some {
            linkIndex
            storedLeft
            storedRight
            conclusion
            side := .storedLeft
          }
        unfold tensorBelowAt?
        rw [linkEquation]
        simp [executableWellFormed, input]
  | storedRight =>
      simp only [TensorBelow.Valid, TensorBelow.premise,
        TensorPremiseSide.premise]
      constructor
      · intro equation
        cases consumerEquation :
            index.uniqueConsumer? vertex with
        | none =>
            simp [tensorBelow?, consumerEquation] at equation
        | some candidate =>
            have equationAt :
                tensorBelowAt? certificate vertex candidate =
                  some {
                    linkIndex
                    storedLeft
                    storedRight
                    conclusion
                    side := .storedRight
                  } := by
              simpa [tensorBelow?, consumerEquation] using equation
            cases linkEquation :
                certificate.links[candidate]? with
            | none =>
                simp [tensorBelowAt?, linkEquation] at equationAt
            | some link =>
                cases link with
                | «axiom» left right =>
                    simp [tensorBelowAt?, linkEquation] at equationAt
                | «par» left right produced =>
                    simp [tensorBelowAt?, linkEquation] at equationAt
                | tensor left right produced =>
                    unfold tensorBelowAt? at equationAt
                    rw [linkEquation] at equationAt
                    by_cases wellFormed :
                        certificate.linkLocallyWellFormed
                          (.tensor left right produced) = true
                    · by_cases leftMatch : vertex = left
                      · simp [wellFormed, leftMatch] at equationAt
                      · by_cases rightMatch : vertex = right
                        · have rightNeLeft : right ≠ left := by
                            intro same
                            exact leftMatch (rightMatch.trans same)
                          have optionEquality :
                              some ({
                                linkIndex := candidate
                                storedLeft := left
                                storedRight := right
                                conclusion := produced
                                side := .storedRight
                              } : TensorBelow) =
                                some {
                                  linkIndex
                                  storedLeft
                                  storedRight
                                  conclusion
                                  side := .storedRight
                                } := by
                              simpa [wellFormed, rightMatch,
                                rightNeLeft] using
                                equationAt
                          have resultEquality :
                              ({
                                linkIndex := candidate
                                storedLeft := left
                                storedRight := right
                                conclusion := produced
                                side := .storedRight
                              } : TensorBelow) =
                                {
                                  linkIndex
                                  storedLeft
                                  storedRight
                                  conclusion
                                  side := .storedRight
                                } := by
                              exact Option.some.inj optionEquality
                          have candidateEq :
                              candidate = linkIndex :=
                            congrArg TensorBelow.linkIndex resultEquality
                          have leftEq : left = storedLeft :=
                            congrArg TensorBelow.storedLeft resultEquality
                          have rightEq : right = storedRight :=
                            congrArg TensorBelow.storedRight resultEquality
                          have conclusionEq : produced = conclusion :=
                            congrArg TensorBelow.conclusion resultEquality
                          subst linkIndex
                          subst storedLeft
                          subst storedRight
                          subst conclusion
                          exact ⟨rfl, linkEquation,
                            (certificate.linkLocallyWellFormed_iff
                              (.tensor left right produced)).mp wellFormed,
                            rightMatch⟩
                        · simp [wellFormed, leftMatch, rightMatch] at equationAt
                    · simp [wellFormed] at equationAt
      · intro valid
        rcases valid with
          ⟨consumerEquation, linkEquation, wellFormed, input⟩
        have executableWellFormed :
            certificate.linkLocallyWellFormed
              (.tensor storedLeft storedRight conclusion) = true :=
          (certificate.linkLocallyWellFormed_iff
            (.tensor storedLeft storedRight conclusion)).mpr wellFormed
        have notLeft : vertex ≠ storedLeft := by
          intro same
          exact wellFormed.1 (same.symm.trans input)
        have rightNeLeft : storedRight ≠ storedLeft := by
          intro same
          exact notLeft (input.trans same)
        unfold tensorBelow?
        rw [consumerEquation]
        change tensorBelowAt? certificate vertex linkIndex =
          some {
            linkIndex
            storedLeft
            storedRight
            conclusion
            side := .storedRight
          }
        unfold tensorBelowAt?
        rw [linkEquation]
        simp [executableWellFormed, input, rightNeLeft]

/-- Successful lookup identifies the exact semantic-singleton consumer. -/
theorem tensorBelow?_consumer
    {certificate : Certificate} {index : ConsumerIndex}
    {vertex : Vertex} {result : TensorBelow}
    (equation :
      tensorBelow? certificate index vertex = some result) :
    index.uniqueConsumer? vertex = some result.linkIndex :=
  (tensorBelow?_eq_some_iff.mp equation).1

/-- Successful lookup identifies the exact submitted tensor slot. -/
theorem tensorBelow?_link
    {certificate : Certificate} {index : ConsumerIndex}
    {vertex : Vertex} {result : TensorBelow}
    (equation :
      tensorBelow? certificate index vertex = some result) :
    certificate.links[result.linkIndex]? =
      some (.tensor result.storedLeft result.storedRight
        result.conclusion) :=
  (tensorBelow?_eq_some_iff.mp equation).2.1

/-- Successful lookup exposes an independently well-formed tensor. -/
theorem tensorBelow?_wellFormed
    {certificate : Certificate} {index : ConsumerIndex}
    {vertex : Vertex} {result : TensorBelow}
    (equation :
      tensorBelow? certificate index vertex = some result) :
    certificate.LinkWellFormed
      (.tensor result.storedLeft result.storedRight
        result.conclusion) :=
  (tensorBelow?_eq_some_iff.mp equation).2.2.1

/-- Successful lookup preserves the stored left/right orientation exactly. -/
theorem tensorBelow?_premise
    {certificate : Certificate} {index : ConsumerIndex}
    {vertex : Vertex} {result : TensorBelow}
    (equation :
      tensorBelow? certificate index vertex = some result) :
    vertex = result.premise :=
  (tensorBelow?_eq_some_iff.mp equation).2.2.2

/-- A successful tensor-below view never returns its input as its mate. -/
theorem tensorBelow?_mate_ne
    {certificate : Certificate} {index : ConsumerIndex}
    {vertex : Vertex} {result : TensorBelow}
    (equation :
      tensorBelow? certificate index vertex = some result) :
    result.mate ≠ vertex := by
  have wellFormed := tensorBelow?_wellFormed equation
  have input := tensorBelow?_premise equation
  cases sideEquation : result.side with
  | storedLeft =>
      have different :
          result.storedLeft ≠ result.storedRight :=
        wellFormed.1
      simp [TensorBelow.mate, TensorPremiseSide.mate,
        TensorBelow.premise, TensorPremiseSide.premise,
        sideEquation] at input ⊢
      exact fun same => different (input.symm.trans same.symm)
  | storedRight =>
      have different :
          result.storedLeft ≠ result.storedRight :=
        wellFormed.1
      simp [TensorBelow.mate, TensorPremiseSide.mate,
        TensorBelow.premise, TensorPremiseSide.premise,
        sideEquation] at input ⊢
      exact fun same => different (same.trans input)

namespace Certificate

/-- Canonical pure projection of a certificate to its consumer index.

The definition deliberately carries no memoization claim. A future
whole-program linearity layer must store and thread this value rather than
recompute it at every scheduler step. -/
def consumerIndex (certificate : Certificate) : ConsumerIndex :=
  ConsumerIndex.build certificate

/-- Canonical fail-closed tensor-mate lookup.

Unlike the low-level table-relative query, this API fixes lookup to the
certificate's sound-and-complete built consumer index. It therefore cannot
accept a caller-supplied partial table that hides a second consumer. -/
def tensorBelow? (certificate : Certificate)
    (vertex : Vertex) : Option TensorBelow :=
  ProofNetIR.tensorBelow? certificate certificate.consumerIndex vertex

/-- Exact success characterization of the canonical tensor-below query. -/
theorem tensorBelow?_eq_some_iff
    {certificate : Certificate} {vertex : Vertex}
    {result : TensorBelow} :
    certificate.tensorBelow? vertex = some result ↔
      result.Valid certificate certificate.consumerIndex vertex :=
  ProofNetIR.tensorBelow?_eq_some_iff

/-- Canonical lookup identifies the exact built-index singleton consumer. -/
theorem tensorBelow?_consumer
    {certificate : Certificate} {vertex : Vertex}
    {result : TensorBelow}
    (equation : certificate.tensorBelow? vertex = some result) :
    certificate.consumerIndex.uniqueConsumer? vertex =
      some result.linkIndex :=
  ProofNetIR.tensorBelow?_consumer equation

/-- Canonical lookup identifies the exact submitted tensor slot. -/
theorem tensorBelow?_link
    {certificate : Certificate} {vertex : Vertex}
    {result : TensorBelow}
    (equation : certificate.tensorBelow? vertex = some result) :
    certificate.links[result.linkIndex]? =
      some (.tensor result.storedLeft result.storedRight
        result.conclusion) :=
  ProofNetIR.tensorBelow?_link equation

/-- Canonical lookup exposes an independently well-formed tensor. -/
theorem tensorBelow?_wellFormed
    {certificate : Certificate} {vertex : Vertex}
    {result : TensorBelow}
    (equation : certificate.tensorBelow? vertex = some result) :
    certificate.LinkWellFormed
      (.tensor result.storedLeft result.storedRight
        result.conclusion) :=
  ProofNetIR.tensorBelow?_wellFormed equation

/-- Canonical lookup preserves the stored left/right orientation exactly. -/
theorem tensorBelow?_premise
    {certificate : Certificate} {vertex : Vertex}
    {result : TensorBelow}
    (equation : certificate.tensorBelow? vertex = some result) :
    vertex = result.premise :=
  ProofNetIR.tensorBelow?_premise equation

/-- Canonical tensor-below lookup never returns its input as its mate. -/
theorem tensorBelow?_mate_ne
    {certificate : Certificate} {vertex : Vertex}
    {result : TensorBelow}
    (equation : certificate.tensorBelow? vertex = some result) :
    result.mate ≠ vertex :=
  ProofNetIR.tensorBelow?_mate_ne equation

/-- Compatibility projection for the existing worklist engine. This is an
alias of `consumerIndex`, not a second independently maintained table. -/
abbrev worklistConsumers (certificate : Certificate) : Array (List Nat) :=
  certificate.consumerIndex

/-- Every concrete in-bounds premise dependency is present in the shared
worklist-compatible consumer table. -/
theorem mem_worklistConsumers_of_premise
    {certificate : Certificate} {link : Link}
    {linkIndex premise : Nat}
    (lookup : certificate.links[linkIndex]? = some link)
    (bound : premise < certificate.formulas.size)
    (premiseMembership : premise ∈ link.premises) :
    linkIndex ∈
      ((certificate.worklistConsumers[premise]?).getD []) := by
  exact ConsumerIndex.build_complete lookup bound premiseMembership

/-- Every entry in a worklist-compatible bucket has exact submitted-link and
premise provenance. -/
theorem mem_worklistConsumers_origin
    {certificate : Certificate} {premise candidate : Nat}
    (membership :
      candidate ∈
        ((certificate.worklistConsumers[premise]?).getD [])) :
    ∃ link,
      certificate.links[candidate]? = some link ∧
      link.isConnective = true ∧
      premise ∈ link.premises :=
  ConsumerIndex.build_origin membership

/-- Every worklist-compatible dependency names a submitted connective rather
than an axiom or an out-of-range slot. -/
theorem mem_worklistConsumers_submitted_connective
    {certificate : Certificate} {premise candidate : Nat}
    (membership :
      candidate ∈
        ((certificate.worklistConsumers[premise]?).getD [])) :
    ∃ link,
      certificate.links[candidate]? = some link ∧
      link.isConnective = true := by
  rcases mem_worklistConsumers_origin membership with
    ⟨link, lookup, connective, _premiseMembership⟩
  exact ⟨link, lookup, connective⟩

/-- Structural linear ownership makes all indices in one worklist-compatible
consumer bucket equal. -/
theorem worklistConsumers_members_eq
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {premise first second : Nat}
    (firstMembership :
      first ∈
        ((certificate.worklistConsumers[premise]?).getD []))
    (secondMembership :
      second ∈
        ((certificate.worklistConsumers[premise]?).getD [])) :
    first = second :=
  ConsumerIndex.build_members_eq structural
    firstMembership secondMembership

end Certificate

end ProofNetIR
