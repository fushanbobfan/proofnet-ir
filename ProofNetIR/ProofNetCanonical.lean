import ProofNetIR.LocalIdentity
import ProofNetIR.StructuralCode
import Std

namespace ProofNetIR

namespace FinitePermutations

/-- Insert `value` at every position of a list, from left to right.  This is
the small executable kernel used by `allPermutations`; it deliberately keeps
duplicate outputs when the input contains duplicate values. -/
def insertEverywhere (value : α) : List α → List (List α)
  | [] => [[value]]
  | head :: tail =>
      (value :: head :: tail) ::
        (insertEverywhere value tail).map (head :: ·)

theorem perm_of_mem_insertEverywhere {value : α} {source output : List α}
    (member : output ∈ insertEverywhere value source) :
    output.Perm (value :: source) := by
  induction source generalizing output with
  | nil => simpa [insertEverywhere] using member
  | cons head tail ih =>
      simp only [insertEverywhere, List.mem_cons, List.mem_map] at member
      rcases member with same | ⟨inserted, insertedMember, rfl⟩
      · subst output
        exact .refl _
      · exact (ih insertedMember).cons head |>.trans
          (List.Perm.swap head value tail).symm

theorem mem_insertEverywhere_erase [BEq α] [LawfulBEq α]
    {value : α} {output : List α} (member : value ∈ output) :
    output ∈ insertEverywhere value (output.erase value) := by
  induction output with
  | nil => simp at member
  | cons head tail ih =>
      by_cases same : head = value
      · subst head
        cases tail <;> simp [insertEverywhere]
      · have tailMember : value ∈ tail := by
          simp only [List.mem_cons] at member
          rcases member with equal | tailMember
          · exact (same equal.symm).elim
          · exact tailMember
        simp [insertEverywhere, same, ih tailMember]

/-- Enumerate every list permutation.  Unlike a set-valued permutation API,
this definition is executable with no ordering assumption on the element
type. -/
def allPermutations : List α → List (List α)
  | [] => [[]]
  | head :: tail =>
      (allPermutations tail).flatMap (insertEverywhere head)

/-- `allPermutations` is exact: membership is equivalent to the independent
inductive `List.Perm` relation. -/
theorem mem_allPermutations_iff [BEq α] [LawfulBEq α]
    {source output : List α} :
    output ∈ allPermutations source ↔ output.Perm source := by
  induction source generalizing output with
  | nil => simp [allPermutations]
  | cons head tail ih =>
      constructor
      · intro member
        simp only [allPermutations, List.mem_flatMap] at member
        rcases member with ⟨rest, restMember, insertedMember⟩
        exact (perm_of_mem_insertEverywhere insertedMember).trans
          ((ih.mp restMember).cons head)
      · intro permutation
        have headMember : head ∈ output :=
          permutation.mem_iff.mpr (by simp)
        have restPermutation : output.erase head |>.Perm tail := by
          exact ((List.cons_perm_iff_perm_erase.mp permutation.symm).2).symm
        simp only [allPermutations, List.mem_flatMap]
        exact ⟨output.erase head, ih.mpr restPermutation,
          mem_insertEverywhere_erase headMember⟩

end FinitePermutations

namespace Certificate

/-- The finite family of all v0.3 reindex-normal representatives obtained by
permuting only link storage order.  Membership is the canonical object: list
order and duplicate enumeration paths are intentionally not part of its
meaning.

For structurally well-formed certificates, extensional equality of these
finite families is proved below to be equivalent to the public
`ProofNetEquivalent` relation.  Ordered conclusions, tensor/par premise order,
formula labels, and axiom endpoint orientation remain significant. -/
def proofNetCanonicalFamily (certificate : Certificate) : List Certificate :=
  (FinitePermutations.allPermutations certificate.links).map fun links =>
    ({ certificate with links := links } : Certificate).equivalenceCanonicalize

theorem mem_proofNetCanonicalFamily_iff
    {certificate candidate : Certificate} :
    candidate ∈ certificate.proofNetCanonicalFamily ↔
      ∃ links, links.Perm certificate.links ∧
        candidate =
          Certificate.equivalenceCanonicalize
            ({ certificate with links := links } : Certificate) := by
  simp only [proofNetCanonicalFamily, List.mem_map]
  constructor
  · rintro ⟨links, membership, rfl⟩
    exact ⟨links, FinitePermutations.mem_allPermutations_iff.mp membership,
      rfl⟩
  · rintro ⟨links, permutation, rfl⟩
    exact ⟨links, FinitePermutations.mem_allPermutations_iff.mpr permutation,
      rfl⟩

private theorem proofNetCanonicalFamily_mem_reindex_forward
    (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size)
    {candidate : Certificate}
    (member : candidate ∈ certificate.proofNetCanonicalFamily) :
    candidate ∈ (certificate.reindex r).proofNetCanonicalFamily := by
  rw [mem_proofNetCanonicalFamily_iff] at member ⊢
  rcases member with ⟨links, permutation, rfl⟩
  let reindexedLinks := links.map (Link.reindex r)
  refine ⟨reindexedLinks, ?_, ?_⟩
  · simpa [reindexedLinks] using permutation.map (Link.reindex r)
  · have updatedReindex :
        (({ certificate with links := links } : Certificate).reindex r) =
          ({ certificate.reindex r with links := reindexedLinks } :
            Certificate) := by
      apply Certificate.ext_fields
      · rfl
      · rfl
      · rfl
    rw [← updatedReindex]
    exact ({ certificate with links := links } : Certificate)
      |>.equivalenceCanonicalize_reindex r |>.symm

/-- Reindexing changes neither membership nor meaning of the finite canonical
family. -/
theorem proofNetCanonicalFamily_mem_reindex_iff
    (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size)
    (candidate : Certificate) :
    candidate ∈ (certificate.reindex r).proofNetCanonicalFamily ↔
      candidate ∈ certificate.proofNetCanonicalFamily := by
  constructor
  · intro member
    have returned := proofNetCanonicalFamily_mem_reindex_forward
      (certificate.reindex r) (certificate.inverseReindexing r) member
    rw [certificate.reindex_inverse r] at returned
    exact returned
  · exact proofNetCanonicalFamily_mem_reindex_forward certificate r

/-- Literal link-list permutations change neither membership nor meaning of
the finite canonical family. -/
private theorem proofNetCanonicalFamily_mem_linkPermutation_forward
    {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right)
    {candidate : Certificate}
    (member : candidate ∈ left.proofNetCanonicalFamily) :
    candidate ∈ right.proofNetCanonicalFamily := by
  rw [mem_proofNetCanonicalFamily_iff] at member ⊢
  rcases member with ⟨links, permutation, rfl⟩
  refine ⟨links, permutation.trans equivalent.links, ?_⟩
  have updated :
      ({ left with links := links } : Certificate) =
        ({ right with links := links } : Certificate) := by
    exact Certificate.ext_fields equivalent.formulas rfl
      equivalent.conclusions
  rw [updated]

theorem LinkPermutationEquivalent.proofNetCanonicalFamily_mem_iff
    {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right)
    (candidate : Certificate) :
    candidate ∈ left.proofNetCanonicalFamily ↔
      candidate ∈ right.proofNetCanonicalFamily :=
  ⟨proofNetCanonicalFamily_mem_linkPermutation_forward equivalent,
    proofNetCanonicalFamily_mem_linkPermutation_forward equivalent.symm⟩

/-- Every generated proof-net equivalence preserves the canonical family as
an extensional finite set. -/
theorem ProofNetEquivalent.proofNetCanonicalFamily_mem_iff
    {left right : Certificate} (equivalent : left.ProofNetEquivalent right)
    (candidate : Certificate) :
    candidate ∈ left.proofNetCanonicalFamily ↔
      candidate ∈ right.proofNetCanonicalFamily := by
  rcases equivalent.toDirect with ⟨r, linkPermutation⟩
  exact (proofNetCanonicalFamily_mem_reindex_iff left r candidate).symm.trans
    (linkPermutation.proofNetCanonicalFamily_mem_iff candidate)

/-- On the library's structurally well-formed domain, extensional equality of
the finite canonical families is a complete invariant for exactly
`ProofNetEquivalent`.

This is not arbitrary graph isomorphism: ordered conclusions, ordered
tensor/par premises, formula labels, and axiom endpoint orientation remain
part of the identity contract. -/
theorem proofNetEquivalent_iff_canonicalFamily
    {left right : Certificate}
    (leftStructural : left.StructurallyWellFormed)
    (rightStructural : right.StructurallyWellFormed) :
    left.ProofNetEquivalent right ↔
      ∀ candidate,
        candidate ∈ left.proofNetCanonicalFamily ↔
          candidate ∈ right.proofNetCanonicalFamily := by
  constructor
  · intro equivalent candidate
    exact equivalent.proofNetCanonicalFamily_mem_iff candidate
  · intro sameFamily
    have leftNormalMember :
        left.equivalenceCanonicalize ∈ left.proofNetCanonicalFamily := by
      rw [mem_proofNetCanonicalFamily_iff]
      exact ⟨left.links, .refl _, rfl⟩
    have rightMember := (sameFamily left.equivalenceCanonicalize).mp
      leftNormalMember
    rw [mem_proofNetCanonicalFamily_iff] at rightMember
    rcases rightMember with ⟨links, permutation, sameNormal⟩
    let reordered : Certificate := { right with links := links }
    have reorderedEquivalent : reordered.LinkPermutationEquivalent right :=
      ⟨rfl, permutation, rfl⟩
    have reorderedStructural : reordered.StructurallyWellFormed :=
      reorderedEquivalent.structurallyWellFormed_iff.mpr rightStructural
    have normalEquation :
        left.equivalenceCanonicalize =
          reordered.equivalenceCanonicalize := by
      simpa [reordered] using sameNormal
    have reindexEquivalent : left.ReindexEquivalent reordered :=
      (reindexEquivalent_iff_equivalenceCanonicalize_eq leftStructural
        reorderedStructural).mpr normalEquation
    exact reindexEquivalent.toProofNetEquivalent.trans
      reorderedEquivalent.toProofNetEquivalent

/-- Checker acceptance supplies the structural premises of the complete
canonical-family theorem automatically. -/
theorem proofNetEquivalent_iff_canonicalFamily_of_check
    {left right : Certificate}
    (leftAccepted : left.check = true) (rightAccepted : right.check = true) :
    left.ProofNetEquivalent right ↔
      ∀ candidate,
        candidate ∈ left.proofNetCanonicalFamily ↔
          candidate ∈ right.proofNetCanonicalFamily :=
  proofNetEquivalent_iff_canonicalFamily
    (left.check_sound_declarative leftAccepted).1
    (right.check_sound_declarative rightAccepted).1

/-- One shared normalized family member is already sufficient to establish
`ProofNetEquivalent`; extensional equality of the whole family is stronger
than the reverse proof needs. -/
theorem proofNetEquivalent_of_common_canonicalFamily_member
    {left right candidate : Certificate}
    (leftStructural : left.StructurallyWellFormed)
    (rightStructural : right.StructurallyWellFormed)
    (leftMember : candidate ∈ left.proofNetCanonicalFamily)
    (rightMember : candidate ∈ right.proofNetCanonicalFamily) :
    left.ProofNetEquivalent right := by
  rw [mem_proofNetCanonicalFamily_iff] at leftMember rightMember
  rcases leftMember with
    ⟨leftLinks, leftPermutation, leftEquation⟩
  rcases rightMember with
    ⟨rightLinks, rightPermutation, rightEquation⟩
  let leftReordered : Certificate := { left with links := leftLinks }
  let rightReordered : Certificate := { right with links := rightLinks }
  have leftReorderedToLeft :
      leftReordered.LinkPermutationEquivalent left :=
    ⟨rfl, leftPermutation, rfl⟩
  have rightReorderedToRight :
      rightReordered.LinkPermutationEquivalent right :=
    ⟨rfl, rightPermutation, rfl⟩
  have leftReorderedStructural :
      leftReordered.StructurallyWellFormed :=
    leftReorderedToLeft.structurallyWellFormed_iff.mpr leftStructural
  have rightReorderedStructural :
      rightReordered.StructurallyWellFormed :=
    rightReorderedToRight.structurallyWellFormed_iff.mpr rightStructural
  have leftCandidateEquation :
      candidate = leftReordered.equivalenceCanonicalize := by
    simpa [leftReordered] using leftEquation
  have rightCandidateEquation :
      candidate = rightReordered.equivalenceCanonicalize := by
    simpa [rightReordered] using rightEquation
  have leftReorderedToCandidate :
      leftReordered.ReindexEquivalent candidate := by
    rw [leftCandidateEquation]
    exact
      leftReorderedStructural.equivalenceCanonicalize_reindexEquivalent
  have rightReorderedToCandidate :
      rightReordered.ReindexEquivalent candidate := by
    rw [rightCandidateEquation]
    exact
      rightReorderedStructural.equivalenceCanonicalize_reindexEquivalent
  exact
    leftReorderedToLeft.symm.toProofNetEquivalent
      |>.trans leftReorderedToCandidate.toProofNetEquivalent
      |>.trans
        (rightReorderedToRight.symm.toProofNetEquivalent
          |>.trans rightReorderedToCandidate.toProofNetEquivalent).symm

/-!
## Compact invariant fingerprint

The complete canonical family above is finite but factorial.  The definitions
below collapse its v0.3 serialized members to their lexicographically least
string.  The resulting fingerprint is executable and is proved invariant
under `ProofNetEquivalent`.

Only the forward theorem is claimed here.  Until serializer injectivity (or an
equivalent checked decoder round trip) is proved, equal fingerprints are not a
public decision procedure for `ProofNetEquivalent`; callers needing an exact
decision must continue to use `CheckedCertificate.sameProofNet?`.
-/

private instance proofNetCanonicalStringMin : Min String := minOfLe

/-- The finite serialized image of `proofNetCanonicalFamily`.  Duplicates are
harmless because the fingerprint depends only on the least member. -/
def proofNetCanonicalStringCandidates
    (certificate : Certificate) : List String :=
  certificate.proofNetCanonicalFamily.map equivalenceCanonicalString

/-- A compact, executable fingerprint obtained by taking the lexicographically
least v0.3 string in the complete finite canonical family.

This is currently an invariant, not a complete decision key: use
`CheckedCertificate.sameProofNet?` for exact pairwise proof-net identity. -/
def proofNetCanonicalFingerprint?
    (certificate : Certificate) : Option String :=
  certificate.proofNetCanonicalStringCandidates.min?

private theorem minList_eq_of_mem_iff
    {α : Type} [Min α] [LE α] [Std.IsLinearOrder α]
    [Std.LawfulOrderMin α]
    (left right : List α)
    (sameMembers : ∀ value, value ∈ left ↔ value ∈ right) :
    left.min? = right.min? := by
  cases leftMinimum : left.min? with
  | none =>
      have leftNil : left = [] :=
        List.min?_eq_none_iff.mp leftMinimum
      subst left
      have rightNil : right = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro value rightMember
        have impossible : value ∈ ([] : List α) :=
          (sameMembers value).mpr rightMember
        simp at impossible
      simp [rightNil]
  | some value =>
      have leftSpec := List.min?_eq_some_iff.mp leftMinimum
      have rightMinimum : right.min? = some value := by
        apply List.min?_eq_some_iff.mpr
        refine ⟨(sameMembers value).mp leftSpec.1, ?_⟩
        intro candidate candidateMember
        exact leftSpec.2 candidate
          ((sameMembers candidate).mpr candidateMember)
      exact rightMinimum.symm

/-- Every certificate contributes at least its own reindex normal form to the
serialized candidate family. -/
theorem equivalenceCanonicalString_mem_proofNetCanonicalStringCandidates
    (certificate : Certificate) :
    certificate.equivalenceCanonicalize.equivalenceCanonicalString ∈
      certificate.proofNetCanonicalStringCandidates := by
  rw [proofNetCanonicalStringCandidates, List.mem_map]
  refine ⟨certificate.equivalenceCanonicalize, ?_, rfl⟩
  rw [mem_proofNetCanonicalFamily_iff]
  exact ⟨certificate.links, .refl _, rfl⟩

/-- The compact fingerprint is total, although it retains `Option` in its
executable type to expose the finite-minimum operation directly. -/
theorem proofNetCanonicalFingerprint?_exists
    (certificate : Certificate) :
    ∃ fingerprint,
      certificate.proofNetCanonicalFingerprint? = some fingerprint := by
  cases equation :
      certificate.proofNetCanonicalFingerprint? with
  | none =>
      have candidateNil :
          certificate.proofNetCanonicalStringCandidates = [] :=
        List.min?_eq_none_iff.mp equation
      have member :=
        certificate
          |>.equivalenceCanonicalString_mem_proofNetCanonicalStringCandidates
      rw [candidateNil] at member
      simp at member
  | some fingerprint =>
      exact ⟨fingerprint, rfl⟩

/-- Successful fingerprint selection returns an actual serialized member of
the complete finite canonical family. -/
theorem proofNetCanonicalFingerprint?_mem
    (certificate : Certificate) {fingerprint : String}
    (equation :
      certificate.proofNetCanonicalFingerprint? = some fingerprint) :
    fingerprint ∈ certificate.proofNetCanonicalStringCandidates :=
  List.min?_mem equation

/-- Generated proof-net equivalence preserves membership in the finite
serialized candidate set. -/
theorem ProofNetEquivalent.proofNetCanonicalStringCandidates_mem_iff
    {left right : Certificate}
    (equivalent : left.ProofNetEquivalent right)
    (value : String) :
    value ∈ left.proofNetCanonicalStringCandidates ↔
      value ∈ right.proofNetCanonicalStringCandidates := by
  simp only [proofNetCanonicalStringCandidates, List.mem_map]
  constructor
  · rintro ⟨candidate, membership, rfl⟩
    exact ⟨candidate,
      (equivalent.proofNetCanonicalFamily_mem_iff candidate).mp membership,
      rfl⟩
  · rintro ⟨candidate, membership, rfl⟩
    exact ⟨candidate,
      (equivalent.proofNetCanonicalFamily_mem_iff candidate).mpr membership,
      rfl⟩

/-- `ProofNetEquivalent` certificates have exactly the same compact
fingerprint.  No converse is claimed until the serialized encoding is proved
injective on canonical-family members. -/
theorem ProofNetEquivalent.proofNetCanonicalFingerprint?_eq
    {left right : Certificate}
    (equivalent : left.ProofNetEquivalent right) :
    left.proofNetCanonicalFingerprint? =
      right.proofNetCanonicalFingerprint? := by
  apply minList_eq_of_mem_iff
  exact equivalent.proofNetCanonicalStringCandidates_mem_iff

/-!
## Equality-reflecting structural canonical code

The JSON-string fingerprint above remains forward-only because the repository
does not assume an unproved `Json.compress` injectivity theorem.  The code below
instead minimizes the explicitly versioned, kernel-proved injective structural
token code from `StructuralCode.lean`.

This yields an exact typed key for `ProofNetEquivalent` on the structurally
well-formed domain.  It still enumerates the factorial canonical family and is
not yet a JSON wire contract.
-/

private instance proofNetStructuralCodeMin : Min (List String) := minOfLe

/-- Injective structural codes for every member of the complete finite
canonical family. -/
def proofNetCanonicalCodeCandidates
    (certificate : Certificate) : List (List String) :=
  certificate.proofNetCanonicalFamily.map structuralCode

/-- The lexicographically least injective structural code in the complete
canonical family.  Unlike `proofNetCanonicalFingerprint?`, this typed token
key has a reverse-completeness theorem below. -/
def proofNetCanonicalCode?
    (certificate : Certificate) : Option (List String) :=
  certificate.proofNetCanonicalCodeCandidates.min?

theorem structuralCode_mem_proofNetCanonicalCodeCandidates
    (certificate : Certificate) :
    certificate.equivalenceCanonicalize.structuralCode ∈
      certificate.proofNetCanonicalCodeCandidates := by
  rw [proofNetCanonicalCodeCandidates, List.mem_map]
  refine ⟨certificate.equivalenceCanonicalize, ?_, rfl⟩
  rw [mem_proofNetCanonicalFamily_iff]
  exact ⟨certificate.links, .refl _, rfl⟩

/-- The exact structural canonical code is total for every certificate. -/
theorem proofNetCanonicalCode?_exists
    (certificate : Certificate) :
    ∃ code, certificate.proofNetCanonicalCode? = some code := by
  cases equation : certificate.proofNetCanonicalCode? with
  | none =>
      have candidatesNil :
          certificate.proofNetCanonicalCodeCandidates = [] :=
        List.min?_eq_none_iff.mp equation
      have member :=
        certificate.structuralCode_mem_proofNetCanonicalCodeCandidates
      rw [candidatesNil] at member
      simp at member
  | some code =>
      exact ⟨code, rfl⟩

/-- A selected exact code comes from an actual canonical-family member. -/
theorem proofNetCanonicalCode?_mem
    (certificate : Certificate) {code : List String}
    (equation : certificate.proofNetCanonicalCode? = some code) :
    code ∈ certificate.proofNetCanonicalCodeCandidates :=
  List.min?_mem equation

theorem ProofNetEquivalent.proofNetCanonicalCodeCandidates_mem_iff
    {left right : Certificate}
    (equivalent : left.ProofNetEquivalent right)
    (code : List String) :
    code ∈ left.proofNetCanonicalCodeCandidates ↔
      code ∈ right.proofNetCanonicalCodeCandidates := by
  simp only [proofNetCanonicalCodeCandidates, List.mem_map]
  constructor
  · rintro ⟨candidate, membership, rfl⟩
    exact ⟨candidate,
      (equivalent.proofNetCanonicalFamily_mem_iff candidate).mp membership,
      rfl⟩
  · rintro ⟨candidate, membership, rfl⟩
    exact ⟨candidate,
      (equivalent.proofNetCanonicalFamily_mem_iff candidate).mpr membership,
      rfl⟩

/-- Generated proof-net equivalence preserves the exact structural canonical
code. -/
theorem ProofNetEquivalent.proofNetCanonicalCode?_eq
    {left right : Certificate}
    (equivalent : left.ProofNetEquivalent right) :
    left.proofNetCanonicalCode? = right.proofNetCanonicalCode? := by
  apply minList_eq_of_mem_iff
  exact equivalent.proofNetCanonicalCodeCandidates_mem_iff

/-- On structurally well-formed certificates, equality of the typed structural
canonical code is equivalent to exactly `ProofNetEquivalent`. -/
theorem proofNetEquivalent_iff_canonicalCode
    {left right : Certificate}
    (leftStructural : left.StructurallyWellFormed)
    (rightStructural : right.StructurallyWellFormed) :
    left.ProofNetEquivalent right ↔
      left.proofNetCanonicalCode? = right.proofNetCanonicalCode? := by
  constructor
  · exact fun equivalent => equivalent.proofNetCanonicalCode?_eq
  · intro sameCode
    rcases left.proofNetCanonicalCode?_exists with
      ⟨code, leftEquation⟩
    have rightEquation :
        right.proofNetCanonicalCode? = some code := by
      rw [← sameCode]
      exact leftEquation
    have leftCodeMember := left.proofNetCanonicalCode?_mem leftEquation
    have rightCodeMember := right.proofNetCanonicalCode?_mem rightEquation
    rw [proofNetCanonicalCodeCandidates, List.mem_map] at leftCodeMember
    rw [proofNetCanonicalCodeCandidates, List.mem_map] at rightCodeMember
    rcases leftCodeMember with
      ⟨leftCandidate, leftMember, leftCodeEquation⟩
    rcases rightCodeMember with
      ⟨rightCandidate, rightMember, rightCodeEquation⟩
    have candidatesEqual : leftCandidate = rightCandidate :=
      structuralCode_injective
        (leftCodeEquation.trans rightCodeEquation.symm)
    subst rightCandidate
    exact proofNetEquivalent_of_common_canonicalFamily_member
      leftStructural rightStructural leftMember rightMember

/-- Checker acceptance supplies the structural premises for the exact typed
canonical-code theorem. -/
theorem proofNetEquivalent_iff_canonicalCode_of_check
    {left right : Certificate}
    (leftAccepted : left.check = true)
    (rightAccepted : right.check = true) :
    left.ProofNetEquivalent right ↔
      left.proofNetCanonicalCode? = right.proofNetCanonicalCode? :=
  proofNetEquivalent_iff_canonicalCode
    (left.check_sound_declarative leftAccepted).1
    (right.check_sound_declarative rightAccepted).1

end Certificate

end ProofNetIR
