import Lean.Elab.Tactic.Omega
import ProofNetIR.DerivationTree
import ProofNetIR.NetEquivalence

namespace ProofNetIR

/-- Evidence returned by the future general sequentializer. The result is
deliberately stronger than an `Option CutFreeDerivation`: it connects
first-order inference, desequentialization, ordered boundary labels, and the
semantic proof-net equivalence relation. -/
structure SequentializationResult (input : Certificate) where
  tree : CutFreeDerivation
  sequent : List Formula
  output : Certificate
  inferred : tree.infer? = some sequent
  desequentialized : tree.desequentialize? = some output
  outputLabels : output.conclusionFormulas? = some sequent
  equivalent : output.ProofNetEquivalent input

namespace SequentializationResult

/-- A sequentialization result always contains a kernel-typed object-logic
derivation; this does not trust the proof-net checker. -/
theorem kernelDerivation {input : Certificate}
    (result : SequentializationResult input) :
    Nonempty (Derivation result.sequent) :=
  result.tree.infer?_sound result.inferred

/-- Proof-net equivalence transports the ordered conclusion formulas from the
desequentialized output back to the input certificate. -/
theorem inputLabels {input : Certificate}
    (result : SequentializationResult input) :
    input.conclusionFormulas? = some result.sequent := by
  calc
    input.conclusionFormulas? = result.output.conclusionFormulas? :=
      result.equivalent.conclusionFormulas?_eq.symm
    _ = some result.sequent := result.outputLabels

/-- If the input was accepted, the reconstructed proof net is accepted as
well. This follows from proved equivalence invariance, not from rerunning and
assuming the checker. -/
theorem outputAccepted {input : Certificate}
    (result : SequentializationResult input)
    (accepted : input.check = true) :
    result.output.check = true := by
  rw [result.equivalent.check_eq]
  exact accepted

/-- Package a successful general sequentialization in the existing checked
derivation/certificate API. -/
def toElaboratedCertificate {input : Certificate}
    (result : SequentializationResult input)
    (accepted : input.check = true) :
    CutFreeDerivation.ElaboratedCertificate where
  sequent := result.sequent
  derivation := result.kernelDerivation
  certificate := result.output
  conclusionLabels := result.outputLabels
  accepted := result.outputAccepted accepted

end SequentializationResult

/-- The exact macro theorem still to be constructed by terminal-par peeling,
splitting-tensor decomposition, and well-founded recursion. Keeping it as a
named proposition prevents a search routine from being mistaken for the
mathematical theorem. -/
def GenerallySequentializable : Prop :=
  ∀ input : Certificate,
    input.check = true → Nonempty (SequentializationResult input)

namespace Certificate

/-- Total compaction map used once the deleted occurrence is known not to be
the input vertex. -/
def compactVertex (removed vertex : Nat) : Nat :=
  if vertex < removed then vertex else vertex - 1

/-- Order-preserving embedding from compacted names back into the original
vertex interval. -/
def expandVertex (removed vertex : Nat) : Nat :=
  if vertex < removed then vertex else vertex + 1

/-- Compact an old vertex name after deleting one formula occurrence. -/
def deleteVertex? (removed vertex : Vertex) : Option Vertex :=
  if vertex = removed then
    none
  else
    some (compactVertex removed vertex)

@[simp] theorem deleteVertex?_self (vertex : Vertex) :
    deleteVertex? vertex vertex = none := by
  simp [deleteVertex?]

theorem deleteVertex?_of_lt {removed vertex : Vertex}
    (before : vertex < removed) :
    deleteVertex? removed vertex = some vertex := by
  simp [deleteVertex?, compactVertex, Nat.ne_of_lt before, before]

theorem deleteVertex?_of_gt {removed vertex : Vertex}
    (after : removed < vertex) :
    deleteVertex? removed vertex = some (vertex - 1) := by
  simp [deleteVertex?, compactVertex, Nat.ne_of_gt after,
    Nat.not_lt.mpr (Nat.le_of_lt after)]

theorem deleteVertex?_eq_some_of_ne {removed vertex : Vertex}
    (different : vertex ≠ removed) :
    deleteVertex? removed vertex = some (compactVertex removed vertex) := by
  simp [deleteVertex?, different]

@[simp] theorem compactVertex_expandVertex (removed vertex : Nat) :
    compactVertex removed (expandVertex removed vertex) = vertex := by
  by_cases before : vertex < removed
  · simp [compactVertex, expandVertex, before]
  · have notBefore : ¬vertex + 1 < removed := by omega
    simp [compactVertex, expandVertex, before, notBefore]

theorem expandVertex_compactVertex_of_ne {removed vertex : Nat}
    (different : vertex ≠ removed) :
    expandVertex removed (compactVertex removed vertex) = vertex := by
  by_cases before : vertex < removed
  · simp [compactVertex, expandVertex, before]
  · have after : removed < vertex := by omega
    have compactNotBefore : ¬vertex - 1 < removed := by omega
    simp [compactVertex, expandVertex, before, compactNotBefore]
    omega

theorem compactVertex_lt {removed vertex bound : Nat}
    (removedInBounds : removed < bound) (vertexInBounds : vertex < bound)
    (different : vertex ≠ removed) :
    compactVertex removed vertex < bound - 1 := by
  by_cases before : vertex < removed
  · simp [compactVertex, before]
    omega
  · simp [compactVertex, before]
    omega

theorem expandVertex_lt {removed vertex bound : Nat}
    (removedInBounds : removed < bound)
    (vertexInBounds : vertex < bound - 1) :
    expandVertex removed vertex < bound := by
  by_cases before : vertex < removed
  · simp [expandVertex, before]
    omega
  · simp [expandVertex, before]
    omega

theorem expandVertex_ne (removed vertex : Nat) :
    expandVertex removed vertex ≠ removed := by
  by_cases before : vertex < removed
  · simp [expandVertex, before]
    omega
  · simp [expandVertex, before]
    omega

end Certificate

namespace Link

/-- Delete one formula occurrence and compact every remaining endpoint. A
link incident to the deleted occurrence is removed. -/
def deleteVertex? (removed : Vertex) : Link → Option Link
  | .axiom left right => do
      let left' ← Certificate.deleteVertex? removed left
      let right' ← Certificate.deleteVertex? removed right
      pure (.axiom left' right')
  | .tensor left right conclusion => do
      let left' ← Certificate.deleteVertex? removed left
      let right' ← Certificate.deleteVertex? removed right
      let conclusion' ← Certificate.deleteVertex? removed conclusion
      pure (.tensor left' right' conclusion')
  | .par left right conclusion => do
      let left' ← Certificate.deleteVertex? removed left
      let right' ← Certificate.deleteVertex? removed right
      let conclusion' ← Certificate.deleteVertex? removed conclusion
      pure (.par left' right' conclusion')

end Link

namespace Certificate

/-- A par link is terminal when its conclusion occurrence is on the ordered
public boundary. Such a link is the unary inverse-rule case of
sequentialization. -/
def TerminalPar (certificate : Certificate)
    (left right conclusion : Vertex) : Prop :=
  Link.par left right conclusion ∈ certificate.links ∧
    conclusion ∈ certificate.conclusions

/-- A tensor link is terminal when its conclusion occurrence is on the public
boundary. Sequentialization additionally needs the tensor to split the
remaining proof structure into two correct components. -/
def TerminalTensor (certificate : Certificate)
    (left right conclusion : Vertex) : Prop :=
  Link.tensor left right conclusion ∈ certificate.links ∧
    conclusion ∈ certificate.conclusions

/-- Executable list of terminal par links. It is only a candidate finder; the
subnet construction and preservation theorem remain proof obligations. -/
def terminalPars (certificate : Certificate) :
    List (Vertex × Vertex × Vertex) :=
  certificate.links.filterMap fun
    | .par left right conclusion =>
        if conclusion ∈ certificate.conclusions then
          some (left, right, conclusion)
        else
          none
    | _ => none

/-- Candidate inverse of a terminal par rule. The produced premise removes the
par conclusion occurrence and its incident link, compacts all vertex names,
and puts the two premises at the tail of the ordered boundary. This function
does not itself assert preservation; `peelTerminalParChecked?` supplies the
safe executable boundary and the general preservation theorem is the next
formal obligation. -/
def peelTerminalParCandidate? (certificate : Certificate)
    (left right conclusion : Vertex) : Option Certificate := do
  if !certificate.links.contains (.par left right conclusion) then none
  if !certificate.conclusions.contains conclusion then none
  let left' ← deleteVertex? conclusion left
  let right' ← deleteVertex? conclusion right
  let context ← (certificate.conclusions.erase conclusion).mapM
    (deleteVertex? conclusion)
  pure {
    formulas := certificate.formulas.eraseIdxIfInBounds conclusion
    links := certificate.links.filterMap (Link.deleteVertex? conclusion)
    conclusions := context ++ [left', right'] }

/-- Checker-gated terminal-par premise. Even before the general preservation
theorem is complete, callers cannot accidentally treat a malformed candidate
as a proof net. -/
def peelTerminalParChecked? (certificate : Certificate)
    (left right conclusion : Vertex) :
    Option CutFreeDerivation.CheckedCertificate := do
  let premise ← certificate.peelTerminalParCandidate? left right conclusion
  if accepted : premise.check = true then
    some ⟨premise, accepted⟩
  else
    none

theorem mem_terminalPars_iff (certificate : Certificate)
    (left right conclusion : Vertex) :
    (left, right, conclusion) ∈ certificate.terminalPars ↔
      certificate.TerminalPar left right conclusion := by
  constructor
  · intro membership
    simp only [terminalPars, List.mem_filterMap] at membership
    rcases membership with ⟨link, linkMembership, emitted⟩
    cases link with
    | «axiom» first second => simp at emitted
    | tensor first second result => simp at emitted
    | par first second result =>
        by_cases boundary : result ∈ certificate.conclusions
        · simp [boundary] at emitted
          rcases emitted with ⟨rfl, rfl, rfl⟩
          exact ⟨linkMembership, boundary⟩
        · simp [boundary] at emitted
  · rintro ⟨linkMembership, boundary⟩
    simp only [terminalPars, List.mem_filterMap]
    exact ⟨.par left right conclusion, linkMembership, by simp [boundary]⟩

end Certificate

end ProofNetIR
