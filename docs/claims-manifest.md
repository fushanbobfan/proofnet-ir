# Claims manifest

What the library proves, the premises the proofs rest on, the executables the
theorems cover, the cost model, and the revision at which all of it was
checked. The [goal ledger](goal-ledger.md) holds the full statements and their
history; the [trust model](trust-model.md) holds the trust boundary in prose.

## Revision

- Every declaration named below is in release `v0.10.0` (`f0fd97f`). The
  toolchain is unchanged since then, and the only library change removed five
  lines from `ProofNetIR/LeanPropSchemaCorpus.lean`, so the statements are
  unchanged on `main`.
- The terminal theorems D1–D4 and D6 were closed between 2026-09-18 and
  2026-09-20, the last of them, D6, by the proof checkpoint `33ebfd5` (CI run
  35557157288).
- The library trust gate at `34cd793` (CI run 35899598850) checks every safe
  compiled declaration of the 191 library modules, 14,477 declarations, and
  admits no axiom beyond `propext`, `Classical.choice`, and `Quot.sound`.
  Unsafe runtime declarations and `example`s are outside it. The curated audit
  `ProofNetIRAxiomAudit.lean` records the exact axioms of 1,191 public
  theorems.

## Premises

- Logic: propositional multiplicative linear logic without units and without
  cut. A `Formula` is an atom (a `String` name and a polarity), a tensor, or a
  par; negation is De Morgan duality. There are no quantifiers, additives, or
  exponentials.
- A `Certificate` (`ProofNetIR/Certificate.lean`) is an array of formula
  occurrences, whose identity is the array position, a list of axiom, tensor,
  and par links over those positions, and an ordered list of conclusions.
- Correctness, `Certificate.DeclarativelyCorrect`, is structural
  well-formedness (local link legality and exact occurrence ownership) together
  with every switching graph being a tree.
- Equivalence, `Certificate.ProofNetEquivalent`, is a bounded vertex renaming
  followed by a permutation of the link list, preserving the ordered
  conclusions, connective premises, formula labels, and axiom orientation. It
  is not isomorphism of unlabeled graphs.
- Derivations are `CutFreeDerivation` trees with explicit exchange.

## Theorems

Files are under `ProofNetIR/`.

| Claim | Theorem (file) | Executable covered | Cost claimed |
| --- | --- | --- | --- |
| The reference checker decides correctness. | `Certificate.check_iff_declarativelyCorrect` (`Checker.lean`); structural form `Certificate.check_iff_structural_cuspAcyclic_allConnected` (`Sequentialization.lean`) | `Certificate.check`, which enumerates all 2^pars switchings | none |
| Every derivation desequentializes to an accepted certificate. | `CutFreeDerivation.desequentialize?_check` (`DesequentializationSoundness.lean`) | `CutFreeDerivation.desequentialize?` | none |
| Every accepted certificate sequentializes. | `Certificate.sequentialization_of_check` (`Sequentialization.lean`); `Certificate.sequentialize_complete` (`ExecutableSequentialization.lean`) | `Certificate.sequentialize` | none |
| Reconstruction search decides exactly what the checker accepts. | `Certificate.reconstructsDerivation_eq_check` (`ReconstructionChecker.lean`) | `Certificate.reconstructsDerivation` | none |
| The public decision is exact and has no fallback search (D1, D2). | `Certificate.unificationCheck_eq_check`, `Certificate.unificationCheck_eq_sequentialFastCheck` (`Figure7/Sequential.lean`) | `Certificate.unificationCheck` | next rows |
| Its scheduler makes progress and stops (D3, D4). | `SequentialFigure7.CanonicalTagHistory.dispatch_or_allMarked` (`Figure7/Closure.lean`); `SequentialFigure7.dispatch_stops` (`Figure7/Termination.lean`) | the dispatcher inside `unificationCheck` | at most `formulas.size` successful dispatcher calls |
| Its operation count is quadratic (D6). | `SequentialCost.decisionStats_total_le_of_structural`: at most `152 * (formulas.size + 1) * submittedSize` on structurally well-formed input; `SequentialCost.decisionStats_total_le`: at most `152 * inputSize^2` on any input (`Figure7/CostBound.lean`) | the counters `Certificate.sequentialDecisionWithStats` (`Figure7/Cost.lean`), whose outcome equals `unificationCheck` by `Certificate.sequentialDecisionWithStats_accepted` | the model below |
| Identity of accepted certificates is decided exactly. | `CutFreeDerivation.CheckedCertificate.sameProofNet?_eq_true_iff` (`ProofNetIdentity.lean`); `Certificate.proofNetEquivalent_iff_intrinsicCanonicalKey_eq_of_check` (`IntrinsicCanonicalKeyWire.lean`) | `CutFreeDerivation.CheckedCertificate.sameProofNet?`, `Certificate.intrinsicCanonicalKey` | none |

## Cost model of D6

The counters are an explicit model computed alongside the run; the
conventions head `Figure7/Cost.lean`. A list traversal is charged its length,
an array access or constant-work primitive one, an index rebuild
`formulas.size + links.length` on every use, a bounded search its fuel plus
one, and a representative walk the parent-array size. A formula is measured in
symbols, two per connective and one per atom. An atom name counts as one
symbol, so comparing two names costs one whatever their length, as it would
with interned names; no theorem charges name bytes. Scans that may stop early
are charged as if they ran to the end. `submittedSize` is
`formulas.size + links.length + conclusions.length + 1`, and `inputSize` adds
the formulas' symbols.

The model is not CPU time, memory, or bytes, and no theorem relates it to
wall-clock time. The bound is quadratic, not linear: the stack is a list read
at its tail, buckets are built by append, and the consumer index is rebuilt
for each rule attempt. A linear bound is the open goal D6-linear.

## Outside these claims

- Finding a linking. No theorem concerns proof search. In the matched-search
  executables `ProofNetIRMatchedSearch.lean` and `ProofNetIRPrunedSearch.lean`,
  the net arms decide each complete linking with `unificationCheck`, while the
  sequent arms return a Boolean without building a derivation. Answers are
  scored against labels fixed by the task generator (positives), by exhaustive
  net search (v0.1's negatives), and by a Lukasiewicz countermodel or the
  focused search (v0.2's count-preserving negatives).
- Quantifiers, cuts, additives, exponentials, units, and any proof-net
  representation of Lean or Mathlib goals.
- Time and bytes, and any bound below quadratic.

## Experiment evidence

Experiments under `experiments/` are preregistered. Each has a
`--check-committed` that CI runs; it verifies the committed artifacts against
their recorded hashes and recomputes what is cheap to recompute. That checks
bookkeeping and the reproducibility of decided outcomes; timings and model
outputs remain observations. The finite replay audits
(`proofnet_ir_new_progress_audit`, `proofnet_ir_tail_law_search`) and the
Python differential audit ([audit-v0.1.0.md](audit-v0.1.0.md)) are regression
evidence for the sets they cover, not theorems.
