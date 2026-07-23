# ProofNet-IR tutorial

This tutorial uses ProofNet-IR as an ordinary Lake dependency. It stays inside
the library's proved scope: unit-free, cut-free multiplicative linear logic
(MLL) with ordered conclusions.

## 1. Add the dependency

For development against a checkout:

```toml
[[require]]
name = "proofnet-ir"
path = "../proofnet-ir"
```

For a released build, pin a tag instead of tracking `main`:

```toml
[[require]]
name = "proofnet-ir"
git = "https://github.com/fushanbobfan/proofnet-ir"
rev = "v0.5.0"
```

Then import the single public umbrella module:

```lean
import ProofNetIR

open ProofNetIR
```

The path consumer in `consumer-smoke/` continuously checks the current API.
The release consumer in `consumer-release-smoke/` protects the latest tagged
API independently. `consumer-smoke/Tutorial.lean` compiles the tutorial's core
examples so documentation drift becomes a CI failure.

## 2. Construct and check a certificate

Formula-array indices are occurrence identities. This small certificate is one
axiom link with its two endpoints as ordered conclusions:

```lean
def p : Formula := .atom "p" true
def pDual : Formula := .atom "p" false

def axiomCertificate : Certificate where
  formulas := #[p, pDual]
  links := [.axiom 0 1]
  conclusions := [0, 1]

example : axiomCertificate.check = true := by native_decide

example : axiomCertificate.DeclarativelyCorrect :=
  axiomCertificate.check_iff_declarativelyCorrect.mp (by native_decide)
```

`check` is executable. `check_iff_declarativelyCorrect` is the theorem that
identifies its result with the independent structural and switching-tree
specification.

## 3. Parse untrusted JSON safely

Use the checked boundary when bytes come from a model, file, or network:

```lean
def parsed := Certificate.checkedFromString axiomCertificate.canonicalString

example : parsed.isOk = true := by native_decide
```

`fromString` checks syntax and canonical wire shape but does not require proof-
net correctness. `checkedFromString` additionally runs the reference checker
and only returns an accepted certificate. Parse errors carry a JSON path and a
message.

The v0.2 `canonicalString` contract preserves submitted formula-array
numbering. `equivalenceCanonicalString` is invariant under the narrower
order-preserving `ReindexEquivalent` relation. Neither operation claims
arbitrary graph-isomorphism canonical labeling.

For the broader relation used by sequentialization, the library exposes a
finite specification family:

```lean
def reordered : Certificate :=
  { axiomCertificate with links := axiomCertificate.links.reverse }

example : axiomCertificate.ProofNetEquivalent reordered ↔
    ∀ candidate,
      candidate ∈ axiomCertificate.proofNetCanonicalFamily ↔
        candidate ∈ reordered.proofNetCanonicalFamily :=
  Certificate.proofNetEquivalent_iff_canonicalFamily_of_check
    (by native_decide) (by native_decide)

example : axiomCertificate.ProofNetEquivalent reordered ↔
    axiomCertificate.proofNetCanonicalCode? =
      reordered.proofNetCanonicalCode? :=
  Certificate.proofNetEquivalent_iff_canonicalCode_of_check
    (by native_decide) (by native_decide)
```

This family enumerates link permutations, so it is factorial and intended for
specification or small audits. The typed canonical code has an exact iff
theorem and a distinct bounded `proofnet-canonical-key-0.1` parser, but the
unbounded generator still enumerates the same family. Public wire generation
and parsed-key matching check a seven-link ceiling before computation; values
above the ceiling return `none`/`false`. Within the ceiling,
`proofNetEquivalent_iff_canonicalKeyWithinLimit_of_check` gives the exact iff
contract. Use `CheckedCertificate.sameProofNet?` for ordinary or larger
identity decisions. The family preserves ordered conclusions,
tensor/par premise order, formula labels, and axiom endpoint orientation; it is
not arbitrary graph isomorphism.

## 4. Sequentialize every accepted certificate

The runtime API reconstructs a first-order cut-free derivation:

```lean
def reconstructed := axiomCertificate.sequentialize

example : reconstructed.isOk = true := by native_decide

example : ∃ result : ExecutableSequentializationResult axiomCertificate,
    axiomCertificate.sequentialize = .ok result :=
  axiomCertificate.sequentialize_complete (by native_decide)
```

The second example is stronger than a regression: `sequentialize_complete`
proves that the actual finite runtime search succeeds on every certificate for
which `check = true`.

Every successful result contains:

- a `CutFreeDerivation` tree;
- its inferred ordered sequent;
- an executable desequentialization back to an accepted certificate;
- a kernel `Derivation` exposed by `result.kernelDerivation`;
- a proof that the output is `ProofNetEquivalent` to the input.

The equivalence permits bounded vertex renaming and link-list permutation. It
preserves ordered conclusions and connective-premise order; it is not arbitrary
unlabeled graph isomorphism.

## 5. Start from a derivation instead

The other direction is independently executable:

```lean
def tree : CutFreeDerivation := .axiom "p" true

example : tree.infer? = some [p, pDual] := by native_decide
example : tree.desequentializeChecked?.isSome = true := by native_decide
example : tree.elaborate?.isSome = true := by native_decide
```

`desequentializeChecked?` returns a certificate only after checker acceptance.
`elaborate?` also connects successful inference to a kernel-typed derivation.

## 6. Know the boundary

ProofNet-IR currently proves and executes the two directions for its documented
unit-free, cut-free MLL representation. It does not yet supply units, cuts,
additives, exponentials, quantifiers, cut elimination, a tactic, or favorable
asymptotic guarantees. Depth-four search is already measurably expensive; see
`performance.md` before treating the runtime as production infrastructure.

For exact declaration types, use the generated [public API reference](api-reference.md).
For the trust boundary and known gaps, read [trust-model.md](trust-model.md) and
[library-readiness-audit.md](library-readiness-audit.md).
