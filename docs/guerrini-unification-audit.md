# Guerrini unification implementation audit

## Source and scope

This audit uses Stefano Guerrini, *Correctness of Multiplicative Proof Nets is
Linear* (LICS 1999), ten pages, downloaded from the primary paper record on
2026-07-23. The local audit copy has SHA-256
`47c2b9fe82c73db3bcbb5c0dab183cb2130c9c446a1ae0f9c72fe59e53cbb149`.
The complete extracted text and all eight figures were inspected. The paper is
supplemental primary literature; it was not one of the seven original PDFs
placed in the parent knowledge folder.

The paper treats multiplicative proof structures without constants and also
allows cuts through a dummy-link encoding. ProofNet-IR v0.9 currently
formalizes only the cut-free, unit-free fragment, so dummy links and cut
handling are outside the implemented state machine.

## Exact link mapping

Guerrini's abstract link classes map to the current certificate syntax as
follows:

| Guerrini link | Switching behavior | ProofNet-IR link |
|---|---|---|
| axiom | edge between its two conclusions | `Link.axiom` |
| unary | retain one premise-to-conclusion edge | `Link.par` |
| binary | retain both premise-to-conclusion edges | `Link.tensor` |
| dummy | no switching edge; represents a cut target | unsupported |

Figure 5 gives three unification rules:

1. `start`: assign a fresh token to both conclusions of an unmarked axiom;
2. `forward`: fire a unary/par link only when both premises yield the same
   current token class, then mark its conclusion with that class;
3. `unify`: fire a binary/tensor link only when its premises yield distinct
   token classes, merge those classes, then mark its conclusion.

An armed binary link whose premises already yield the same token is a
permanent deadlock. An armed unary link whose premises yield different tokens
waits because a later binary merge can make it ready. Definition 11 and
Proposition 12 characterize correctness by a total marking whose partition has
one thread. Proposition 15 and Theorem 16 concern the more disciplined
sequential strategy of Figures 7 and 8 and its linear implementation.

## What the code implements

`ProofNetIR/Unification.lean` implements a deterministic, eager-start
unification pass:

- all axiom threads are initialized;
- connective links are scanned left to right;
- ready par and tensor links fire according to Figure 5;
- scans repeat until no progress or the link-count fuel is exhausted;
- every token class carries a partial `CutFreeDerivation` and exact occurrence
  frontier;
- a successful single component is exchanged to the submitted ordered
  conclusion boundary.

The generated tree is not trusted. `unificationReconstruct?` submits it to the
independent `verifyDerivation?` boundary, which rechecks structural
well-formedness, formula inference, desequentialization, and intrinsic
`ProofNetEquivalent` identity.

Library callers can use the detailed `unificationDerivationCandidate` and
`unificationReconstruct` forms to receive a stable `UnificationErrorCode`,
message, and input counts. Except for `malformedInput`, these diagnostics mean
that the deterministic tier did not produce a verified result; they are not
logical rejections. The `?` forms are convenience wrappers.

Lean currently proves:

```text
unificationReconstruct? = some result → check = true
unificationFastCheck = true → check = true
unificationCheck = check
unificationCheck = true ↔ DeclarativelyCorrect
```

The last two theorems use the deterministic pass as a short-circuiting fast
path and the already complete checker-free recursive sequentializer as a miss
fallback. Neither branch enumerates switching graphs.

## What is not yet proved

The following stronger claims are intentionally absent:

- `unificationFastCheck = check`;
- completeness or confluence of the eager repeated-scan schedule;
- a polynomial, quasi-linear, or linear bound for the hybrid
  `unificationCheck`;
- equivalence between this eager implementation and the sequential stack,
  waiting-set, `NEXTAXIOM`, and special union-find algorithm in Figures 7--8;
- support for cuts, dummy links, units, Mix, additives, or exponentials.

The current repeated scan can take a quadratic number of link visits before
independent derivation verification. A fast-path miss invokes the exhaustive
recursive fallback. Therefore citing Guerrini's Theorem 16 as a complexity
theorem for the present executable would be incorrect.

## Differential evidence

`proofnet_ir_unification_audit` checks 1,500 deterministic certificates:

- 250 derivation-generated positives;
- their 250 reversed-link variants;
- their 250 reversed-boundary variants;
- 750 malformed missing-link, duplicate-link, or invalid-axiom mutations.

It additionally checks a structurally well-formed but disconnected
two-axiom sentinel and requires the stable `nonUniqueThread` diagnostic. The
first recorded Windows run reported 750/750 positive fast-path hits, zero
positive misses, zero false positives, and exact hybrid/reference agreement.
This is regression evidence, not the missing fast-path completeness theorem.
The main 291-case performance workload and the 18-case repeated-label stress
suite also require the deterministic fast path to return a proof-bearing
result.

A second positive-only counterexample search covers 6,000 reordered
derivation-generated certificates from 1,000 seeds, depths zero through five,
up to 111 formula occurrences and 79 links. It observed no fast-path miss in
its first recorded run. The source theorem
`CutFreeDerivation.desequentialize?_check` establishes acceptance of each base
certificate; the order variants preserve the same occurrences and links.
This finite search is intentionally kept separate from the universal
completeness theorem.

## Remaining formalization route

1. State the operational one-step relation independently of the executable
   scan and prove that every fired component denotes the corresponding parsing
   substructure.
2. Prove progress for every nonfinal correct state, distinguishing waiting par
   links from tensor deadlocks.
3. Prove the deterministic schedule complete, yielding
   `unificationFastCheck = check` and removing the recursive fallback.
4. Replace repeated scans with explicit ready/waiting worklists and prove a
   concrete operation bound.
5. Only after the worklist, `NEXTAXIOM`, and union-find invariants are
   formalized should the library expose a Guerrini-linear complexity theorem.
