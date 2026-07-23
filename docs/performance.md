# Performance budget and current boundary

## CI workload

`ProofNetIRBenchmark.lean` runs the native checker, deterministic
unification fast path, executable sequentializer, checker-free automatic
reconstruction, and `ProofNetEquivalent` decision procedure on 291 deterministic
derivation-generated certificates, followed by one adversarial pairwise-
identity case:

- 250 depth-2 trees;
- 40 depth-3 trees;
- one depth-4 sentinel;
- every even-numbered input has its link storage order reversed.

The identity stress fixture contains 64 identical positive atoms and 64
identical negative atoms, with every vertex fixed by the ordered conclusion
boundary. The old unconstrained formula-label enumerator therefore has
`(64!)^2` theoretical alignments. The constrained generator now produces one
candidate and rejects a shifted axiom matching immediately. The fixture is
structurally well formed but, for more than one pair, not switching-connected;
it deliberately isolates the exact identity engine's structural theorem
domain rather than posing as an accepted proof net.

Internal repeated labels are additionally filtered by a numeric-free one-hop
view of every vertex's incident link roles and endpoint formulas. Lean proves
that any actual direct equivalence witness preserves these view multisets, so
the filter cannot remove a genuine witness. It remains a local necessary
condition, not a complete canonical label or a polynomial-time guarantee.

The executable verifies every result and accumulates a stable checksum so the
work cannot be optimized away silently. Timing begins after process startup and
excludes compilation. CI fails when the complete workload exceeds 45 seconds.
The threshold is deliberately a regression guard with platform headroom, not a
claim of constant, polynomial, interactive, or production-grade performance.

`reconstructDerivation?` does not evaluate `Certificate.check`, enumerate
switching graphs, or invoke the explicit vertex-permutation identity search.
Its structure-guided fast path greedily aligns repeated boundary occurrences
by complete formula-tree/axiom profiles and verifies only the completed tree.
If that heuristic result fails, the proved exhaustive path can still
backtrack across terminal par/tensor candidates and enumerate
formula-compatible occurrence orders. Its separate `reconstruction_ms`
counter is therefore a regression and comparison metric, not an asymptotic
guarantee.

`unificationReconstruct?` is an independent deterministic candidate path
based on axiom/start, par/forward, and tensor/unify token rules. It carries a
partial derivation per live token class and accepts only after the completed
tree passes `verifyDerivation?`. The benchmark requires this fast path to
succeed on every one of the 291 accepted inputs and records a separate
`unification_ms` counter. The eager repeated scan can revisit waiting links,
and the exact `unificationCheck` wrapper retains the exhaustive recursive
fallback on a miss, so the counter is not a linearity theorem.

The statistics-bearing candidate and verification APIs expose `passes`,
`linkVisits`, and `successfulFirings`. Their result type carries proofs of
`passes ≤ |links|` and
`linkVisits = passes * |links|`; the axiom-free theorem
`UnificationCandidateResult.linkVisitsBound` derives
`linkVisits ≤ |links|²`. This is an exact bound on link-list entries inspected
by eager saturation. It deliberately excludes linear frontier searches,
union-find representative walks, derivation verification, and any hybrid
fallback, so it is not a quadratic whole-program theorem.

A separate `proofnet_ir_reconstruction_audit` executable runs the exact
v0.2-shaped 1,000-case family: 250 derivation positives plus missing-link,
duplicated-resource, and self-axiom mutations. It fails on any Boolean
disagreement with the reference checker, requires every positive to return a
proof-bearing result, checks the expected 250/750 label split, and enforces a
15-second native budget. The recorded Windows run reported:

```text
checker-free-reconstruction-audit-ok cases=1000 positives=250 negatives=750
checksum=6124 elapsed_ms=413 budget_ms=15000
```

`proofnet_ir_unification_audit` adds reversed-link and reversed-boundary
positive variants and checks 1,500 inputs total. It requires exact
`unificationCheck`/reference agreement, rejects any fast-path false positive,
and reports rather than conceals a fast-path positive miss. The first recorded
Windows run reported:

```text
unification-audit-ok cases=1500 structural_negative_sentinels=1
reference_positives=750
reference_negatives=750 fast_positive_hits=750 fast_positive_misses=0
fast_false_positives=0 max_passes=5 max_link_visits=45
checksum=18372 elapsed_ms=352 budget_ms=15000
```

Zero observed misses are evidence for the pending completeness proof, not a
replacement for it.

`proofnet_ir_unification_completeness_search` is a separate positive-only
counterexample search. It generates 1,000 kernel-sound derivation trees at
depths zero through five, desequentializes them, and applies six storage-order
variants to each certificate: original, reversed links, reversed boundary,
rotated links, parity-partitioned links, and combined link/boundary
permutations. A miss reports the exact seed, depth, variant, and structured
unification error. The first recorded Windows run reported:

```text
unification-completeness-search-ok cases=6000 seeds=1000 depths=0..5
variants_per_seed=6 max_formulas=111 max_links=79 max_passes=9
max_link_visits=711 checksum=399450 elapsed_ms=5213 budget_ms=30000
```

This widens the counterexample search substantially, but remains finite
empirical evidence. Its executable name does not mean that universal
fast-path completeness has been proved.

A separate `proofnet_ir_reconstruction_stress` executable exercises 18
accepted identity nets with a single repeated internal atom. It crosses
right-skewed tensor, balanced tensor, balanced par, and alternating shapes;
includes original and reversed link storage; and reaches 126 formula
occurrences and 94 links. It calls
`reconstructDerivationWithinLimits` with the qualified 128-formula,
96-link, 24-conclusion envelope, so it never enters the exhaustive
formula-order fallback. The recorded Windows run reported:

```text
checker-free-reconstruction-stress-ok cases=18 checksum=41224
elapsed_ms=33457 budget_ms=45000
```

The same stress run now first requires deterministic unification success.
Individual unification times ranged from below one millisecond to five
milliseconds on the recorded run; the much larger total remains dominated by
the independently qualified bounded recursive reconstruction.

Exploratory pre-fix runs exceeded 8-second per-case timeouts at right-tensor
depth 8 and exceeded 30-second timeouts at balanced depth 4. After boundary
profiles, storage-order-independent candidate preference, deferred top-level
verification, and lazy fallback selection, the full bounded suite fits its CI
budget. These observations qualify the named strata only; they do not prove a
polynomial bound or rule out adversarial fallback behavior.

The repeated-boundary stratum expands a depth-20 identity to 22 conclusions
and then reverses link storage; it completed in 6,552 ms in its isolated
recorded run. A depth-31 expansion with 33 conclusions remained below the
formula/link ceilings but took 47,746 ms and exceeded the original stress
budget. That counterexample is why the qualified conclusion ceiling is 24
rather than 128; oversized inputs fail before structure-guided search.

The qualified limits are input-size gates, not a wall-clock deadline. The
bounded function can return structured `noCandidate` or
`candidateVerificationFailed` errors on a valid certificate; those outcomes
are inconclusive and callers may explicitly choose the unbounded complete API
or an external process deadline. Lean proves only the direction needed for
fail-closed use: every bounded success is sound, reference-accepted, and
accepted by the unbounded reconstruction decision.

Unbounded `Certificate.proofNetCanonicalFamily` is excluded from the main
291-case workload. It enumerates every link-list permutation and is therefore
factorial in the link count. Its purpose is to provide an executable,
kernel-proved complete invariant for the exact `ProofNetEquivalent` relation.
Production identity checks should use `CheckedCertificate.sameProofNet?` after
checker acceptance (or the lower-level `Certificate.proofNetEquivalent?` when
a caller already manages its structural premise). The checked API has an iff
theorem for exactly `ProofNetEquivalent`; neither path materializes the family.

The released `Certificate.proofNetCanonicalFingerprint?` maps and
minimizes that same family, so its compact return type does not imply compact
computation. The exact typed `Certificate.proofNetCanonicalCode?` likewise
minimizes the family; its iff theorem settles logical completeness but not
runtime suitability. These unbounded APIs remain specification oracles.

The public `proofnet-canonical-key-0.1` generator and parsed-key matcher check
`CanonicalKey.maxGenerationLinks = 7` before factorial evaluation. Inputs above
the limit return `none` or `false` immediately. A dedicated benchmark covers
accepted identity certificates with 1, 4, and 7 links, including reversed link
storage, JSON parsing, and safe matching. It materializes 5,065 family
candidates in total and fails above 10 seconds. This qualifies a small-input
wire contract; it does not improve the factorial asymptotic bound. Larger
inputs must use `sameProofNet?`.

The v0.8 `proofnet-canonical-key-0.2` path does not enumerate link orders.
Its direct list-based implementation is conservatively `O(VL + V^2)` for
`V` formula occurrences and `L` links, excluding emitted formula-text volume.
A separate benchmark builds, reorders, encodes, parses, and safely matches four
structurally well-formed identity certificates through 145 links. It has a
five-second budget. The benchmark intentionally uses the structural theorem
domain: running the independent all-switchings checker on the same nested
identity family would measure exponential checker work, not canonicalization.

## Baseline measurement

On the Windows development machine on 2026-07-23, the qualified workload
reported:

```text
cases=291 checksum=1040800 elapsed_ms=9895
check_ms=1 unification_ms=63 unification_link_visits=9086
unification_max_passes=7 sequentialize_ms=6505
reconstruction_ms=1655 equivalence_ms=0
identity_stress_pairs=64 identity_candidates=1 identity_ms=0
canonical_key_cases=3 canonical_key_candidates=5065 canonical_key_ms=732
canonical_key_budget_ms=10000 canonical_key_max_links=7
intrinsic_canonical_key_cases=4 intrinsic_canonical_key_max_links=145
intrinsic_canonical_key_ms=132 intrinsic_canonical_key_budget_ms=5000
```

The millisecond counters are coarse; zero means below one aggregate measured
millisecond at those isolated call sites. Recursive checker and equivalence
calls performed inside sequentialization are included in `sequentialize_ms`.
Ordered-boundary pruning removes a severe repeated-label case, but formulas on
internal non-boundary vertices can still require combinatorial search. This
measurement is not a polynomial-time or general scalability result.
On this workload both the deterministic unification and checker-free
reconstruction aggregates were lower than the legacy checker-gated
sequentializer aggregate, but the single run is a regression receipt rather
than a statistically controlled speedup or asymptotic claim.

The independent intrinsic wire envelope was also exercised negatively during
development: a depth-64 identity certificate produced 45,022 tokens and
1,292,168 aggregate token characters, so generation failed closed at the
one-million-character limit. The qualified depth-48 case remains inside the
envelope. This records a real output-size limit rather than silently raising
the parser budget.

The held-out model experiment's qualification batch exercises the harder
internal repeated-label case. Across 264 distinct inputs, Lean rejected all
176 corruptions and accepted and executably sequentialized all 88 positive
certificates in 291.7 seconds on the same Windows machine. A previous build
without the one-hop filter exceeded ten minutes and reached roughly 15.5 GB
before being stopped. This before/after observation motivated the filter; it
is not a controlled benchmark or an asymptotic claim.

An exploratory workload with eight depth-4 cases took 60,409 ms and failed an
initial 15,000 ms budget. Removing those eight cases reduced the depth-2/3
workload to 3,746 ms; adding one depth-4 sentinel raised it to 8,107 ms. This
shows that the current inverse-rule search has a meaningful depth-sensitive
cost. The benchmark protects against catastrophic regression but does not close
the need for profiling, asymptotic improvement, adversarial workloads, or a
documented user-configurable resource limit.

Run it with:

```text
lake exe proofnet_ir_benchmark
lake exe proofnet_ir_reconstruction_audit
lake exe proofnet_ir_reconstruction_stress
```

The separate LeanProp corpus executable checks 600
typed/erased/elaborated/canonical-JSON positive templates and 1,000
raw/canonical-JSON negative templates rejected by both inference and typed
elaboration with exact diagnostics under a 10-second native execution budget. Compilation is excluded,
and the threshold is likewise a catastrophic-regression guard rather than an
asymptotic claim. CI also sends 5,000 deterministic mutated strings through the
native LeanProp parser in a separate fuzz process.

## Matched algorithmic experiment

The native regression above measures the executable sequentializer. It is
separate from the first 1,000-task comparison of focused search, direct
proof-net generation, and checker-guided one-edit repair. That experiment,
including per-depth failures, Python timing/allocation data, checker calls,
Lean batch verification, and its strict interpretation boundary, is recorded
in [matched-v0.1](../experiments/matched-v0.1/README.md).

The next 180-task model-backed comparison is frozen in
[model-v0.2](../experiments/model-v0.2/README.md). All 360 model calls finished,
but the preregistered runner then spent roughly 100 minutes in algorithmic
scoring without reaching Lean verification: the 60-second outcome budget was
checked only after return. Protocol amendment 1 records that failed execution,
preserves the raw-response hash, and moves each method/task into a child
process with a real 60-second deadline. Final result artifacts were
deliberately absent from the preregistration checkpoint. The amended final run
produced 20 hard timeouts, exactly the depth-4 negative tasks in the two-label
and one-label
strata. Proof-net generation therefore solved 160/180 within budget; focused
search solved 85/180, distance-ordered repair 180/180, model direct 117/180,
and model repair 2/180. See the
[final report](../experiments/model-v0.2/report.md) for why these are controlled
task results rather than a general performance claim.
