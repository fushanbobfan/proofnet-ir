# Performance budget and current boundary

## CI workload

`ProofNetIRBenchmark.lean` runs the native checker, executable
sequentializer, and `ProofNetEquivalent` decision procedure on 291 deterministic
derivation-generated certificates:

- 250 depth-2 trees;
- 40 depth-3 trees;
- one depth-4 sentinel;
- every even-numbered input has its link storage order reversed.

The executable verifies every result and accumulates a stable checksum so the
work cannot be optimized away silently. Timing begins after process startup and
excludes compilation. CI fails when the complete workload exceeds 45 seconds.
The threshold is deliberately a regression guard with platform headroom, not a
claim of constant, polynomial, interactive, or production-grade performance.

`Certificate.proofNetCanonicalFamily` is deliberately excluded from this
workload. It enumerates every link-list permutation and is therefore factorial
in the link count. Its purpose is to provide an executable, kernel-proved
complete invariant for the exact `ProofNetEquivalent` relation. Production
identity checks should use `Certificate.proofNetEquivalent?`, whose
completeness theorem does not require materializing the family.

## Baseline measurement

On the Windows development machine on 2026-07-22, the committed workload
reported:

```text
cases=291 checksum=8246 elapsed_ms=8107
check_ms=0 sequentialize_ms=7133 equivalence_ms=0
```

The millisecond counters are coarse; zero means below one aggregate measured
millisecond at those isolated call sites. Recursive checker and equivalence
calls performed inside sequentialization are included in `sequentialize_ms`.

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
```

## Matched algorithmic experiment

The native regression above measures the executable sequentializer. It is
separate from the first 1,000-task comparison of focused search, direct
proof-net generation, and checker-guided one-edit repair. That experiment,
including per-depth failures, Python timing/allocation data, checker calls,
Lean batch verification, and its strict interpretation boundary, is recorded
in [matched-v0.1](../experiments/matched-v0.1/README.md).
