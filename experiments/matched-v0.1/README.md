# Matched deterministic MLL experiment v0.1

Run date: 2026-07-22

This is the first completed matched experiment for ProofNet-IR. It compares
three deterministic algorithms on the same 1,000 provable unit-free, cut-free
MLL sequents. It is not model-backed and does not establish an advantage on
ordinary Lean or mathlib goals.

## Pre-result design

- Corpus: 700 depth-2, 250 depth-3, and 50 depth-4 tasks emitted by Lean from
  `CutFreeDerivation.generate`, inferred as genuine derivations,
  desequentialized, and accepted by the reference checker.
- Fixed budget: at most 1,000 memo states and 1,000 tensor-resource partitions
  for focused search; at most 1,000 complete candidates for net generation and
  repair. The 1,000 limit was fixed after pilot runs exposed that state-only
  limits failed to bound resource-partition work. No formal result existed
  when the final budget was chosen.
- Focused search eagerly decomposes par and enumerates tensor resource splits.
  Every claimed success is replayed through a separate derivation-tree
  verifier.
- Direct net generation expands the known sequent into its complete formula
  occurrence/connective skeleton, enumerates atom-duality matchings, and calls
  the independent checker on every complete candidate.
- Repair starts from one of four deterministic one-edit corruptions of a known
  valid net: missing axiom, wrong axiom endpoint, missing connective, or
  duplicated link. It searches a generic one-edit neighborhood and rechecks
  every candidate.
- The Python checker is the differential oracle in `scripts/audit_v010.py`.
  The compiled Lean checker then rechecks every unique invalid and accepted
  certificate. Every unique accepted certificate must also succeed through
  the public executable `Certificate.sequentialize` API.
- All methods are deterministic, so the five-seed stochastic rule is not
  applicable. Model-token cost is zero.

The committed [corpus](corpus.jsonl), [per-task results](results.jsonl), and
[summary](summary.json) have content hashes in the summary. Run

```text
python scripts/run_matched_experiment.py --check-committed
python scripts/run_matched_experiment.py --write
```

to validate the artifacts or repeat the experiment. The complete repeat also
runs the Lean batch verifier and is intentionally not a normal CI gate; CI
runs a small end-to-end smoke sample.

## Results

| Depth | Tasks | Focused success | Net generation | One-edit repair |
|---:|---:|---:|---:|---:|
| 2 | 700 | 700 (100%) | 700 (100%) | 700 (100%) |
| 3 | 250 | 60 (24%) | 250 (100%) | 250 (100%) |
| 4 | 50 | 0 (0%) | 50 (100%) | 50 (100%) |
| **All** | **1,000** | **760 (76%)** | **1,000 (100%)** | **1,000 (100%)** |

Focused search hit its budget on 190 depth-3 and all 50 depth-4 tasks. Direct
net enumeration and repair never hit their candidate budgets. Direct
generation made 2,550 independent-checker calls in total; repair made 10,999.
Focused first-solution search expanded 86,133 memo states and tried 286,663
resource partitions.

On the recorded Windows machine, per-method time to the first claimed result
was:

| Method | Total | Median/task | p95/task | Max traced Python allocation |
|---|---:|---:|---:|---:|
| Focused first solution | 51.312 s | 7.095 ms | 193.143 ms | 32,769 B |
| Direct net generation | 5.260 s | 1.281 ms | 14.727 ms | 149,448 B |
| One-edit repair | 40.240 s | 13.339 ms | 114.816 ms | 801,833 B |

These method totals exclude the separate exhaustive focused-trace counting and
the final Lean batch. Exhaustive trace counting took 76.729 s and completed
only for the 700 depth-2 tasks; the deeper 300 tasks hit the partition budget.
For the completed shallow stratum, `log2(N_seq / max(1, N_net))` had median
1.0 and p95 2.322. No redundancy statistic is reported for depth 3 or 4.

The fixed corpus contains 930 distinct sequent payloads and 930 distinct
`reindex-v1` winning-net keys. Deduplication therefore reduced the final Lean
batch to 930 invalid plus 930 accepted certificates. Lean rejected all 930
invalid certificates, accepted all 930 valid certificates, and the runtime
sequentializer succeeded on all 930 accepted certificates. Those unique checks
cover 1,000 logical mutations and 2,000 logical generation/repair outputs.

## Interpretation boundary

The result supports a narrow statement: on this derivation-first corpus, when
the complete formula-occurrence skeleton is given and search is chiefly over
axiom matchings, the direct graph generator solved more tasks within the fixed
algorithmic budget than this focused Python baseline. It does **not** establish
that proof nets generally outperform focused proof search.

Important reasons not to generalize the result are:

- 950 tasks have unique atom labels within each proof and require only one
  axiom-matching candidate; the 50 depth-4 tasks account for the additional
  1,550 candidates.
- the net generator receives the full formula/connective skeleton, while the
  focused baseline must discover tensor resource partitions;
- all tasks were generated from valid derivations and are positive instances;
- repair begins exactly one edit from a known-valid net and is not evidence for
  noisy model-output repair at larger distance;
- timings compare Python implementations and exclude Lean-verifier wall time;
- `reindex-v1` diversity is not arbitrary graph-isomorphism canonicalization;
- no learned proposer, token budget, ordinary Lean elaboration, unification,
  rewriting, persistent contexts, or mathlib theorem is present.

The next empirical version must add held-out negative/unprovable sequents,
harder repeated-label strata, edit distances greater than one, equalized
wall-clock limits, and genuinely model-backed proposals before the research
hypothesis can be evaluated outside this controlled algorithmic setting.
