# Search-redundancy experiment v0.1

Step 1 of the v0.11 program ([design](../../docs/v0.11-design.md)): how many
cut-free sequent derivations denote one proof net, exactly, on the committed
MLL corpora.

## Artifacts

- `preregistration.json`: corpora hashes, counting-implementation hashes,
  budgets, strata, hypotheses H1 to H3, and the statement that no corpus count
  existed when it was written; committed on `main` before the run;
- `results.jsonl`: one row per task (1,180: the 1,000 matched tasks and the
  180 model tasks) with the four exact counts, the memoized-state usage, the
  exclusion flags, the ratios, and the brute-force cross-check outcome;
- `summary.json`: per-stratum quartiles and the hypothesis decisions, with the
  SHA-256 of `results.jsonl` and of the preregistration;
- `report.md`: the generated table and the hypotheses answered as stated;
- `amendment-1.json`: the post-run change to the checking mode only.

## Reproduction

```text
python scripts/run_redundancy_experiment.py --check-committed
```

recomputes the counts of the 1,163 tasks whose recursion stayed within
100,000 memoized states with `lake exe proofnet_ir_redundancy_count`, compares
them with the committed rows, and verifies the artifact hashes; CI runs it.
`--run` regenerates everything, including the brute-force cross-check of
`scripts/redundancy_bruteforce.py` on the 1,060 tasks with at most 16 atoms
and 1,000 candidate linkings (about three hours on Windows, all of it in the
Python enumerator).

## Outcome

All 90 negatives count zero everywhere. Twenty repeated-label depth-4 model
positives exceed the linking budget (up to 16! candidate linkings) and
carry no net count; five of them also exceed the state budget. Every other
task is exact and every cross-checked task agrees.

- H1 supported: on 81.8% of the ratio-bearing tasks the tensor-persistent
  focused calculus still has more than one derivation per net.
- H2 supported: the median number of plain derivations per net on the matched
  corpus is 2 at 8 atoms, 36 at 16 atoms, and 170,734 at 32 atoms; the
  largest complete task has 3,432,145,449 derivations for 6 nets.
- H3 not supported as registered: strict focusing is strictly smaller than the
  committed baseline on 27.8% of tasks, because the 8-atom tasks, 700 of the
  1,000 matched tasks, have no nested tensor under focus and the two counts
  coincide there. On the 16-atom and 32-atom matched strata the median ratio
  `dFoc / dWeak` is 0.67 and 0.15.

These are properties of the search spaces of three calculi relative to the net
space. They say nothing about the running time of any search procedure and
claim no advantage for any method; that is step 2.
