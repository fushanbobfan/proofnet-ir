# Equal-information matched search v0.1

Step 2 of the v0.11 program ([design](../../docs/v0.11-design.md)): with the
sequent as the only input and one wall-clock budget, does net-space search
decide more MLL sequents than focused sequent search, and where does label
repetition reverse the answer?

## Artifacts

- `corpus.jsonl`: 640 held-out tasks from `proofnet_ir_search_corpus` (seeds
  20000-20119, forty bases per depth at 8, 16, and 32 atoms), each base
  collapsed to unique, two-label, and one-label names (360 positives), plus
  one connective-flip negative per positive wherever exhaustive net-space
  search refuted the flip within twenty seconds (280 negatives; none exists
  for the two-label and one-label 32-atom strata);
- `preregistration.json`: corpus and implementation hashes, the three arms,
  the budget, and hypotheses H4 to H6, committed on `main` before the run;
- `results.jsonl`: per task and arm, the outcome (`found`, `refuted`,
  `timeout`), correctness against the certified label, elapsed
  milliseconds, and the arm's operation counters;
- `summary.json` and `report.md`: the stratum table and the hypothesis
  decisions.

## Arms

All three run in one Lean process (`proofnet_ir_matched_search`) with five
seconds of wall-clock per arm per task: `focused` is the committed
`scripts/focused_search.py` reproduced step for step (identical outcomes and
counters on 86 sequents); `focusedBalanced` adds per-name atom-balance
pruning; `nets` enumerates axiom linkings in the committed generator's order
and decides each with `Certificate.unificationCheck`.

## Reproduction

```text
python scripts/run_matched_search.py --check-committed
```

verifies the hashes and reruns the 388 tasks on which every arm finished
within 200 ms, comparing outcomes; CI runs it. `--run` reruns everything
(about twenty minutes); timings are machine-specific, outcomes within the
budget are not.

## Outcome

No arm ever gave a wrong answer. H4, H5, and H6 all hold as registered.

- Unique labels, where the linking is forced: `nets` decides every task at
  every size, in a median of 1.9 ms on the 32-atom positives and 9.8 ms on
  the 32-atom negatives; `focusedBalanced` needs a median of 12.6 ms and
  1.9 s there and times out on 4 of the 40 negatives; the unpruned
  `focused` times out on 37 of 40 positives and all 40 negatives.
- One label, where the linking space explodes: `nets` times out on all 40
  32-atom positives after a median of 49,780 candidate linkings, and on the
  16-atom negatives already needs a median of 3.0 s; `focusedBalanced`
  proves every 32-atom positive in a median of 0.3 ms.
- Balance pruning never loses to the committed baseline, and it is what makes
  sequent search viable at 32 atoms.

Read together with step 1: proof nets remove all rule-order redundancy,
which grows to five orders of magnitude at 32 atoms, and replace it by
linking redundancy, which is nil when labels are unique and factorial when
they repeat. Which family wins is decided by label repetition, not by the
size of the sequent. A search for a proof assistant would have to combine
both prunings. This is a statement about two search families on unit-free,
cut-free MLL sequents; it claims nothing about Lean or Mathlib.
