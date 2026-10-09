# MLL certify v0.1

matched-search-v0.2 added to its corpus 343 count-preserving negatives, unprovable sequents that keep atom balance
and the edge count, so that refuting them takes search. A countermodel in a finite Łukasiewicz chain certified 90 of
them; the other 253 were certified by the focused search that the experiment then evaluated, so its refutations of
those were not an independent measurement. This experiment decides every task of the corpus with
`scripts/mll_independent_prover.py`, an exhaustive prover for the plain sequent calculus of unit-free MLL written apart
from the library's searches: pars are decomposed first (par is invertible), every distinct tensor is tried as the last
rule with every multiset split of the rest whose two premises keep per-name atom balance and 2t + 2 = a, and sequents
are memoized. It uses no focusing and shares no code with `focusedStrict` or the net searches.

## Artifacts

- `preregistration.json`: question, prover, budget (600 s and 50 million distinct sequents per task), hypotheses H107
  and H108, check C42, registered before the corpus was run;
- `results.jsonl`: per task, the prover's answer, the distinct sequents it examined, and its time;
- `summary.json`, `report.md`.

## Reproduction

```text
python scripts/run_mll_certify.py --check-committed
```

reruns every task the prover decided within a second and recomputes the summary; CI runs it.

## Outcome

The prover agrees with the expected status on all 983 tasks and decides each within 9.3 s (C42).

- **H107 holds**: it refutes all 253 count-preserving negatives that the focused search had certified (the slowest
  in 9.3 s, a 32-atom negative with unique labels).
- **H108 holds**: it proves all 360 positives and refutes all 280 connective flips and all 343 count-preserving
  negatives.

So every negative of the corpus is now certified without the searches the corpus compares, and matched-search-v0.2's
result that the focused search decides every task no longer rests on that search's own certificates.
