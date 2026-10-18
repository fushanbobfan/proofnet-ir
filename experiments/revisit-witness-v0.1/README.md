# Revisit witness v0.1

revisit-provenance-v0.1 classed the strictly focused search's revisits by branch signature. On the count-preserving
negatives, 7.8% are permutations of an earlier branch, 33.3% decompose the same tensors with other splits, and 58.9%
decompose other tensors, a class that mixes attempts that differ with subproblems a reordering re-creates; with the
splits class read as excluding rule order, a reading revisit-witness-v0.2 tests, rule order accounts for between 7.8%
and 66.7% of the revisits. This experiment runs the same search with its control
flow unchanged (`ProofNetIRRevisitWitness.lean`), keeps each query's first four distinct branches in full, and writes
out the tensors revisits of every count-preserving negative with unique labels and 2% of those with repeated labels.
Each sampled revisit is rebuilt rule by rule from the input and compared with the earlier branches: a *reordering
witness* (the branches differ only by moving rules of tensors outside the revisited sub-sequent across the splits that
send them away), an *exclusion witness* (every earlier branch, all kept, sends a shared tensor into a different
premise or puts a formula that both meet at a tensor on a different side), *alike* (a formula the comparison needs
occurs more than once among the input's subformulas, so keys do not identify it), or *unresolved*.

## Artifacts

- `preregistration.json`: the question, the sample rule and rates, the definitions, hypotheses H119 to H121, checks
  C51 and C52, the corpus and the compared results by hash, implementation hashes, registered before any run on the
  corpus;
- `results.jsonl.gz`: per task, the outcome, the counters and classes, and each sampled revisit with its branches and
  witness class;
- `summary.json`, `report.md`: the witness shares and the identification interval for rule order by stratum; the
  hypotheses and checks.

## Reproduction

```text
python scripts/test_revisit_witness.py
python scripts/run_revisit_witness.py --check-committed
```

run the hand-made cases (two tensors decomposed in either order, a shared tensor entered from different sides,
repeated labels), and verify the hashes and the summary and rerun every task that finished within 200 ms; CI runs both.

## Outcome

The search reproduces focused-revisits-v0.1's outcomes and counters and revisit-provenance-v0.1's class counts on all
983 tasks (C51), and every branch of all 3,643 sampled revisits rebuilds to its query (C52).

- **H119 fails**: of the 1,894 tensors revisits with unique labels, 25 have a reordering witness (1.3%); 1,868 are
  alike.
- **H120 holds**: no tensors revisit has an exclusion witness, in any stratum.
- **H121 fails**: on the 32-atom negatives with unique labels, rule order accounts for between 23.3% and 84.5% of the
  revisits.

The registered premise behind H119 and H121, that keys identify formulas where labels are unique, is false at 32
atoms. The corpus's label modes rename the bases' own atom names, and every 32-atom base, positive or negative, uses
11 names for its 16 atom pairs: five names occur twice with each polarity, so a 32-atom task with unique labels has 32
axiom linkings, not one. The search compares formulas by keys and splits alike formulas by count, so on those tasks
which copy of a formula a branch moved is not defined, and the comparison classes every such revisit alike. Where keys
do identify every formula, on the 8- and 16-atom negatives with unique labels, there are 26 tensors revisits, all at 16
atoms: 25 have a reordering witness, 1 is unresolved, and none has an exclusion witness; with the stratum's 17
permutations, rule order accounts for 70.0% to 71.7% of its 60 revisits.

## Interpretation boundary

Where the comparison can be made, nearly every tensors revisit is a reordering and none contradicts the earlier
branches, so on those tasks rule order accounts for most revisits; but that stratum has 60 revisits, and 155,806 of the
count-preserving negatives' 156,624 lie at 32 atoms, where alike formulas make the question undefined for this search.
Attributing them would need a search that tracks formula occurrences and keeps alike formulas apart. The intervals
above count every splits revisit as excluding rule order; revisit-witness-v0.2 examined that class the same way and
found 2 of the stratum's 17 splits revisits to be reorderings, which puts rule order at 73.3% to 75.0% of the
stratum's revisits and leaves the corpus share without the upper limit of 66.7%. The hypotheses are reported as
registered; the 32-atom label repetition was found by this experiment.
