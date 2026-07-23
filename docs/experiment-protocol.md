# Controlled MLL experiment protocol

## Research question

For matched unit-free, cut-free MLL sequents, does generating or repairing a
checked proof net reduce search redundancy or improve valid-proof yield over a
focused sequent baseline at the same compute budget?

The experiment does not begin with ordinary Lean/mathlib goals. That bridge
adds persistent hypotheses, elaboration, unification, and rewriting, which
would prevent attribution of any result to the graph representation itself.

## Matched systems

1. **Unfocused sequent search** is a diagnostic lower baseline. It enumerates
   legal cut-free rule applications without quotienting invertible rule order.
2. **Focused sequent search** is the scientific baseline. It eagerly performs
   the asynchronous phase and records only genuine focus and resource choices.
3. **ProofNet-IR generation** predicts or enumerates occurrence/link
   certificates and accepts only certificates passing the Lean checker.
4. **ProofNet-IR repair** starts from matched invalid mutations and applies
   bounded local graph edits before rechecking.

Every accepted output must reconstruct a derivation in the supported object
logic. Later Lean-term reconstruction must additionally pass the Lean kernel.

## Corpus generation

- Generate cut-free derivation trees first.
- Desequentialize them to valid proof nets.
- Use the recursive `identityCertificate` family as the first arbitrary-depth
  generator sanity stratum; do not mistake it for a diverse proof corpus.
- The transparent `Formula.enumerate` helper intentionally retains duplicates;
  canonicalization and train/test splitting must happen before experiments.
- Deduplicate by a versioned canonical serialization that is invariant under
  occurrence renaming but preserves formula labels and link incidence.
- Stratify by atom count, connective count, number of par links, maximum depth,
  and number of admissible resource partitions.
- Produce invalid examples only by labeled mutations of known-valid nets:
  non-dual axiom, missing/duplicate resource, wrong connective producer,
  cycle, disconnection, and out-of-bounds incidence.
- Split by canonical net before producing mutations, so variants of the same
  proof object cannot leak across train and test sets.

## Metrics

- `checked_success`: fraction with a checker-accepted and reconstructed proof;
- `kernel_success`: fraction accepted by Lean after the future Lean bridge;
- `candidate_count`: total complete candidates proposed;
- `search_nodes`: partial states expanded;
- `checker_calls` and `reconstruction_calls`;
- wall time, peak memory, and model tokens where applicable;
- repair success by mutation class and edit distance;
- canonical proof-object diversity.

For a sequent `S`, define a bounded redundancy-collapse statistic

```text
R_B(S) = N_seq,B(S) / max(1, N_net,B(S))
```

where `N_seq,B` is the number of successful derivation traces found under
budget `B`, and `N_net,B` is the number of distinct canonical proof nets to
which those traces desequentialize. Report both counts and `log2 R_B`; do not
infer a search improvement from a large quotient alone.

## Fairness and stopping rules

- Use the same formula instances, timeout, hardware class, and random seeds.
- Give each system access to the same subformula and duality operations.
- Tune budgets on validation data only.
- Report timeouts and malformed outputs, not only solved examples.
- Run at least five seeds for stochastic proposers and publish confidence
  intervals or the full seed table.
- A graph method wins only if it improves checked success or cost at matched
  success against the focused baseline. A smaller textual representation or a
  visually appealing graph is not enough.

## First completed deterministic run

The committed [matched-v0.1 experiment](../experiments/matched-v0.1/README.md)
applies this protocol to 1,000 matched positive tasks with a fixed 1,000-unit
per-method budget. It compares deterministic focused search, atom-matching net
generation over a supplied formula skeleton, and generic one-edit repair. All
unique certificate outputs are rechecked by Lean, and every accepted output is
executably sequentialized.

This is a controlled algorithmic baseline, not the planned model-backed study.
The supplied skeleton, mostly unique atom labels, positive-only
derivation-first corpus, and edit-distance-one repair make the graph tasks
substantially easier. The report therefore records the observed 76% versus
100% versus 100% success rates without claiming a general proof-net advantage.
