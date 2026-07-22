# Trust model

## Trusted

- the Lean 4 kernel selected by `lean-toolchain`;
- the compiled definitions and theorems in this repository, after `lake build`;
- the small object-logic derivation type used for supported reconstruction.

## Untrusted

- an AI model or graph neural network proposing certificates;
- prompts, retrieved text, local-model summaries, and imported papers;
- a future Python/TypeScript dataset generator or visualizer;
- a future JSON parser until its output is revalidated in Lean;
- benchmark labels not regenerated from checked certificates;
- the high-level claim that proof geometry improves proof search.

## Current theorem boundary

`Certificate.check_sound` states that executable acceptance implies:

1. structural `wellFormed` acceptance;
2. every enumerated switching satisfies `Graph.IsTree`.

`Graph.IsTree` is a proposition over bounded edges, finite reachability from
vertex zero, and the edge-count equation. The current reachability engine is a
finite closure computation. A path-inductive equivalence theorem is planned so
that connectedness is also related to an independent walk semantics.

`Certificate.check_complete` proves the converse for the implemented
declarative contract. It is not the proof-net sequentialization theorem.

## Failure containment

Even if a future graph proposer, optimized checker, or sequentializer is wrong,
the final Lean proof must still elaborate and pass the kernel. Experimental
metrics must distinguish:

- syntactically valid JSON;
- structurally well-formed certificates;
- switching-valid certificates;
- sequentialization success;
- Lean kernel success.

Collapsing these stages into a single "solved" label would hide the project's
most useful diagnostic signal.
