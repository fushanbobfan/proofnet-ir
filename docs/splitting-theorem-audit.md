# Global splitting theorem audit

Review date: 2026-07-22

## Claim under audit

The remaining decomposition theorem needed by `GenerallySequentializable` is:

> Every checker-accepted non-axiom certificate has either a terminal par link
> or a terminal tensor whose removal separates its two premise occurrences.

The current Lean predicate

```text
SplittingTensor left right conclusion :=
  TerminalTensor left right conclusion /\
  not (fullGraphWithoutVertex conclusion).Walk left right
```

uses the occurrence graph with all axiom, tensor, and both par-premise edges.
Deleting the terminal conclusion removes exactly the two terminal tensor edges;
therefore non-reachability of the two premises is the intended component form
of splitting for this representation.

## Evidence checked

The local proof-net exposition, section 14.1, gives only the informal component
definition and the standard recursive outline. It explicitly says that the
nontrivial step is existence of a suitable terminal rule. It is not sufficient
evidence for a formal existence proof.

The locally reviewed Rocq development at commit
`9b582a53c4c9c94013146d2c749597dada9edf96` uses a stronger proof architecture:

1. orient each multigraph edge locally and color directed incidences so that
   the two premise incidences of a par link share a color;
2. translate switching acyclicity into absence of nonempty cusp-free cycles;
3. define a strict ordering on directed edges using simple cusp-free paths;
4. apply a generalized Yeo theorem to a finite set of sequentialization edges;
5. prove a maximal selected edge targets a vertex that is both terminal and
   splitting;
6. only then construct the two induced tensor proof nets and recurse on a
   strict edge-count measure.

The upstream source is a mathematical reference under its own license. No Rocq
proof text or code is copied into this MIT repository; the Lean representation
and proofs must be independent.

## Representation obligations in ProofNet-IR

The Rocq graph has rule vertices and formula-labelled directed edges.
ProofNet-IR instead has formula occurrences as vertices and stores proof links
separately. A valid Lean proof therefore needs explicit bridges rather than a
name-level restatement of Yeo:

1. **Edge-aware paths (foundation complete).** `Graph.Walk` records adjacent
   vertices but not which stored multiedge was traversed. `Graph.DirectedEdge`
   and `Graph.EdgeWalk` now retain list indices, orientation, reversal, and
   exact traversal composition while forgetting soundly to `Graph.Walk`.
   Colored paths still need the cusp/simple-cycle layer on top of this API.
2. **Local switching colors.** Define colors for directed stored-edge
   incidences. The two edges emitted by one par link must share a color at the
   par conclusion; unrelated incidences must not be identified.
3. **Correctness bridge.** Prove that `DeclarativelyCorrect` implies
   cusp-acyclicity of the colored occurrence multigraph. This must cover every
   independent `ChoiceSelection`, not merely executable enumeration examples.
4. **Finite maximality/Yeo.** Prove the generalized finite colored-graph
   splitting theorem or an equivalent self-contained lemma in Lean.
5. **Terminal bridge.** Relate a selected directed edge target to the stored
   link and ordered public boundary. The formula-complexity theorem already
   proves that connective structure has some terminal connective, but does not
   prove that a terminal tensor splits.
6. **Splitting equivalence.** For a terminal tensor, prove that the colored
   splitting condition is equivalent to the existing
   `fullGraphWithoutVertex` non-reachability predicate.

## What is already complete

- terminal par reduction preserves structural, declarative, and Boolean
  correctness;
- assuming `SplittingTensor`, the executable tensor candidate is total;
- every child switching is an induced restriction of an input switching;
- exact vertex and edge partitions force both child switchings to be trees;
- `TerminalTensorReduction` preserves declarative and Boolean correctness;
- every structurally well-formed certificate containing a connective has some
  terminal tensor or terminal par, by strict formula-complexity growth.

## Claim boundary

None of the completed bullets proves universal splitting existence. Generated
examples and successful checker-gated candidates are regression evidence only.
`GenerallySequentializable` must remain unproved until the six representation
obligations above and the subsequent well-founded reconstruction/equivalence
proof are kernel-checked with no `sorry` or `admit`.
