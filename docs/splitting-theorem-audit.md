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

1. **Edge-aware paths and simple cycles (foundation complete).** `Graph.Walk` records adjacent
   vertices but not which stored multiedge was traversed. `Graph.DirectedEdge`
   and `Graph.EdgeWalk` now retain list indices, orientation, reversal, and
   exact traversal composition while forgetting soundly to `Graph.Walk`.
   `Graph.EdgeSimpleCycle` represents nonempty multigraph cycles without
   collapsing equal-valued parallel edges.
2. **Local switching colors (foundation complete).** `fullEdgeAnnotations`
   proves that stored edges and their source-link annotations stay aligned.
   `incidenceColor` gives the two incoming premise incidences of one par link
   their shared conclusion color and gives every other directed incidence its
   exact edge-index/orientation color. `Cusp` compares the two incidences at a
   path transition, and `cusp_reverse_iff` proves local reversal invariance.
   `CuspFreeTraversal`, `CuspFreeCycle`, and `CuspAcyclic` now state the
   proposition-level colored-cycle criterion. The projection and existence
   theorems prove that every stored par link supplies two exact indexed
   incidences aimed at its conclusion with that shared color.
3. **Correctness bridge (complete).**
   `DeclarativelyCorrect.cuspAcyclic` now proves cusp-acyclicity of the colored
   occurrence multigraph for every independent `ChoiceSelection`, not merely
   executable enumeration examples. The proof treats stored edge indices as
   occurrence identity, proves a cusp-free simple cycle cannot use both
   positions of a par pair, constructs a `FullSwitchingSelection` mask that
   preserves every requested cycle occurrence, transports the cycle through
   mask compaction, and contradicts the selected switching's `IsTree` theorem.
   This includes parallel equal-valued edges and the cycle's closing cusp.
4. **Finite maximality/Yeo (order foundation complete).** `EdgeSimplePath`,
   `CuspFreeContinuation`, and the strengthened `OrderingPath` now encode the
   simple open cusp-free continuation and universal path-separation condition.
   Their append theorem proves the induced `EdgeOrdering` is irreflexive and
   transitive. A representation-independent finite theorem now supplies a
   maximal member of every nonempty duplicate-free list under such a relation.
   Simple-cycle reversal, freely closing cycle orientation, a minimal finite
   internal-cusp count, and prefix extraction are now formalized. From
   cusp-acyclicity, a freely oriented non-closing cycle yields a simple
   cusp-free continuation to its first nontrivial cusping edge. Cusp-count
   additivity and reversal invariance preserve the minimal-cycle measure;
   first-intersection truncation normalizes a hypothetical later path, while
   structural looplessness excludes reuse of either edge at the chosen cusp.
   Exact path reversal/suffix extraction and a two-path cycle constructor now
   turn the normalized later prefix plus old return suffix into a genuine
   simple occurrence cycle. Cusp-acyclicity proves its splice boundary must be
   its unique internal cusp. A one-cusp split now yields cusp-free pieces, and
   exact cycle rotation extracts the complementary wrap-around path needed for
   the final reroute. The first-return path is now proved edge-disjoint from the
   entire original cycle (including parallel occurrences), closes with the
   reversed complementary arc, and rotates to an exact simple cycle at the
   original base while preserving cyclic cusp count. The remaining
   generalized-Yeo proof now has a kernel-checked exact traversal normal form,
   cusp-free closing proof, strict minimal-cycle inequality, and final
   cusp-free-cycle contradiction whenever the first hit is not the old base.
   Both endpoint orientations of the degenerate hit-at-base branch are now
   kernel checked as well. Thus every first hit at or before the selected cusp
   is impossible. The symmetric wrap-around construction for a first cycle
   hit after the cusp is now also complete through its final cusp-free-cycle
   contradiction. The arbitrary normalized first intersection is now
   exhaustively classified into the old prefix, selected incoming edge,
   selected partner, or old suffix. The partner would revisit the later
   path's start; the other cases are discharged by the before/base,
   orientation-reversed adjacent, and after-cusp theorems. Consequently the
   first-cusp continuation is now an `OrderingPath`; finite maximality proves
   existence of a colored `SplittingVertex` in every nonempty cusp-acyclic
   occurrence graph.
5. **Stored-link and terminal bridge (partially complete).** Exact annotation
   inversion now proves every nontrivially cusping occurrence is a concrete
   stored par premise occurrence aimed at that par conclusion. Finite
   maximality restricted to cusping occurrences therefore returns a stored par
   conclusion satisfying `SplittingVertex`. What remains is the global
   terminality argument: when such a par conclusion has a parent, propagate
   the strict occurrence ordering toward the ordered public boundary and
   derive either a terminal par or a terminal splitting tensor.
6. **Terminal-tensor splitting bridge (required direction complete).**
   `SplittingVertex.toSplittingTensor` proves that a structurally well-formed
   terminal tensor satisfying the colored splitting condition has no walk
   between its premises in `fullGraphWithoutVertex`. The proof loop-erases and
   lifts a vertex walk to an exact occurrence-aware simple path, closes it with
   the two distinct tensor occurrences, rotates the resulting cycle to the
   tensor conclusion, and contradicts the two unequal unique closing colors.
   No converse is used by recursive sequentialization and none is currently
   claimed.

## What is already complete

- terminal par reduction preserves structural, declarative, and Boolean
  correctness;
- assuming `SplittingTensor`, the executable tensor candidate is total;
- every child switching is an induced restriction of an input switching;
- exact vertex and edge partitions force both child switchings to be trees;
- `TerminalTensorReduction` preserves declarative and Boolean correctness;
- every structurally well-formed certificate containing a connective has some
  terminal tensor or terminal par, by strict formula-complexity growth.
- edge-aware simple cycles and the exact local switching-color/cusp semantics
  are defined without collapsing parallel edge occurrences.
- declarative switching correctness now implies the exact proposition-level
  colored-cycle criterion `CuspAcyclic`.
- a colored splitting terminal tensor now implies the existing mathematical
  `SplittingTensor` separator proposition, with exact multiedge identity.

## Claim boundary

None of the completed bullets proves universal splitting existence. Generated
examples and successful checker-gated candidates are regression evidence only.
`GenerallySequentializable` must remain unproved until the six representation
obligations above and the subsequent well-founded reconstruction/equivalence
proof are kernel-checked with no `sorry` or `admit`.
